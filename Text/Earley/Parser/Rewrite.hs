{-# LANGUAGE RankNTypes, GADTs #-}
module Text.Earley.Parser.Rewrite where

import Control.Monad.ST
-- import Control.Monad.Trans
import Data.STRef
import Control.Monad
import Data.Foldable
import Control.Applicative
import Control.Monad.Fix
import Control.Arrow
import Text.Earley.Grammar

import Debug.Trace

-- if you want a lazy list of results, earley is the wrong algorithm
-- use gll instead. gll is like earley but it doesn't process the 
-- input one character at a time and instead keeps a
-- [(start pos,[(end pos,result)])] for each rule
-- and doesn't need to run all rules in lockstep on the input, 
-- so it can be more lazy, but it uses more memory (/can't gc intermediate results)

-- earley is fine if you want all results or your grammar isn't that ambiguous

-- (if you want a list of results, earlier results first, earley can do that)

type M s e i = State s e i -> ST s (State s e i)

-- TODO: more stuff here
data State s e i = State {
  reset :: ![ST s ()],
  next :: ![M s e i],
  curPos :: {-# UNPACK #-} !Int,
  input :: i,
  names :: [e]
}
-- obvious way to do coalescing & skip through input is to have next be
-- :: Map (Position,RuleI s e i a) [a -> State s e i -> ST s (State s e i)]


newtype Parser s e i a = Parser {
  unParser :: (Results s e i a -> M s e i) -> M s e i
}

liftST :: ST s a -> Parser s e i a
liftST f = Parser $ \cb s -> f >>= \x -> cb (Results $ \cb' -> cb' x) s
{-# INLINE liftST #-}


-- TODO: so we reset cb but not results after we're done with start pos
-- (and store a RuleResults per end pos w/ results, reset RuleResults in RuleI after done w/ pos)

-- could we s/[a]/a/ on Results? idk if it affects time complexity, but the user really should be able to get an [a]
-- maybe we can use some lazy IO trick to give the user a complete [a]? 
-- problem is if left recursion + user getting list. so we can't give the user a complete [a]
-- maybe could w/ nulls transformation though

-- TODO: could we store a [Results s e i a] here?
data RuleResults s e i a = RuleResults [a] [a -> M s e i]

-- so we reset results after done w/ pos
data RuleI s e i a = RuleI {-# UNPACK #-} !(STRef s (RuleResults s e i a)) [Results s e i a -> M s e i]

-- data Results s e i a where
--   Results :: STRef s [a] -> STRef s [a -> State s e i -> ST s (State s e i)] -> Results s e i a


newtype Results s e i a = Results ((a -> M s e i) -> M s e i)
  -- deriving (Functor)

instance Functor (Results s e i) where
  fmap f (Results g) = Results (\cb -> g (cb . f))
instance Applicative (Results s e i) where
  pure x = Results (\cb -> cb x)
  Results f <*> Results x = Results (\cb -> f (\f' -> x (\x' -> cb (f' x'))))
  liftA2 f (Results x) (Results y) = Results (\cb -> x (\a -> y (\b -> cb (f a b))))

-- FIXME: can merge results at same rule w/ diff start pos & same end pos!
-- (if a calls b at pos i and j, and i-k & j-k both return results, only need to return once)
-- however, with fuly binarized/memoized grammars this is pointless
-- i.e. it must be that `a = b <*> c`, but `c` must be a rule, which does the merging for us
-- what about alts tho? shouldn't matter, but i'm not sure

-- TODO: gll-style optimization for multiple results at same position

-- NOTE: techincally this is two things in one (GLL (and us) merge them):
-- 1. merge multiple `Result`s at same position (optimization, needed to be `O(n^3)`, speeds up `rule (\_ -> a <|> b) <*> c`)
-- 2. cps processing for start position, to deal with left recursion
ruleP :: (Parser s e i a -> Parser s e i a) -> ST s (Parser s e i a)
ruleP f = do
  -- TODO: remove the Maybe, just use an empty RuleI
  -- check if callbacks list empty instead of isNothing
  currentRef <- newSTRef (Nothing :: Maybe (STRef s (RuleI s e i a)))

  emptyResults <- newSTRef (undefined :: RuleResults s e i a)

  -- TODO: need to use weakrefs for GC
  let
    resetcb = writeSTRef currentRef Nothing
    -- TODO: this is wrong, need to pass STRef (RuleResults) instead
    -- so that this works when at future pos
    results pos ref = Results $ \cb s -> do
      RuleResults rs rcbs <- readSTRef ref
      when (curPos s == pos) $ writeSTRef ref (RuleResults rs (cb:rcbs))
      foldrM cb s rs
    p = Parser $ \cb st ->
      readSTRef currentRef >>= \r -> case r of
        Just ref -> do
          RuleI r cbs <- readSTRef ref
          writeSTRef ref (RuleI r (cb:cbs))
          if r == emptyResults then pure st else cb (results (curPos st) r) st
        Nothing -> do
          ref <- newSTRef (RuleI emptyResults [cb])
          writeSTRef currentRef (Just ref)
          let
            reset2 rs = do
              modifySTRef ref (\(RuleI _ cbs) -> RuleI emptyResults cbs)
              modifySTRef rs (\(RuleResults xs _) -> RuleResults xs undefined)
            g x s = do
              RuleI rs cbs <- readSTRef ref
              if rs == emptyResults
                then do
                  rs' <- newSTRef (RuleResults [x] [])
                  writeSTRef ref (RuleI rs' cbs)
                  foldrM ($ results (curPos s) rs') (s {reset = reset2 rs':reset s}) cbs
                else do
                  RuleResults rxs rcbs <- readSTRef rs
                  writeSTRef rs (RuleResults (x:rxs) rcbs)
                  foldrM ($ x) s rcbs
          unParser (f p) (\(Results xs) -> xs g) (st {reset = resetcb:reset st})
  pure p


fixP :: (Parser s e i a -> Parser s e i a) -> Parser s e i a
fixP f = join $ liftST (ruleP f)

rule' :: Parser s e i a -> ST s (Parser s e i a)
rule' p = ruleP (\_ -> p)

-- thin :: Parser s e i a -> Parser s e i ()
-- thin (Parser p) = Parser $ \cb -> p (\_ -> cb $ Results ($ ()))

instance Functor (Parser s e i) where
  fmap f (Parser p) = Parser $ \cb -> p (\x -> cb (f <$> x))
  {-# INLINE fmap #-}
instance Applicative (Parser s e i) where
  -- TODO: make this operate on list of results from the same position for time complexity
  (<*>) = ap
  {-# INLINE (<*>) #-}
  pure = return
  {-# INLINE pure #-}
  liftA2 f (Parser a) (Parser b) = Parser $ \cb -> a (\x -> b (\y -> cb (liftA2 f x y)))
  {-# INLINE liftA2 #-}
  -- TODO: do we want this? currently w/ results it only returns once
  -- ((a <|> b) *> x) != (a *> x) <|> (b *> x)
  -- if a & b both succeed the first will only have one result and the second will have two
  Parser a *> Parser b = Parser $ \cb -> a (\_ -> b cb)
  {-# INLINE (*>) #-}
instance Monad (Parser s e i) where
  return a = Parser $ \cb -> cb $ pure a
  {-# INLINE return #-}
  Parser p >>= f = Parser $ \cb -> p (\(Results a) -> a (\x -> unParser (f x) cb))
  {-# INLINE (>>=) #-}

instance Alternative (Parser s e i) where
  empty = Parser $ \_ -> pure
  {-# INLINE empty #-}
  Parser a <|> Parser b = Parser $ \cb -> a cb >=> b cb
  {-# INLINE (<|>) #-}


terminalP :: (t -> Maybe a) -> Parser s e [t] a
terminalP v = Parser $ \cb s -> case input s of
  [] -> pure s
  (x:_) -> case v x of
    Nothing -> pure s
    Just a -> pure $ s {next = cb (pure a):next s}
-- {-# INLINE terminalP #-}


emptyState :: i -> State s e i
emptyState i = State {
  reset = [],
  next = [],
  curPos = 0,
  input = i,
  names = []
}

-- | A parsing report, which contains fields that are useful for presenting
-- errors to the user if a parse is deemed a failure.  Note however that we get
-- a report even when we successfully parse something.
data Report e i = Report
  { position   :: Int -- ^ The final position in the input (0-based) that the
                      -- parser reached.
  , expected   :: [e] -- ^ The named productions processed at the final
                      -- position.
  , unconsumed :: i   -- ^ The part of the input string that was not consumed,
                      -- which may be empty.
  } deriving (Eq, Ord, Read, Show)

run :: Bool -> (forall s. Parser s e [a] r) -> [a] -> ([(r, Int)], Report e [a])
run keep p l = runST $ do
  results <- newSTRef ([] :: [(r,Int)])
  s1 <- unParser p (\(Results cb) -> cb (\a s -> modifySTRef results ((a, curPos s):) >> pure s)) (emptyState l)
  let f s | null (next s) = do
            sequenceA_ (reset s)
            rs <- readSTRef results
            pure (rs, Report {
              position = curPos s,
              expected = names s,
              unconsumed = input s
            })
          | otherwise = do
            sequenceA_ (reset s)
            unless keep $ writeSTRef results []
            s' <- foldr (\a x -> x >>= a) (pure $ s {
              next = [],
              input = tail $ input s,
              curPos = curPos s + 1,
              names = [],
              reset = []}) (next s)
            f s'
  f s1

named :: Parser s e i a -> e -> Parser s e i a
named (Parser p) e = Parser $ \cb s -> p cb (s{names = e:names s})
{-# INLINE named #-}

newtype Rule s e t a = Rule (Parser s e [t] a)

interpProd :: Prod (Rule s) e t a -> Parser s e [t] a
interpProd p = case p of
  Terminal t f -> terminalP t <**> interpProd f
  NonTerminal (Rule r) f -> r <**> interpProd f
  Pure a -> pure a
  Alts as f -> foldr (<|>) empty (fmap interpProd as) <**> interpProd f
  Many m f -> many (interpProd m) <**> interpProd f
  Named f e -> interpProd f `named` e
{-# INLINE interpProd #-}

interpGrammar :: Grammar (Rule s) a -> ST s a
interpGrammar g = case g of
  RuleBind p f -> do
    r <- ruleP (\_ -> interpProd p)
    let p' = NonTerminal (Rule r) (pure id)
    interpGrammar (f p')
  FixBind f k -> do
    a <- mfix (interpGrammar . f)
    interpGrammar $ k a
  Return a -> pure a
{-# INLINE interpGrammar #-}



parser :: (forall r. Grammar r (Prod r e t a)) -> Parser s e [t] a
parser g = join $ liftST $ fmap interpProd $ interpGrammar g
{-# INLINE parser #-}

allParses :: (forall s. Parser s e [t] a) -> [t] -> ([(a,Int)],Report e [t])
allParses p i = run True p i

fullParses :: (forall s. Parser s e [t] a) -> [t] -> ([a],Report e [t])
fullParses p i = first (fmap fst) $ run False p i

-- | See e.g. how far the parser is able to parse the input string before it
-- fails.  This can be much faster than getting the parse results for highly
-- ambiguous grammars.
report :: (forall s. Parser s e [t] a) -> [t] -> Report e [t]
report p i = snd $ run False p i

-- ident (x:_) = isAlpha x
-- ident _     = False

token :: Eq t => t -> Parser s e [t] t
token y = satisfy (== y)
{-# NOINLINE token #-}

satisfy :: (t -> Bool) -> Parser s e [t] t
satisfy f = terminalP (\x -> if f x then Just x else Nothing)
{-# NOINLINE satisfy #-}

f <?> x = named f x

namedToken x = token x `named` x
rule = rule'

