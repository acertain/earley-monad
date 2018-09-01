{-# LANGUAGE RankNTypes, GADTs, TupleSections #-}
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
liftST f = Parser $ \cb s -> f >>= \x -> cb (pure x) s
{-# INLINE liftST #-}


-- could we s/[a]/a/ on Results? idk if it affects time complexity, but the user really should be able to get an [a]
-- maybe we can use some lazy IO trick to give the user a complete [a]? 
-- problem is if left recursion + user getting list. so we can't give the user a complete [a]
-- maybe could w/ nulls transformation though

-- TODO: no reason to use [a] here if we aren't merging results
newtype Results s e i a = Results (([a] -> M s e i) -> M s e i)

instance Functor (Results s e i) where
  fmap f (Results g) = Results (\cb -> g (cb . fmap f))
instance Applicative (Results s e i) where
  pure x = Results (\cb -> cb $ pure x)
  Results f <*> Results x = Results (\cb -> f (\a -> x (\b -> cb (a <*> b))))
  liftA2 f (Results x) (Results y) = Results (\cb -> x (\a -> y (\b -> cb (liftA2 f a b))))

-- FIXME: can merge results at same rule w/ diff start pos & same end pos!
-- (if a calls b at pos i and j, and i-k & j-k both return results, only need to return once)
-- however, with fuly binarized/memoized grammars this is pointless
-- i.e. it must be that `a = b <*> c`, but `c` must be a rule, which does the merging for us
-- what about alts tho? shouldn't matter, but i'm not sure

-- recover :: Parser s e i a -> ST s (Parser s e i a)
-- recover p = do
--   _

data RuleResults s e i a = RuleResults [Results s e i a] [[a] -> M s e i]

data RuleI s e i a = RuleI {-# UNPACK #-} !(STRef s (RuleResults s e i a)) [Results s e i a -> M s e i]

-- NOTE: techincally this is two things in one (GLL (and us) merge them):
-- 1. merge multiple `Result`s at same position (optimization, needed to be `O(n^3)`, speeds up `rule (\_ -> a <|> b) <*> c`)
-- 2. cps processing for start position, to deal with left recursion
ruleP :: (Parser s e i a -> Parser s e i a) -> ST s (Parser s e i a)
ruleP f = do
  -- TODO: remove the Maybe, just use an empty RuleI
  currentRef <- newSTRef (Nothing :: Maybe (STRef s (RuleI s e i a)))

  emptyResults <- newSTRef (undefined :: RuleResults s e i a)

  let
    resetcb = writeSTRef currentRef Nothing
    results pos ref = Results $ \cb s -> do
      RuleResults rs rcbs <- readSTRef ref
      when (curPos s == pos) $ writeSTRef ref (RuleResults rs (cb:rcbs))
      foldrM (\x -> case x of Results go -> go cb) s rs
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
                  foldrM (\c -> case x of Results go -> go c) s rcbs
          unParser (f p) g (st {reset = resetcb:reset st})
  pure p


-- fixP :: (Parser s e i a -> Parser s e i a) -> Parser s e i a
-- fixP f = join $ liftST (ruleP f)

rule' :: Parser s e i a -> ST s (Parser s e i a)
rule' p = ruleP (\_ -> p)

thin :: Parser s e i a -> Parser s e i ()
thin (Parser p) = Parser $ \cb -> p (\_ -> cb $ Results ($ [()]))

instance Functor (Parser s e i) where
  fmap f (Parser p) = Parser $ \cb -> p (\x -> cb (f <$> x))
  {-# INLINE fmap #-}
  -- x <$ Parser a = Parser $ \cb -> a _
  -- {-# INLINE (<$) #-}
instance Applicative (Parser s e i) where
  Parser f <*> Parser a = Parser $ \cb -> f (\f' -> a (\a' -> cb (f' <*> a')))
  {-# INLINE (<*>) #-}
  pure a = Parser ($ pure a)
  {-# INLINE pure #-}
  liftA2 f (Parser a) (Parser b) = Parser $ \cb -> a (\x -> b (\y -> cb (liftA2 f x y)))
  {-# INLINE liftA2 #-}
  -- this is old, currently we aren't merging results so this doesn't matter
  -- -- TODO: do we want this? currently w/ results it only returns once
  -- -- ((a <|> b) *> x) != (a *> x) <|> (b *> x)
  -- -- if a & b both succeed the first will only have one result and the second will have two
  -- -- Parser a *> Parser b = Parser $ \cb -> a (\_ -> b cb)
  -- -- 
  -- {-# INLINE (*>) #-}
instance Monad (Parser s e i) where
  return = pure
  {-# INLINE return #-}
  Parser p >>= f = Parser $ \cb -> p (\(Results a) -> a (\xs s -> foldrM (\x -> unParser (f x) cb) s xs))
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

run :: Bool -> Parser s e [a] r -> [a] -> ST s ([(r, Int)], Report e [a])
run keep p l = do
  results <- newSTRef ([] :: [(Results s e [a] r,Int)])
  s1 <- unParser p (\rs s -> modifySTRef results ((rs,curPos s):) >> pure s) (emptyState l)
  let f s | null (next s) = do
            sequenceA_ (reset s)
            pure $ Report {
              position = curPos s,
              expected = names s,
              unconsumed = input s
            }
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
  r <- f s1
  traceM "done parsing, building results now"
  rs2 <- newSTRef ([] :: [(r,Int)])
  -- TODO: this is possibly exponential,
  -- need to do something to return a lazy list or such
  readSTRef results >>= traverse_ (\(Results rs, pos) -> rs (\x s -> modifySTRef rs2 (fmap (,pos) x++) >> pure s) ((emptyState l) {curPos = position r + 1}))
  (,r) <$> readSTRef rs2

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
allParses p i = runST $ run True p i

fullParses :: (forall s. Parser s e [t] a) -> [t] -> ([a],Report e [t])
fullParses p i = first (fmap fst) $ runST $ run False p i

-- | See e.g. how far the parser is able to parse the input string before it
-- fails.  This can be much faster than getting the parse results for highly
-- ambiguous grammars.
report :: (forall s. Parser s e [t] a) -> [t] -> Report e [t]
report p i = snd $ runST $ run False p i

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

