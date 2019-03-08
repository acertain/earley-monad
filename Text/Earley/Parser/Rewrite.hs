{-# LANGUAGE RankNTypes, GADTs, TupleSections, OverloadedLists, BangPatterns, ScopedTypeVariables, LambdaCase, FlexibleContexts #-}
module Text.Earley.Parser.Rewrite where

import Control.Monad.ST
import Control.Monad.ST.Unsafe
-- import Control.Monad.Trans
import Data.STRef
import Control.Monad
import Data.Foldable
import Control.Applicative
import Control.Monad.Fix
import Control.Arrow
import Text.Earley.Grammar
import Data.Coerce
import Data.IntMap (IntMap)
import qualified Data.IntMap as M

import qualified Data.Sequence as S
import GHC.Stack

import Debug.Trace

type M s e i = State s e i -> ST s (State s e i)

-- TODO: more stuff here
data State s e i = State {
  reset :: ![ST s ()],
  next :: ![M s e i],
  -- actions to process once we're done at current position but before next position
  -- used only for rules, keyed by birthpos of the rule
  -- so we can get better complexity
  here :: IntMap [M s e i], -- [(Int,Queue M s e i)] -- !(Queue (M s e i)),
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


-- data Queue a = Queue ![a] ![a]

-- push :: a -> Queue a -> Queue a
-- push a (Queue x y) = Queue (a:x) y

-- pop :: Queue a -> Maybe (a, Queue a)
-- pop (Queue [] []) = Nothing
-- pop (Queue x []) = pop $ trace ``"swap" $ Queue [] (reverse x)
-- pop (Queue x (y:ys)) = Just (y, Queue x ys)

push :: Int -> a -> IntMap [a] -> IntMap [a]
push i a = M.alter (Just . maybe [a] (a:)) i

-- could we s/[a]/a/ on Results? idk if it affects time complexity, but the user really should be able to get an [a]
-- maybe we can use some lazy IO trick to give the user a complete [a]? 
-- problem is if left recursion + user getting list. so we can't give the user a complete [a]
-- maybe could w/ nulls transformation though

-- TODO: different SMany, (<>) has the wrong asymtotics for []
-- invariant: SMany nonempty
data Seq a = Zero | One a | SMany [a]

instance Functor Seq where
  fmap f Zero = Zero
  fmap f (One a) = One (f a)
  fmap f (SMany a) = SMany (fmap f a)
instance Applicative Seq where
  pure = One
  Zero <*> _ = Zero
  _ <*> Zero = Zero
  One f <*> One a = One (f a)
  One f <*> SMany a = SMany (fmap f a)
  SMany f <*> One a = SMany (fmap ($ a) f)
  SMany f <*> SMany a = SMany (f <*> a)

  _ <* Zero = Zero
  Zero <* _ = Zero
  a <* One _ = a
  One a <* SMany b = SMany ([a] <* b)
    -- where go [] = []
    --       go (x:xs) = a:go xs
  SMany a <* SMany b = SMany (a <* b)
  -- a <* b = liftA2 const a b


instance Semigroup (Seq a) where
  Zero <> a = a
  a <> Zero = a
  One a <> One b = SMany [a,b]
  One a <> SMany b = SMany (a:b)
  SMany a <> One b = SMany (a ++ [b])
  SMany a <> SMany b = SMany (a ++ b)
instance Monoid (Seq a) where
  mempty = Zero
instance Foldable Seq where
  null Zero = True
  null _ = False
  toList Zero = []
  toList (One a) = [a]
  toList (SMany a) = a
  foldMap f Zero = mempty
  foldMap f (One a) = f a
  foldMap f (SMany a) = foldMap f a



newtype Results s e i a = Results ((Seq a -> M s e i) -> M s e i)

instance Functor (Results s e i) where
  fmap f (Results g) = Results (\cb -> g (\x -> let !r = fmap f x in cb r))
instance Applicative (Results s e i) where
  pure x = Results (\cb -> cb $! pure x)
  Results f <*> Results x = Results (\cb -> f (\a -> x (\b -> cb (a <*> b))))
  liftA2 f (Results x) (Results y) = Results (\cb -> x (\a -> y (\b -> cb (liftA2 f a b))))
  -- Results x *> Results y = Results (\cb -> x (\a -> y (\b -> cb (a *> b))))
  -- -- {-# INLINE (*>) #-}
  -- -- Results x <* Results y = Results (\cb -> x (\a -> y (\b -> let r = b *> a in cb r)))
  Results x <* Results y = Results (\cb -> x (\a -> y (\b -> let !r = a <* b in cb r)))
  -- -- {-# INLINE (<*) #-}



-- Can merge results at same rule w/ diff start pos & same end pos!
-- (if a calls b at pos i and j, and i-k & j-k both return results, only need to return once with merged results)
-- however, with fuly binarized/memoized grammars, ignoring alts, we can assume that `a = b <*> c`, but `c` must be a rule, which does some merging for us

-- But this still adds too many callbacks to `c` (if b returns at `i-k` & `j-k`, then `c` gets two instances of `a` in its conts),
-- and callbacks in `c` cost per position where `c` succeeds starting from `k`

-- Practical, General Parser Combinators (Meerkat) avoids this by using a HashSet of Conts in rules.

-- However, this might not cause worst case complexity to go over cubic with fully binarized grammars. According to the meerkat paper,

-- > In Appendix A.3 we show that the execution of memoized CPS
-- > recognizers of Figure 2 and 6 can require O(n^(m+1)) operations, where
-- > m is the length of the longest rule in the grammar. The reason for
-- > such unbounded polynomial behaviour is that the same continuation
-- > can be called multiple times at the same input position. As illustrated
-- > in Appendix A.3, this happens when the same continuation is
-- > added to different continuation lists that are associated with calls
-- > made to the same recognizer but at different input positions.
-- > If the recognizer produces the same input position starting from different
-- > input positions, duplicate calls are made. The duplicate calls further
-- > result in adding the same continuations to the same continuation
-- > lists multiple times

-- I think it still affects non-worst case complexity though :(

-- I don't know if this is avoidable without using StableNames or similar to compare Conts


-- recover :: Parser s e i a -> ST s (Parser s e i a)
-- recover p = do
--   _


data RuleI s e i a = RuleI {-# UNPACK #-} !(STRef s (RuleResults s e i a)) [Results s e i a -> M s e i]


data RuleResults s e i a = RuleResults {
  processed :: !(Seq a),
  unprocessed :: !(Seq a),
  callbacks :: [Seq a -> M s e i],
  queued :: !Bool
} | DelayedResults [(Seq a -> M s e i) -> M s e i]

printStack :: HasCallStack => a -> IO ()
printStack a = do
  stack <- ccsToStrings =<< getCurrentCCS a
  putStrLn $ renderStack stack

-- what if keeping callabcks around is what's causing the leak?
-- 

-- NOTE: techincally this is two things in one (GLL (and us) merge them):
-- 1. merge multiple `Result`s at same position (optimization, needed to be `O(n^3)`, speeds up `rule (\_ -> (a <|> b) <*> c`)
-- 2. cps processing for start position, to deal with left recursion
ruleP :: forall s e i a. (Parser s e i a -> Parser s e i a) -> ST s (Parser s e i a)
ruleP f = do
  -- TODO: remove the Maybe, just use an empty RuleI
  currentRef <- newSTRef (Nothing :: Maybe (STRef s (RuleI s e i a)))

  emptyResults <- newSTRef (undefined :: RuleResults s e i a)
  let
    resetcb = writeSTRef currentRef Nothing
    resetr !rs =
      -- TODO: when can we gc processed here?
      modifySTRef ({-# SCC "reset2_rs" #-} rs) $ \case
        (RuleResults xs Zero _ False) -> RuleResults xs mempty undefined False
        DelayedResults rxs -> DelayedResults rxs
    results !birthPos !pos !ref = Results $ \cb s -> do
      !res <- readSTRef ref
      case res of
        DelayedResults rxs -> do
          -- undefined
          writeSTRef ref $ RuleResults {
            processed = mempty,
            unprocessed = mempty,
            callbacks = [cb],
            queued = False
          }
          foldMA (h birthPos ref) rxs $ s { reset = resetr ref:reset s }
        RuleResults{} ->
          -- TODO: is this right anymore?
          if curPos s /= pos then
            -- traceM $ "unaligned results: " <> show pos <> " from " <> show (curPos s)
            -- unsafeIOToST $ printStack f
            cb (processed res) s
          else {-# SCC "results2" #-} do
            -- when (not (null $ unprocessed res) && not (null $ processed res)) $ traceM "hi"
            writeSTRef ref $! res { callbacks = cb:callbacks res }
            if null (processed res) then pure s else
              -- when (queued res) $ traceM "hi :|"
              -- traceM $ show $ length $ callbacks res
              cb (processed res) s
    recheck !ref s = do
      !rs <- readSTRef ref
      case rs of
        DelayedResults rxs -> undefined
        RuleResults{} -> do
          let xs = unprocessed rs
          if null xs then pure s else {-# SCC "propagate" #-} do
            writeSTRef ref $! rs { unprocessed = mempty, processed = xs <> processed rs, queued = False }
            -- traceM $ show $ curPos s
            -- unsafeIOToST $ printStack f
            -- traceM $ "propagate " <> (show $ length $ callbacks rs) <> " at " <> (show $ curPos s)
            foldMA xs (callbacks rs) s
    h !birthPos !ref x s = do
      !res <- readSTRef ref
      -- undefined
      -- when (not $ queued res) $
          --   traceM $ "g again at " <> (show $ curPos s) <> " from " <> (show birthPos)
          --   -- unsafeIOToST $ printStack res
      writeSTRef ref $! {-# SCC "g_res" #-} res { unprocessed = x <> unprocessed res, queued = True }
      pure $! if queued res then s else {-# SCC "g_s" #-} s { here = push birthPos (recheck ref) (here s) }
    p = Parser $ \cb st -> do
      let !birthPos = curPos st
      readSTRef currentRef >>= \r -> case r of
        Just ref -> do
          RuleI r cbs <- readSTRef ref
          -- traceM $ "new child " <> (show $ length cbs) <> " at " <> (show birthPos)
          writeSTRef ref $ RuleI r (cb:cbs)
          if r == emptyResults then pure st else cb (results birthPos birthPos r) st
        Nothing -> do
          ref <- newSTRef (RuleI emptyResults [cb])
          writeSTRef currentRef (Just ref)
          let
            reset2 =
              modifySTRef ({-# SCC "reset2_ref" #-} ref) (\(RuleI _ cbs) -> RuleI emptyResults cbs)
            g (Results rxs) s = do
              RuleI rs cbs <- readSTRef ref
              if rs == emptyResults
                then do
                  rs' <- {-# SCC "g_rs'" #-} newSTRef $ DelayedResults [rxs]
                  writeSTRef ref $ {-# SCC "g_ref" #-} RuleI rs' cbs
                  -- traceM $ "g " <> (show $ length cbs) <> " at " <> (show birthPos) <> "-" <> (show $ curPos s)
                  let s' = {-# SCC "g_s1" #-} s {reset = reset2:reset s} -- , here = push birthPos (recheck rs') (here s) } -- push (recheck rs') (here s)}
                  foldMA (results birthPos (curPos s) rs') cbs s'
                else do
                  !res <- readSTRef rs
                  -- traceM $ "g again at " <> (show birthPos) <> "-" <> (show $ curPos s)
                  case res of
                    DelayedResults rxs' -> do
                      writeSTRef rs (DelayedResults (rxs:rxs'))
                      pure s
                    RuleResults{} ->
                      rxs (h birthPos rs) s
          -- traceM $ show $ curPos st
          -- unsafeIOToST $ printStack f
          unParser (f p) g (st {reset = resetcb:reset st})
  pure p

foldMA :: forall s a b. a -> [a -> b -> ST s b] -> b -> ST s b
foldMA y (x:xs) s = x y s >>= foldMA y xs
foldMA _ [] s = pure s



-- fixP :: (Parser s e i a -> Parser s e i a) -> Parser s e i a
-- fixP f = join $ liftST (ruleP f)

rule' :: Parser s e i a -> ST s (Parser s e i a)
rule' p = ruleP (\_ -> p)

bindList :: ([a] -> Parser s e i b) -> Parser s e i a -> Parser s e i b
bindList f (Parser p) = Parser $ \cb -> p (\(Results x) -> x (\l -> unParser (f $ toList l) cb))

fmapList :: ([a] -> b) -> Parser s e i a -> Parser s e i b
-- TODO: strictness here matters
-- (should be strict for thin, but probably not in general)
fmapList f (Parser p) = Parser $ \cb -> p (\(Results rs) -> cb (Results $ \g -> rs (\l -> g $ pure $! f $ toList l)))
-- {-# INLINE fmapList #-}

-- thin :: Parser s e i a -> Parser s e i ()
-- thin = fmapList (\_ -> ())
-- thin (Parser p) = Parser $ \cb -> p (\(Results rs) -> cb (Results $ \g -> g $ One ()))
thin = bindList (\_ -> pure ())
-- {-# INLINE thin #-}

-- thin = id

-- thin :: Parser s e i a -> Parser s e i ()
-- thin (Parser p) = Parser $ \cb -> p (\_ -> cb $ Results ($ pure $ ()))

traceP :: String -> Parser s e i a -> Parser s e i a
traceP st (Parser p) = Parser $ \cb s -> do
  let !left = curPos s
  traceM $ (show left) <> ": " <> st
  p (\r s' -> (traceM $ (show left) <> "-" <> (show $ curPos s') <> ": " <> st) >> cb r s') s

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
  Parser a *> Parser b = Parser $ \cb -> a (\x -> b (\y -> cb (x *> y)))
  {-# INLINE (*>) #-}
  --
  Parser a <* Parser b = Parser $ \cb -> a (\x -> b (\y -> cb (x <* y)))
  {-# INLINE (<*) #-}

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
  -- TODO: can opt this when a & b both return results at same (start,end) range
  -- (can merge results)
  -- Earley does this
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
  names = [],
  here = mempty
  -- here = Queue [] []
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

-- newtype EndoC c a = EndoC { runEndoC :: c a a }

-- instance Category c => Semigroup (EndoC c) where
--   EndoC a <> EndoC b = EndoC (a . b)



foldM2 :: forall s a b. [b -> ST s b] -> b -> ST s b
foldM2 (x:xs) s = x s >>= foldM2 xs
foldM2 [] s = pure s

run :: Bool -> Parser s e [a] r -> [a] -> ST s ([(Seq r, Int)], Report e [a])
run keep p l = do
  results <- newSTRef ([] :: [(Results s e i r,Int)])
  s1 <- unParser p (\rs s -> modifySTRef results ((rs,curPos s):) >> pure s) (emptyState l)
  let go s = case M.maxView (here s) of
        Just (l,hr) -> foldMA () (fmap const $ reverse l) (s { here = hr }) >>= go
        Nothing -> if null (next s)
          then do
            sequenceA_ (reset s)
            rs' <- newSTRef ([] :: [(Seq r, Int)])
            -- TODO: do we need s in Results?
            s' <- readSTRef results >>= foldr (\(Results rs, pos) -> (>>= rs (\x s' -> modifySTRef rs' ((x,pos):) >> pure s'))) (pure ((emptyState l) {curPos = curPos s + 1}))
            -- t <- foldM2 (fmap foldM2 $ toList $ here s') (s' { here = mempty })
            let l t | null (here t) = pure t
                    | otherwise = foldM2 (fmap foldM2 $ toList $ here t) (t { here = mempty }) >>= l
            l s'
            -- traceM $ show $ length $ here t
            -- when (not $ null $ here s') $ void $ go s'
            -- go s'
            rs <- readSTRef rs'
            -- traceM $ show $ length rs
            pure (rs, Report {
              position = curPos s,
              expected = names s,
              unconsumed = input s
            })
          else do
            sequenceA_ (reset s)
            unless keep $ writeSTRef results []
            -- traceM $ show $ curPos s
            go $ State {
              next = [],
              input = tail $ input s,
              -- TODO: this is wrong, should be keeping
              -- info about birthPos in next
              here = M.fromList [(curPos s + 1, next s)],
              curPos = curPos s + 1,
              names = [],
              reset = []
            }
  go s1

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



parser :: (forall r. Grammar r (Prod r e t a)) -> ST s (Parser s e [t] a)
parser g = fmap interpProd $ interpGrammar g
{-# INLINE parser #-}

-- allParses :: (forall s. ST s (Parser s e [t] a)) -> [t] -> ([(Seq a,Int)],Report e [t])
-- allParses p i = runST $ do
--   p' <- p
--   run True p' i

-- fullParses :: (forall s. ST s (Parser s e [t] a)) -> [t] -> ([Seq a],Report e [t])
-- fullParses p i = runST $ do
--   p' <- p
--   first (fmap fst) <$> run False p' i

allParses :: (forall s. ST s (Parser s e [t] a)) -> [t] -> ([(a,Int)],Report e [t])
allParses p i = runST $ do
  p' <- p
  first (foldMap $ \(s,p) -> (,p) <$> toList s) <$> run True p' i

fullParses :: (forall s. ST s (Parser s e [t] a)) -> [t] -> ([a],Report e [t])
fullParses p i = runST $ do
  p' <- p
  first (foldMap toList . fmap fst) <$> run False p' i


-- | See e.g. how far the parser is able to parse the input string before it
-- fails.  This can be much faster than getting the parse results for highly
-- ambiguous grammars.
report :: (forall s. ST s (Parser s e [t] a)) -> [t] -> Report e [t]
report p i = runST $ do
  p' <- p
  snd <$> run False p' i

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

