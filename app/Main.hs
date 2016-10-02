{-# LANGUAGE BangPatterns #-}
import Data.List (foldl',nub)
import System.Environment (getArgs)
import System.Random 
import Lattice2
import Control.Parallel (par, pseq)
import Control.Parallel.Strategies
import Control.DeepSeq
import GHC.Float
import Data.Vector.Unboxed (foldl',fromList)
-- import Graphics.EasyPlot

main =  do
	[l,n] <- map read `fmap` getArgs
	g <- newStdGen
        --print (paromega' l n g)
	mapM_ putStrLn (map showMu $ mu n g)
	--plot X11 $ Data2D [] [] $ zip (map fromIntegral [l..n]::[Float]) (map (\x-> paromega x 10000 g :: Float) [l..n])
----------------Pivot method---------------------------------------------------------------------
sawSample l g = drop 2000 $ scanl chooseWalk (initWalk l) ts :: [[Cubic]]
	where   (g1, g2)   = split g
		ts 	   = zip (randomRs(0,l) g1 :: [Int]) (randoms g2 :: [Sym3])

changeWalk (n, d) w = w1 ++ map (conj p d) w2
	where w1        = take n w
	      w2@(p:_)  = drop n w

chooseWalk w (n,d)
	| isSelfAv w' = w'
	| otherwise   = w
	where w' = changeWalk (n,d) w

---------------Computing mu recursively----------------------------------------------------------------
randomSAWpairs l g = zip (sawSample l g1) (sawSample l g2) where (g1, g2) = split g

b (w1, w2)
	| isSelfAv $ w1 ++ tail w2 = 1
	| otherwise 	      	    = 0

bnn l n g = expected b $ take n $ randomSAWpairs l g
parbnn l n  = fourCPU (bnn l n)


mu n g = takeWhile ((/=0.0) . snd) $ iterate new (1,fromIntegral d) 
	where new (l, mun) = (2 * l, mun * bnn l n g **(1/realToFrac (2*l)))
	      d 	   = length $ nextSteps $ head $ head $ sawSample 1 g
--
---------------Omega--------------------------------------------------------------------- 
omega l n g = expected endSqrDist $ take n $ sawSample l g
paromega l n = fourCPU (omega l n)
paromega' l n g = pexpected endSqrDist $ take n $ sawSample l g

------- General functions needed---------------------------------------------------------------------------
avg l = realToFrac t / realToFrac n where (t,n) = Data.List.foldl' (\(!b,!c) a -> (a+b,c+1)) (0,0) l -- Fast average
avg' l = realToFrac t / realToFrac n where (t,n) = Data.Vector.Unboxed.foldl' (\(!b,!c) a -> (a+b,c+1)) (0,0) (fromList l) -- Fast average
expected f = avg . map f
pexpected f = mapReduce rdeepseq f rseq avg
--expected f = avg . (withStrategy (parBuffer 100 rdeepseq)) . map f
showMu (n,mun) = "mu_"++ show n ++" = "++ show mun

fourCPU f g = e `pseq` (eh `deepseq` avg (eh:e)) -- to avoid a fizzle!
--fourCPU f g = avg $ parMap rdeepseq (double2Float . f) [g1,g2,g3,g4]
	where (gt1,gt2) = split g
	      (g1,g2) = split gt1
	      (g3,g4) = split gt2
	      e = parMap rdeepseq (double2Float . f) [g1,g2,g3] -- to avoid a fizzle!
	      eh = double2Float (f g4) -- to avoid a fizzle!


mapReduce mapStrat mapFunc reduceStrat reduceFunc input = mapResult `pseq` reduceResult
    where mapResult    = parMap mapStrat mapFunc input
          reduceResult = reduceFunc mapResult `using` reduceStrat
----------------------------------------------------------------------------------------------------------
{-
dir = length (directions :: [Square])
w1 #+ w2 = w1 ++ (map (fixed +#) w2)

b (w1, w2)
	| isSelfAv (w1 #+ w2) = 1
	| otherwise 	      = 0

bnn l n gen = avF b $ take n (randomSAWpairs l gen)

mu' n gen = iterate new (1,fromIntegral dir) 
	where 
	      new :: (Int, Double) -> (Int, Double)
	      new (l, mun) = (2*l+1, (raise $ fromIntegral dir)*(raise $ bnn l n gen)*(raise' (mun**2)))
		      where raise mn = mn**(1/realToFrac (2*l+1))
		            raise' mn = mn**(realToFrac l/realToFrac (2*l+1))	
isSelfAv w = nub w == w



sawSample l gen = [w | (w,True) <- (walkList l gen)] :: [[Cubic]]
	where   (gen1, gen2)   = split gen
		ts 	       = zip (randomRs(0,l) gen1::[Int]) (randoms gen2::[Sym3])
		walkList l gen = scanl chooseWalk (initWalk l, True) ts

changeWalk (n, d) w = w1++trans w2
	where w1        = take n w
	      w2@(p:_)  = drop n w
	      trans     = map $ conj p d

chooseWalk (w,_) (n,d)
	| isSelfAv w' = (w', True)
	| otherwise   = (w, False)
	where w' = changeWalk (n,d) w


omega l n g = (force a) `par` (force b) `par` (force c) `par` (force d) `pseq` (a+b+c+d)/4
	where (gt1,gt2) = split g
	      (g1,g2) = split gt1
	      (g3,g4) = split gt2
	      a = expected endSqrDist $ take n $ sawSample l g1
	      b = expected endSqrDist $ take n $ sawSample l g2
	      c = expected endSqrDist $ take n $ sawSample l g3
	      d = expected endSqrDist $ take n $ sawSample l g4




paromega' l n g = avg $ parMap rdeepseq (double2Float . omega l n) [g1,g2,g3,g4]
	where (gt1,gt2) = split g
	      (g1,g2) = split gt1
	      (g3,g4) = split gt2
parbnn' l n g = avg $ parMap rdeepseq (double2Float . bnn l n) [g1,g2,g3,g4]
	where (gt1,gt2) = split g
	      (g1,g2) = split gt1
	      (g3,g4) = split gt2


parbnn'' l n g =  (force a) `par` (force b) `par` (force c) `par` (force d) `pseq` (a+b+c+d)/4
	where (gt1,gt2) = split g
	      (g1,g2) = split gt1
	      (g3,g4) = split gt2
	      a = expected b $ take n $ randomSAWpairs l g1
	      b = expected b $ take n $ randomSAWpairs l g2
	      c = expected b $ take n $ randomSAWpairs l g3
	      d = expected b $ take n $ randomSAWpairs l g4

paromega'' l n g = double2Float $ (force a) `par` (force b) `par` (force c) `par` (force d) `par` (force e) `pseq` (a+b+c+d+e)/5
	where (gt1,gt2) = split g
	      (g1,g2) = split gt1
	      (g3,g4) = split gt2
	      a = expected endSqrDist $ take n $ sawSample l g1
	      b = expected endSqrDist $ take n $ sawSample l g2
	      c = expected endSqrDist $ take n $ sawSample l g3
	      d = expected endSqrDist $ take n $ sawSample l g4
	      e = expected endSqrDist $ take n $ sawSample l g



mapP :: (a -> b) -> [a] -> [b] 
mapP _ [] = [] 
mapP f (w:[]) = [f w] 
mapP f (w:x:[]) = fx `par` [f w,fx] 
	where fx = f x 
mapP f (w:x:y:[]) = fx `par` fy `par` [f w,fx,fy] 
	where fx = f x 
	      fy = f x 
mapP f (w:x:y:z:zs) = fx `par` fy `par` fz `par` (f w:fx:fy:fz : (mapP f zs)) 
	where fx = f x 
	      fy = f y 
              fz = f z 
mapP' f xs = parBuffer 4 rdeepseq $ map f xs
-}

data Pair = Pair !Int !Float
mean xs = s / fromIntegral n
  where
    Pair n s       = Data.Vector.Unboxed.foldl' k (Pair 0 0) xs
    k (Pair n s) x = Pair (n+1) (s+x)
