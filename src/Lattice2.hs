{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE FunctionalDependencies #-}

module Lattice2 (endpoint, isSelfAv, walks, walks'', initWalk, onlySAWs, endSqrDist, conj, Square, Cubic, Triangular, Hexagonal, Dihedral, Sym3, Dihedral3, Dihedral6, nextSteps) where

import Data.List
import Data.List.Split (chunksOf)
import System.Random
import Data.Char
import Data.Ratio
import Numeric
import Control.DeepSeq

type Q = Ratio Int
class Eq a => Lattice a where
	origin :: a
	(+#) :: a -> a -> a
	(*#) :: Q -> a -> a
	nextSteps :: a -> [a]
	norm :: a -> Q

	(-#) :: a -> a -> a

	x -# y = x +# ((fromIntegral (-1)) *# y)

class Lattice b => GroupAction a b where
	(*+) :: a -> b -> b

	conj :: b -> a -> b -> b
	conj m d n = p +# m 
		where p = d *+ (n -# m)



newtype Square = Sq (Q,Q) deriving (Eq)

instance Lattice Square where
	origin = Sq (0,0)
	Sq (x1,x2) +# Sq (y1,y2) = Sq (x1+y1,x2+y2)
	t *# Sq (y1,y2) = Sq (t*y1,t*y2)

	norm  (Sq (x,y)) = x^2 + y^2

	nextSteps (Sq (a,b)) = [Sq (a,b)+# p | p<- [Sq (0,1), Sq (1,0), Sq (-1,0), Sq (0,-1)]] 

instance Show Square where 
	show (Sq (a,b)) = "("++(show $ realToFrac a)++","++(show $ realToFrac b)++")"


newtype Cubic = Cb (Q,Q,Q) deriving (Eq)
instance NFData Cubic where
	rnf (Cb (x,y,z)) = rnf x `deepseq` rnf y `deepseq` rnf z `deepseq` rnf (x,y,z)

instance Lattice Cubic where
	origin = Cb (0,0,0)
	Cb (x1,x2,x3) +# Cb (y1,y2,y3) = force (Cb (x1+y1,x2+y2,x3+y3))
	t *# Cb (y1,y2,y3) = force $ Cb (t*y1,t*y2,t*y3)

	norm  (Cb (x,y,z)) = force $ x^2 + y^2 + z^2

	nextSteps (Cb (a,b,c)) = [Cb (a,b,c)+# p | p<- [Cb (0,1,0), Cb (1,0,0), Cb (-1,0,0), Cb (0,-1,0), Cb (0,0,1), Cb (0,0,-1)]] 


instance Show Cubic where 
	show (Cb (a,b,c)) = "("++(show $ realToFrac a)++","++(show $ realToFrac b)++","++(show $ realToFrac c)++")"




newtype Triangular = Tr (Q,Q,Q, Q) deriving (Eq)

instance Lattice Triangular where 
	origin = Tr (0,0,0,0)
	Tr (x1,y1,z1,w1) +# Tr (x2,y2,z2,w2) = Tr (x1+x2, y1+y2, z1+z2, w1+w2)
	t *# Tr (x,y,z,w) = Tr (t*x, t*y, t*z, t*w)

	norm  (Tr (x,y,z,w)) = x^2 + y^2 + z^2 + w^2

	--nextSteps (Tr (a,b,c,d)) = [Tr (a,b,c,d)+# p | p<- [Tr (2,0,0,0), Tr (1,0,0,1), Tr (-1,0,0,1), Tr (-2,0,0,0), Tr (-1,0,1,-1), Tr (1,0,0,-1)]] 
	nextSteps (Tr (a,b,c,d)) = [Tr (a,b,c,d)+# p | p<- [Tr (1,0,0,0), Tr (1%2,0,0,1%2), Tr ((-1)%2,0,0,1%2), Tr (1,0,0,0), Tr ((-1)%2,0,1%2,(-1)%2), Tr (1%2,0,0,(-1)%2)]] 

instance Show Triangular where
	show (Tr (a,b,c,d)) = "("++x++", "++y++")"
		where x = (show $ realToFrac a)++" + "++ (show $ realToFrac b)++ " T"
		      y = (show $ realToFrac c)++" + "++ (show $ realToFrac d)++ " T"


newtype Hexagonal = Hx (Q, Q,Q, Q) deriving (Eq)

instance Lattice Hexagonal where 
	origin = Hx (0,0,0,0)
	Hx (x1,y1,z1,w1) +# Hx (x2,y2,z2,w2) = Hx (x1+x2, y1+y2, z1+z2, w1+w2)
	t *# Hx (x,y,z,w) = Hx (t*x, t*y, t*z, t*w)

	norm  (Hx (x,y,z,w)) = x^2 + y^2 + z^2 + w^2

	nextSteps (Hx (a,b,c,d)) = [Hx (a,b,c,d)+# p | p<- directions (Hx (a,b,c,d))] 
		where 
			directions (Hx (a,b,c,d))
				| c == 2*d    =  [Hx (0,0,-1,0), Hx (1%2,0,0,1%2), Hx ((-1)%2,0,0,1%2)]
				| otherwise  =  [Hx (1%2,0,0,(-1)%2), Hx ((-1)%2,0,0,(-1)%2), Hx (0,0,1,0)]


instance Show Hexagonal where
	show (Hx (a,b,c,d)) = "("++x++", "++y++")"
		where x = (show $ realToFrac a)++" + "++ (show $ realToFrac b)++ " H"
		      y = (show $ realToFrac c)++" + "++ (show $ realToFrac d)++ " H"

-----Dihedral 4-------------------------------------------------------
data Dihedral = D0 | D1 | D2 | D3 | D4 | D5 | D6 | D7 deriving (Show, Enum, Bounded, Eq)
type Sym2 = Dihedral

instance GroupAction Dihedral Square where
	D0 *+ Sq (x,y) = Sq (x,y)
	D1 *+ Sq (x,y) = Sq (-y,x)
	D2 *+ Sq (x,y) = Sq (-x,-y)
	D3 *+ Sq (x,y) = Sq (y,-x)
	D4 *+ Sq (x,y) = Sq (y,x)
	D5 *+ Sq (x,y) = Sq (x,-y)
	D6 *+ Sq (x,y) = Sq (-y,-x)
	D7 *+ Sq (x,y) = Sq (-x,y)

instance Random Dihedral where
	randomR (a, b) g = (toEnum x, g') where (x,g') = randomR (fromEnum a, fromEnum b) g
  	random g = randomR (minBound, maxBound) g



-----Sym 3-------------------------------------------------------

data Perm3 = P0 | P1 | P2 | P3 | P4 | P5 deriving (Show, Enum, Bounded, Eq)

instance GroupAction Perm3 Cubic where
	P0 *+ Cb (x,y,z) = Cb (x, y, z)
	P1 *+ Cb (x,y,z) = Cb (z, x, y)
	P2 *+ Cb (x,y,z) = Cb (y, z, x)
	P3 *+ Cb (x,y,z) = Cb (x, z, y)
	P4 *+ Cb (x,y,z) = Cb (z, y, x)
	P5 *+ Cb (x,y,z) = Cb (y, x, z)

instance Random Perm3 where
	randomR (a, b) g = (toEnum x, g') where (x,g') = randomR (fromEnum a, fromEnum b) g
  	random g = randomR (minBound, maxBound) g
	
data Sign3 = S0 | S1 | S2 | S3 | S4 | S5 | S6 | S7 deriving (Show, Enum, Bounded, Eq)

instance GroupAction Sign3 Cubic where
	S0 *+ Cb (x,y,z) = Cb (x, y, z)
	S1 *+ Cb (x,y,z) = Cb (-x, y, z)
	S2 *+ Cb (x,y,z) = Cb (x, -y, z)
	S3 *+ Cb (x,y,z) = Cb (-x, -y, z)
	S4 *+ Cb (x,y,z) = Cb (x, y, -z)
	S5 *+ Cb (x,y,z) = Cb (-x, y, -z)
	S6 *+ Cb (x,y,z) = Cb (x, -y, -z)
	S7 *+ Cb (x,y,z) = Cb (-x,-y, -z)

instance Random Sign3 where
	randomR (a, b) g = (toEnum x, g') where (x,g') = randomR (fromEnum a, fromEnum b) g
  	random g = randomR (minBound, maxBound) g
	
data Sym3 = Sym3 !Sign3 !Perm3 deriving (Show, Bounded, Eq)

instance GroupAction Sym3 Cubic where 
	Sym3 d0 d1 *+ p = d0 *+ (d1 *+ p) 


instance Random Sym3 where
	randomR (Sym3 x1 y1, Sym3 x2 y2) gen1 = (Sym3 x y, gen3)
		where (x, gen2) = randomR (x1, x2) gen1
		      (y, gen3) = randomR (y1, y2) gen2
	random  gen1 = (Sym3 x y, gen3)
		where (x, gen2) = random gen1
		      (y, gen3) = random gen2

-----Dihedral 6-------------------------------------------------------
data Reflections = R0 | R1 deriving (Show, Enum, Bounded, Eq)

instance GroupAction Reflections Triangular where
	R0 *+ Tr (x,y,z,w) = Tr (x, y, z, w)
	R1 *+ Tr (x,y,z,w) = Tr (x, y, -z, -w)

instance Random Reflections where
	randomR (a, b) g = (toEnum x, g') where (x,g') = randomR (fromEnum a, fromEnum b) g
  	random g = randomR (minBound, maxBound) g
	
data Rotations6 = O60 | O61 | O62 | O63 | O64 |O65 deriving (Show, Enum, Bounded, Eq)

instance GroupAction Rotations6 Triangular where
	O60 *+ p = p
	--O61 *+ Tr (a,b,c,d) = Tr ((a+3*d) /2, (b+c) /2, ((-3)*b+c) /2, ((-a)+d) /2)
	O61 *+ Tr (a,b,c,d) = Tr (1%2 * a - 3%2 * d , 1%2 *b - 1%2 * c, 3%2*b + 1%2 * c ,1%2*a +1%2 *d)
	O62 *+ p = O61 *+ (O61 *+ p)
	O63 *+ p = O61 *+ (O62 *+ p)
	O64 *+ p = O61 *+ (O63 *+ p)
	O65 *+ p = O61 *+ (O64 *+ p)

instance Random Rotations6 where
	randomR (a, b) g = (toEnum x, g') where (x,g') = randomR (fromEnum a, fromEnum b) g
  	random g = randomR (minBound, maxBound) g
	
data Dihedral6 = Di6 !Reflections !Rotations6 deriving (Show, Bounded, Eq)

instance GroupAction Dihedral6 Triangular where 
	Di6 d0 d1 *+ x = d0 *+ (d1 *+ x) 

instance Random Dihedral6 where
	randomR (Di6 x1 y1, Di6 x2 y2) gen1 = (Di6 x y, gen3)
		where (x, gen2) = randomR (x1, x2) gen1
		      (y, gen3) = randomR (y1, y2) gen2
	random  gen1 = (Di6 x y, gen3)
		where (x, gen2) = random gen1
		      (y, gen3) = random gen2



-----Dihedral 3-------------------------------------------------------
data Rotations3 = O30 | O31 | O32 deriving (Show, Enum, Bounded, Eq)

--rot3 (Hx (a,b,c,d)) = Hx ((-1)%2 * a - 3%2 * d , (-1)%2 *b - 1%2 * c, 3%2*b - 1%2 * c ,1%2*a -1%2 *d)
rot6 (Hx (a,b,c,d)) = Hx (1%2 * a - 3%2 * d , 1%2 *b - 1%2 * c, 3%2*b + 1%2 * c ,1%2*a +1%2 *d)
instance GroupAction Rotations3 Hexagonal where
	O30 *+ p = p
	O31 *+ p = rot6 $ rot6 p
	--O31 *+ p = rot3 p
	O32 *+ p = O31 *+ (O31 *+ p)
	--O31 *+ Hx (a,b,c,d) = Hx (((-a)+3*d) /2, (c-b) /2, ((-3)*b-c) /2, ((-a)-d) /2)

instance Random Rotations3 where
	randomR (a, b) g = (toEnum x, g') where (x,g') = randomR (fromEnum a, fromEnum b) g
  	random g = randomR (minBound, maxBound) g

instance GroupAction Reflections Hexagonal where
	R0 *+ Hx (x,y,z,w) = Hx (x, y, z, w)
	R1 *+ Hx (x,y,z,w) = Hx (x, y, -z, -w)

data Dihedral3 = Di3 !Reflections !Rotations3 deriving (Show, Bounded, Eq)

instance GroupAction Dihedral3 Hexagonal where 
	Di3 r0 r1 *+ x = r0 *+ (r1 *+ x) 

instance Random Dihedral3 where
	randomR (Di3 x1 y1, Di3 x2 y2) gen1 = (Di3 x y, gen3)
		where (x, gen2) = randomR (x1, x2) gen1
		      (y, gen3) = randomR (y1, y2) gen2
	random  gen1 = (Di3 x y, gen3)
		where (x, gen2) = random gen1
		      (y, gen3) = random gen2

--- Functions on these lattices
dir p = length $ nextSteps p

endpoint :: Lattice a => [a] -> a
endpoint = last

isSelfAv :: Lattice a => [a] -> Bool
isSelfAv w = nub w == w

updates w@(p:_) = [n:w | n<-nextSteps p]

walks :: Lattice a => Int -> [[a]]
walks l = map reverse $ iterate (concat . map updates) [[origin]] !! l

walk l n = scanl (\p n ->(nextSteps p) !! n) origin (head++tail)
	where tail = map digitToInt $ showIntAtBase 4 intToDigit n ""
	      lt = length tail
	      head = take (l-lt) $ repeat 0

walks'' l = map (walk l) [1..4^l]

onlySAWs :: Lattice a => [[a]] -> [[a]]
onlySAWs = filter isSelfAv


initWalk l = take (l+1) $ iterate (head . nextSteps) origin 

-------------Observables defined for all walks---------------------------------------------------------
endSqrDist :: Lattice a => [a] -> Float
endSqrDist w = realToFrac $ norm $ endpoint w
--radOfGyr w = avg [norm (realToFrac x - cx, realToFrac y - cy) | (x,y) <- w] where (cx, cy) = cOfMass w
--------------------------------------------------------------------------------------------------------



