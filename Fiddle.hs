{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module Main where

import Control.Monad (forever, forM_, mzero, when)
import Data.List (intercalate)
import System.Console.ANSI

main :: IO ()
main = do
    --circle
    triangle

circle :: IO ()
circle = do
    let dir = Vec (1 :| 1 :| 1 :| TNil)
    let pos = Vec $ 0 :| 0 :| 20 :| 1 :| TNil
    clearScreen
    forM_ [1..] $ \t -> do
        let rotX = rotX3 (t / 10)
        let rotY = rotY3 (t / 10)
        let transy = trans4 10 0 0
        let rot = mmul rotX rotY
        let dir' = vmul rot dir
        let pos' = vmul (mmul (rotZ4 (t / 10)) transy) pos
        renderFrame $ circ {
            circlePosition = Vec (x pos' :| y pos' :| z pos' :| TNil),
            circleDir = dir'
        }

triangle :: IO ()
triangle = do
    clearScreen
    forM_ [1..] $ \t -> do
        let rotX = rotX4 (t / 8)
        let rotY = rotY4 (t / 10)
        let rotZ = rotZ4 (t / 12)
        let rot = mmul rotX (mmul rotY rotZ)
        renderFrame (transTri rot tri)

renderFrame :: Traceable s => s Double -> IO ()
renderFrame c = do
    forM_ [1..40] $ \y -> do
        forM_ [1..60] $ \x -> do
            setCursorPosition (y - 1) (x - 1)
            let o = Vec $ (fromIntegral x - 30) :| (negate $ fromIntegral y - 20) :| 0 :| TNil
            let ray = Ray o unitZ3
            case (trace c ray) of
                Just h -> putStr $ calcChar (hitNormal h)
                _ -> putStr " "
        putStr "\n"

circ :: Circle Double
circ = Circle pos dir 15.0
    where
    pos = Vec $ 0 :| 0 :| 20 :| TNil
    dir = Vec $ 1 :| 1 :| 1 :| TNil

tri :: Tri Double
tri = Tri a b c
    where
    a = Vec (-15 :| 15 :| 50 :| TNil)
    b = Vec (15 :| 0 :| 50 :| TNil)
    c = Vec (-15 :| 0 :| 50 :| TNil)

transTri :: Matrix4 Double -> Tri Double -> Tri Double
transTri m (Tri a b c) = Tri (tx m a) (tx m b) (tx m c)
    where
    tx m v = to3 . vmul m $ Vec (x v :| y v :| z v :| 1 :| TNil)
    to3 v = Vec (x v :| y v :| z v :| TNil)

posHit :: (Num a, Ord a) => Hit a -> Bool
posHit (Hit p _) | z p > 0 = True
posHit _ = False

calcChar :: Vec3 Double -> String
calcChar v
    | d < 0.25 = "."
    | d < 0.50 = "*"
    | d < 0.75 = "C"
    | otherwise = "#"
    where d = abs $ dot unitZ3 v --double-sided

--
-- The stuff
--

epsilon :: (Floating a, Num a) => a
epsilon = 1e-6

--
-- Types
--

data Nat = Z | S Nat deriving Show

data TList (n :: Nat) a where
    TNil :: TList Z a
    (:|) :: a -> TList n a -> TList (S n) a

infixr 5 :|

instance Show a => Show (TList n a) where
    show = intercalate " :| " . fmap show . toList

instance Functor (TList n) where
    fmap f TNil = TNil
    fmap f (a :| ax) = f a :| fmap f ax

thead :: TList (S n) a -> a
thead (v :| _) = v

ttail :: TList (S n) a -> TList n a
ttail (_ :| v) = v

toList :: TList n a -> [a]
toList TNil = []
toList (a :| ax) = a : toList ax

tzip :: TList n a -> TList n b -> TList n (a, b)
tzip TNil TNil = TNil
tzip (a :| ax) (b :| bx) = (a, b) :| tzip ax bx

newtype Vec r a = Vec { unVec :: (TList r a) } deriving Show

x :: Vec (S x) a -> a
x (Vec (v :| _)) = v

y :: Vec (S (S x)) a -> a
y (Vec (_ :| v :| _)) = v

z :: Vec (S (S (S x))) a -> a
z (Vec (_ :| _ :| v :| _)) = v

w :: Vec (S (S (S (S x)))) a -> a
w (Vec (_ :| _ :| _ :| v :| _)) = v

data Matrix r c a = Matrix { unMatrix :: TList c (TList r a) } deriving Show

--
-- Basic linalg ops
--

add :: Num a => Vec n a -> Vec n a -> Vec n a
add (Vec v1) (Vec v2) = Vec $ fmap (uncurry (+)) (tzip v1 v2)

sub :: Num a => Vec n a -> Vec n a -> Vec n a
sub (Vec v1) (Vec v2) = Vec $ fmap (uncurry (-)) (tzip v1 v2)

mul :: Num a => a -> Vec n a -> Vec n a
mul v (Vec vx) = Vec $ fmap (*v) vx

neg :: Num a => Vec n a -> Vec n a
neg (Vec v) = Vec $ fmap negate v

dot :: Num a => Vec n a -> Vec n a -> a
dot (Vec v1) (Vec v2) = foldl (+) 0 (uncurry (*) <$> zip l1 l2)
    where
    l1 = toList v1
    l2 = toList v2

len :: (Floating a, Num a) => Vec n a -> a
len v = sqrt (dot v v)

normalise :: (Floating a, Num a) => Vec n a -> Vec n a
normalise (Vec v) = Vec $ fmap (/l) v
    where l = len (Vec v)

mmul :: Num a => Matrix (S r) (S c) a -> Matrix (S c) (S n) a -> Matrix (S r) (S n) a
mmul (Matrix m1) (Matrix m2) = transpose m
    where
    Matrix m1t = transpose (Matrix m1)
    m = Matrix $ fmap mrow m1t
    mrow r = fmap (dot (Vec r) . Vec) m2

vmul :: Num a => Matrix (S r) (S c) a -> Vec (S c) a -> Vec (S r) a
vmul m (Vec v) = Vec (thead m')
    where
    Matrix m' = mmul m $ Matrix (v :| TNil)

transpose :: Matrix (S r) (S c) a -> Matrix (S c) (S r) a
transpose (Matrix m@(v :| _)) = Matrix $ toCol v m
    where
    toCol :: TList x a -> TList y (TList x a) -> TList x (TList y a)
    toCol TNil _ = TNil
    toCol (_ :| rx) m' = (fmap thead m') :| toCol rx (fmap ttail m')

--
-- R2 Util
--

type Vec2 = Vec (S (S Z))

--
-- R3 util
--

type Vec3 = Vec (S (S (S Z)))

type Matrix3 = Matrix (S (S (S Z))) (S (S (S Z)))

rotX3 :: (Floating a, Num a) => a -> Matrix3 a
rotX3 rad = Matrix (i :| j :| k :| TNil)
    where
    i = 1 :| 0 :| 0 :| TNil
    j = 0 :| cos rad :| (negate $ sin rad) :| TNil
    k = 0 :| sin rad :| cos rad :| TNil

rotY3 :: (Floating a, Num a) => a -> Matrix3 a
rotY3 rad = Matrix (i :| j :| k :| TNil)
    where
    i = cos rad :| 0 :| (negate $ sin rad) :| TNil
    j = 0 :| 1 :| 0 :| TNil
    k = sin rad :| 0 :| cos rad :| TNil

rotZ3 :: (Floating a, Num a) => a -> Matrix3 a
rotZ3 rad = Matrix (i :| j :| k :| TNil)
    where
    i = cos rad :| (negate $ sin rad) :| 0 :| TNil
    j = sin rad :| cos rad :| 0 :| TNil
    k = 0 :| 0 :| 1 :| TNil

cross :: Num a => Vec3 a -> Vec3 a -> Vec3 a
cross (Vec v1) (Vec v2) = Vec (cx :| cy :| cz :| TNil)
    where
    [x1, y1, z1] = toList v1
    [x2, y2, z2] = toList v2
    cx = y1 * z2 - z1 * y2
    cy = z1 * x2 - x1 * z2
    cz = x1 * y2 - y1 * x2

zero3 :: Num a => Vec3 a
zero3 = Vec (0 :| 0 :| 0 :| TNil)

unitX3 :: Num a => Vec3 a
unitX3 = Vec (1 :| 0 :| 0 :| TNil)

unitY3 :: Num a => Vec3 a
unitY3 = Vec (0 :| 1 :| 0 :| TNil)

unitZ3 :: Num a => Vec3 a
unitZ3 = Vec (0 :| 0 :| 1 :| TNil)

--
-- R4 util
--

type Vec4 = Vec (S (S (S (S Z))))

type Matrix4 = Matrix (S (S (S (S Z)))) (S (S (S (S Z))))

rotX4 :: (Floating a, Num a) => a -> Matrix4 a
rotX4 rad = Matrix (i :| j :| k :| l :| TNil)
    where
    i = 1 :| 0 :| 0 :| 0 :| TNil
    j = 0 :| cos rad :| (negate $ sin rad) :| 0 :| TNil
    k = 0 :| sin rad :| cos rad :| 0 :| TNil
    l = 0 :| 0 :| 0 :| 1 :| TNil

rotY4 :: (Floating a, Num a) => a -> Matrix4 a
rotY4 rad = Matrix (i :| j :| k :| l :| TNil)
    where
    i = cos rad :| 0 :| (negate $ sin rad) :| 0 :| TNil
    j = 0 :| 1 :| 0 :| 0 :| TNil
    k = sin rad :| 0 :| cos rad :| 0 :| TNil
    l = 0 :| 0 :| 0 :| 1 :| TNil

rotZ4 :: (Floating a, Num a) => a -> Matrix4 a
rotZ4 rad = Matrix (i :| j :| k :| l :| TNil)
    where
    i = cos rad :| (negate $ sin rad) :| 0 :| 0 :| TNil
    j = sin rad :| cos rad :| 0 :| 0 :| TNil
    k = 0 :| 0 :| 1 :| 0 :| TNil
    l = 0 :| 0 :| 0 :| 1 :| TNil

trans4 :: Num a => a -> a -> a -> Matrix4 a
trans4 tx ty tz = Matrix (i :| j :| k :| t :| TNil)
    where
    i = 1 :| 0 :| 0 :| 0 :| TNil
    j = 0 :| 1 :| 0 :| 0 :| TNil
    k = 0 :| 0 :| 1 :| 0 :| TNil
    t = tx :| ty :| tz :| 1 :| TNil

zero4 :: Num a => Vec4 a
zero4 = Vec (0 :| 0 :| 0 :| 1 :| TNil)

unitX4 :: Num a => Vec4 a
unitX4 = Vec (1 :| 0 :| 0 :| 1 :| TNil)

unitY4 :: Num a => Vec4 a
unitY4 = Vec (0 :| 1 :| 0 :| 1 :| TNil)

unitZ4 :: Num a => Vec4 a
unitZ4 = Vec (0 :| 0 :| 1 :| 1 :| TNil)

--
-- Tracing
--

class Traceable t where
    trace :: (Floating a, Num a, Ord a, Show a) => t a -> Ray a -> Maybe (Hit a)

data Hit a = Hit {
    hitPosition :: Vec3 a,
    hitNormal :: Vec3 a
}

instance Show a => Show (Hit a) where
    show (Hit (Vec p) (Vec n)) = "Hit " ++ show (toList p) ++ " " ++ show (toList n)

data Ray a = Ray {
    rayOrigin :: Vec3 a,
    rayDirection :: Vec3 a
}

data Plane a = Plane (Vec3 a) a --normal, offset

instance Traceable Plane where
    trace (Plane n s) (Ray o l) = do
        let n' = normalise n
        let l' = normalise l
        let d = dot n' l'
        when (abs d < epsilon) mzero
        let p = sub (mul s n') o
        let t = (dot p n') / d
        (pure . flip Hit (neg n') . add o) (mul t l)

data Circle a = Circle {
    circlePosition :: Vec3 a,
    circleDir :: Vec3 a,
    circleRadius :: a
}

instance Traceable Circle where
    trace (Circle p d r) ray@(Ray o l) = do
        let d' = normalise d
        let s = dot d' p
        hit <- flip trace ray $ Plane d' s
        when (len (sub (hitPosition hit) p) > r) mzero
        pure hit

data Tri a = Tri {
    triA :: Vec3 a,
    triB :: Vec3 a,
    triC :: Vec3 a
}

instance Traceable Tri where
    trace tri@(Tri a b c) ray@(Ray o l) = do
        let norm = neg . normalise $ cross (sub b a) (sub c a)
        let plane = Plane norm (dot norm $ normalise l)
        Hit pos _ <- trace plane ray
        let basis = triBasis tri
        let pos' = vmul basis $ Vec (x pos :| y pos :| z pos :| 1 :| TNil)
        let a' = vmul basis $ Vec (x a :| y a :| z a :| 1 :| TNil)
        let b' = vmul basis $ Vec (x b :| y b :| z b :| 1 :| TNil)
        let c' = vmul basis $ Vec (x c :| y c :| z c :| 1 :| TNil)
        let pos2 = Vec (x pos' :| y pos' :| TNil)
        let a2 = Vec (x a' :| y a' :| TNil)
        let b2 = Vec (x b' :| y b' :| TNil)
        let c2 = Vec (x c' :| y c' :| TNil)
        when (not $ isInTri (a2, b2, c2) pos2) mzero
        pure (Hit pos norm)

isInTri :: (Floating a, Num a, Ord a, Show a) => (Vec2 a, Vec2 a, Vec2 a) -> Vec2 a -> Bool
isInTri (t1, t2, t3) p = b1 == b2 && b2 == b3
    where
    b1 = triSign p t1 t2 < 0
    b2 = triSign p t2 t3 < 0
    b3 = triSign p t3 t1 < 0
    triSign p1 p2 p3 = (x p1 - x p3) * (y p2 - y p3) - (x p2 - x p3) * (y p1 - y p3)

triBasis :: (Floating a, Num a, Ord a) => Tri a -> Matrix4 a
triBasis (Tri a b c) = mmul t (transpose r)
    where
    vz' = neg . normalise $ cross (sub b a) (sub c a)
    vy' = normalise $ cross vz' (sub b a)
    vz = to4 vz'
    vy = to4 vy'
    vx = to4 . normalise $ cross vz' vy'
    r = Matrix (vx :| vy :| vz :| (0 :| 0 :| 0 :| 1 :| TNil) :| TNil)
    t = trans4 (negate $ x a) (negate $ y a) (negate $ z a)
    to4 v = (x v :| y v :| z v :| 0 :| TNil)
