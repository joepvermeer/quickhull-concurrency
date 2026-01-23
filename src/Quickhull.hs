{-# LANGUAGE BlockArguments    #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RebindableSyntax  #-}
{-# LANGUAGE TypeOperators     #-}

module Quickhull (

  Point, Line, SegmentedPoints,
  quickhull,

  -- Exported for display
  initialPartition,
  partition,

  -- Exported just for testing
  propagateL, shiftHeadFlagsL, segmentedScanl1,
  propagateR, shiftHeadFlagsR, segmentedScanr1,

) where

import Data.Array.Accelerate
import Data.Array.Accelerate.Debug.Trace
import qualified Prelude                      as P

-- IMPORTANT NOTE FOR SELF 
-- Work ways, personal first steps to do in assignment 
-- 1. Understand the problem domain (convex hulls, quickhull algorithm)
-- 2. Familiarize with the Accelerate library and its data types
-- 3. Implement the initialPartition function
-- 4. Implement the partition function
-- 5. Implement the quickhull function
-- 6. Test each function thoroughly

-- choose one line 
-- split de remaining pount in sets Left/Right of this line 
-- search per sub set the point furthest from the line --> this point is on the hull
-- repeat recursively until no points are left --> recursively will be done in data parallel way 

-- there are three layers for solving the problem
-- first the "helper-functions; shifts, segmentscanl & r, propagatel & r
-- second is the quickhull core in segmented form  (initial partition and partition ) 
-- third is the quickhull function quickhull :: Acc (Vector Point) -> Acc (Vector Point)

-- NOTE: the operator :. is used to construct shapes in Accelerate, such as Z :. n for a 1D array of length n.
---------------------------


-- Points and lines in two-dimensional space
--
type Point = (Int, Int)
type Line  = (Point, Point)

-- This algorithm will use a head-flags array to distinguish the different
-- sections of the hull (the two arrays are always the same length).
--
-- A flag value of 'True' indicates that the corresponding point is
-- definitely on the convex hull. The points after the 'True' flag until
-- the next 'True' flag correspond to the points in the same segment, and
-- where the algorithm has not yet decided whether or not those points are
-- on the convex hull.
--
type SegmentedPoints = (Vector Bool, Vector Point)


-- Core implementation
-- -------------------

-- Initialise the algorithm by first partitioning the array into two
-- segments. Locate the left-most (p₁) and right-most (p₂) points. The
-- segment descriptor then consists of the point p₁, followed by all the
-- points above the line (p₁,p₂), followed by the point p₂, and finally all
-- of the points below the line (p₁,p₂).
--
-- To make the rest of the algorithm a bit easier, the point p₁ is again
-- placed at the end of the array.
--
-- We indicate some intermediate values that you might find beneficial to
-- compute.
--
initialPartition :: Acc (Vector Point) -> Acc SegmentedPoints
initialPartition points =
  let
      p1, p2 :: Exp Point
      -- locate the left-most point, p1 with smallest x, if they are the same x choose the one with smallest y
      p1 = the (fold1 minPoint points)
      -- locate the right-most point, p2 with largest x, if they are the same x choose the one with largest y
      p2 = the (fold1 maxPoint points)

      --for isupper en islower we can use te pointIsLeftOfLine function

      -- True for points strictly above line (p1, p2)
      -- points above the line (p1, p2)
      isUpper :: Acc (Vector Bool)
      isUpper =
        let line = T2 p1 p2
        in  map (pointIsLeftOfLine line) points


      -- True for points strictly below line (p1, p2)
      -- points below the line (p1, p2)
      isLower :: Acc (Vector Bool)
      isLower =
        let lineRev = T2 p2 p1
        in  map (pointIsLeftOfLine lineRev) points

      offsetUpper :: Acc (Vector Int) -- every position where isUpper is true, this will give the compacted index from point to upper-array
      countUpper  :: Acc (Scalar Int) -- total number upper points
      T2 offsetUpper countUpper = boolOffsetsAndCount isUpper

      offsetLower :: Acc (Vector Int)
      countLower  :: Acc (Scalar Int)
      T2 offsetLower countLower = boolOffsetsAndCount isLower

      -- destination[i]: index in result array for point i, or Nothing if dropped
      destination :: Acc (Vector (Maybe DIM1))
      destination =
        let
          -- scalar countUpper to Exp Int
          cUpper :: Exp Int
          cUpper = the countUpper
        in
        generate (shape points) $ \ix ->
          let
            Z :. i      = unlift ix :: Z :. Exp Int
            isU         = isUpper ! index1 i
            isL         = isLower ! index1 i
            offU        = offsetUpper ! index1 i
            offL        = offsetLower ! index1 i

            -- index for upper points: start at 1, then offsetUpper
            dstUpper    = 1 + offU

            -- index for lower points: start at 2 + countUpper, then offsetLower
            dstLower    = 2 + cUpper + offL
          in
          if isU
            then Just_ (index1 dstUpper)
            else if isL
              then Just_ (index1 dstLower)
              else Nothing_

      newPoints :: Acc (Vector Point)
      newPoints = 
        let
          u :: Exp Int
          u = the countUpper

          l :: Exp Int
          l = the countLower

          totalLen :: Exp Int
          totalLen = 3 + u + l

          sh :: Exp DIM1
          sh = index1 totalLen

          -- base array filled with p1 everywhere
          base :: Acc (Vector Point)
          base = generate sh (\_ -> p1)

          -- place all upper points at indices 1 + offsetUpper[i]
          upperPlaced :: Acc (Vector Point)
          upperPlaced =
            permute
              const
              base
              (\ix ->
                 let Z :. i = unlift ix :: Z :. Exp Int
                     isU    = isUpper ! index1 i
                     offU   = offsetUpper ! index1 i
                 in
                 if isU
                   then Just_ (index1 (1 + offU))
                   else Nothing_)
              points

          -- place all lower points at indices 2 + u + offsetLower[i]
          upperAndLower :: Acc (Vector Point)
          upperAndLower =
            permute
              const
              upperPlaced
              (\ix ->
                 let Z :. i = unlift ix :: Z :. Exp Int
                     isL    = isLower ! index1 i
                     offL   = offsetLower ! index1 i
                 in
                 if isL
                   then Just_ (index1 (2 + u + offL))
                   else Nothing_)
              points

          -- fix the three hull points: p1 at 0 and at end, p2 at 1+u
        in
        generate sh $ \ix ->
          let
            Z :. i = unlift ix :: Z :. Exp Int
          in
          if i == 0 then
            p1
          else if i == 1 + u then
            p2
          else if i == totalLen - 1 then
            p1
          else
            upperAndLower ! ix

      headFlags :: Acc (Vector Bool)
      headFlags = 
        let
          u :: Exp Int
          u = the countUpper

          l :: Exp Int
          l = the countLower

          totalLen :: Exp Int
          totalLen = 3 + u + l

          sh :: Exp DIM1
          sh = index1 totalLen
        in
        generate sh $ \ix ->
          let
            Z :. i = unlift ix :: Z :. Exp Int
          in
          i == 0 || i == 2 + u
  in
  T2 headFlags newPoints


  ------------------
-- helper functions for initialPartition

-- choose smallest point for x then y
minPoint :: Exp Point -> Exp Point -> Exp Point
minPoint (T2 x1 y1) (T2 x2 y2) =
  if x1 < x2 then T2 x1 y1
  else if x1 > x2 then T2 x2 y2
  else if y1 <= y2 then T2 x1 y1
  else T2 x2 y2


-- choose largest point for x then y
maxPoint :: Exp Point -> Exp Point -> Exp Point
maxPoint (T2 x1 y1) (T2 x2 y2) =
  if x1 > x2 then T2 x1 y1
  else if x1 < x2 then T2 x2 y2
  else if y1 >= y2 then T2 x1 y1
  else T2 x2 y2



-- turn a bool vector into offsets and count of True values
boolOffsetsAndCount :: Acc (Vector Bool) -> Acc (Vector Int, Scalar Int)
boolOffsetsAndCount flags =
  let
    -- True/False -> 1/0
    flagsInt :: Acc (Vector Int)
    flagsInt = map boolToInt flags

    -- running count
    prefix :: Acc (Vector Int)
    prefix = scanl1 (+) flagsInt

    -- total = last element
    count :: Acc (Scalar Int)
    count =
      let Z :. n = unlift (shape prefix) :: Z :. Exp Int
      in  slice prefix (lift (Z :. n - 1))

    -- offset[i] = prefix[i] - 1 for True entries
    offsets :: Acc (Vector Int)
    offsets =
      map
        (\(T2 fl pref) ->
            if fl
              then pref - 1
              else 0)   -- value for False won't be used
        (zip flags prefix)
  in
  lift (offsets, count)


-- The core of the algorithm processes all line segments at once in
-- data-parallel. This is similar to the previous partitioning step, except
-- now we are processing many segments at once.
--
-- For each line segment (p₁,p₂) locate the point furthest from that line
-- p₃. This point is on the convex hull. Then determine whether each point
-- p in that segment lies to the left of (p₁,p₃) or the right of (p₂,p₃).
-- These points are undecided.


partition :: Acc SegmentedPoints -> Acc SegmentedPoints
partition (T2 headFlags points) =
  let
    leftPts  :: Acc (Vector Point)
    leftPts  = propagateL headFlags points

    rightPts :: Acc (Vector Point)
    rightPts = propagateR headFlags points

    distances :: Acc (Vector Int)
    distances =
      zipWith3
        (\p l r -> nonNormalizedDistance (T2 l r) p)
        points
        leftPts
        rightPts

    -- Gebruik segmentedScanr1 om het maximum door het hele segment te propageren
    maxDist :: Acc (Vector Int)
    maxDist = segmentedScanr1 max headFlags distances

    isFarthest :: Acc (Vector Bool)
    isFarthest =
      zipWith3
        (\d m h -> (d == m) && not h)
        distances
        maxDist
        headFlags

    newHeadFlags :: Acc (Vector Bool)
    newHeadFlags =
      zipWith (||) headFlags isFarthest

    -- Propageer farthest punt binnen nieuwe segmenten
    farthestPts :: Acc (Vector Point)
    farthestPts = propagateL newHeadFlags points

    leftOfLeft :: Acc (Vector Bool)
    leftOfLeft =
      zipWith4
        (\p l f nf -> not nf && pointIsLeftOfLine (T2 l f) p)
        points
        leftPts
        farthestPts
        newHeadFlags

    rightOfRight :: Acc (Vector Bool)
    rightOfRight =
      zipWith4
        (\p f r nf -> not nf && pointIsLeftOfLine (T2 f r) p)
        points
        farthestPts
        rightPts
        newHeadFlags

    keep :: Acc (Vector Bool)
    keep =
      zipWith3
        (\h l r -> h || l || r)
        newHeadFlags
        leftOfLeft
        rightOfRight

    flags'  :: Acc (Vector Bool)
    flags'  = packAcc keep newHeadFlags

    points' :: Acc (Vector Point)
    points' = packAcc keep points

  in
  T2 flags' points'


-- The completed algorithm repeatedly partitions the points until there are
-- no undecided points remaining. What remains is the convex hull.
--
quickhull :: Acc (Vector Point) -> Acc (Vector Point)
quickhull =
  error "TODO: quickhull"


-- Helper functions
-- ----------------

-- >>> import Data.Array.Accelerate.Interpreter
-- >>> let flags  = fromList (Z :. 9) [True,False,False,True,True,False,False,False,True]
-- >>> let values = fromList (Z :. 9) [1   ,2    ,3    ,4   ,5   ,6    ,7    ,8    ,9   ] :: Vector Int
-- >>> run $ propagateL (use flags) (use values)
--
-- should be:
-- Vector (Z :. 9) [1,1,1,4,5,5,5,5,9]

-- each true in flag is a new segment start
-- each propagateL copies the source value to the left until a new segment start is reached



-- copy the value at each head-flag to the right within its segment
-- depends on segmentedScanl1
propagateL :: Elt a => Acc (Vector Bool) -> Acc (Vector a) -> Acc (Vector a)
propagateL flags values = segmentedScanl1 (\left _right -> left) flags values   -- in a left-to-right segmented scan, always keep the left value



-- >>> import Data.Array.Accelerate.Interpreter
-- >>> let flags  = fromList (Z :. 9) [True,False,False,True,True,False,False,False,True]
-- >>> let values = fromList (Z :. 9) [1   ,2    ,3    ,4   ,5   ,6    ,7    ,8    ,9   ] :: Vector Int
-- >>> run $ propagateR (use flags) (use values)
--
-- should be:
-- Vector (Z :. 9) [1,4,4,4,5,9,9,9,9]


-- propagateR needs a little different approach
-- for propagateR we need the next head-flag to the right (over segment boundaries),
-- so we first compute, for each index, the position of the next True to the right with a scanr1 and then index into values.
propagateR :: Elt a => Acc (Vector Bool) -> Acc (Vector a) -> Acc (Vector a)
propagateR flags values =
  let
    Z :. n = unlift (shape flags) :: Z :. Exp Int
    big    = n  -- sentinel index "no head"

    -- start[i] = i if flags[i] is True, otherwise big
    start = generate (shape flags) $ \ix ->
        let Z :. i = unlift ix :: Z :. Exp Int
        in  if flags ! index1 i
              then i
              else big

    -- nextHeadIdx[i] = index of first True at or to the right of i
    nextHeadIdx = scanr1 min start

    -- result[i] = values[ nextHeadIdx[i] ]
    result = generate (shape values) $ \ix ->
        let
          Z :. i = unlift ix :: Z :. Exp Int
          j      = nextHeadIdx ! index1 i
        in
          values ! index1 j
  in
  result
-- >>> import Data.Array.Accelerate.Interpreter
-- >>> run $ shiftHeadFlagsL (use (fromList (Z :. 6) [False,False,False,True,False,True]))
--
-- should be:
-- Vector (Z :. 6) [False,False,True,False,True,True]


-- shift head flags one position to the left 
-- out[i] for i < n+1, and out[n-1] = in [n-1] 
shiftHeadFlagsL :: Acc (Vector Bool) -> Acc (Vector Bool)
shiftHeadFlagsL flags =
  let
    Z :. n = unlift (shape flags) :: Z :. Exp Int  -- length of vector 
  in
  generate (shape flags) $ \ix ->
    let
      Z :. i   = unlift ix :: Z :. Exp Int
      notLast  = i < n - 1
      this     = flags ! index1 i
      shifted  = flags ! index1 (i + 1)
    in
    if notLast
      then shifted  -- use element right of current
      else this    -- last element remains the same

-- >>> import Data.Array.Accelerate.Interpreter
-- >>> run $ shiftHeadFlagsR (use (fromList (Z :. 6) [True,False,False,True,False,False]))
--
-- should be:
-- Vector (Z :. 6) [True,True,False,False,True,False]


-- same as shiftHeadFlagsL but to the right 
-- so in short: shift head-flags one position to the right 
shiftHeadFlagsR :: Acc (Vector Bool) -> Acc (Vector Bool)
shiftHeadFlagsR flags =
  let
    Z :. _n = unlift (shape flags) :: Z :. Exp Int --length of vector again 
  in
  generate (shape flags) $ \ix ->
    let
      Z :. i  = unlift ix :: Z :. Exp Int
      notFirst = i > 0
      this    = flags ! index1 i
      shifted = flags ! index1 (i - 1)
    in
    if notFirst
      then shifted   -- use element on the left
      else this      -- first element remains the same

-- >>> import Data.Array.Accelerate.Interpreter
-- >>> let flags  = fromList (Z :. 9) [True,False,False,True,True,False,False,False,True]
-- >>> let values = fromList (Z :. 9) [1   ,2    ,3    ,4   ,5   ,6    ,7    ,8    ,9   ] :: Vector Int
-- >>> run $ segmentedScanl1 (+) (use flags) (use values)
--
-- Expected answer:
-- >>> fromList (Z :. 9) [1, 1+2, 1+2+3, 4, 5, 5+6, 5+6+7, 5+6+7+8, 9] :: Vector Int
-- Vector (Z :. 9) [1,3,6,4,5,11,18,26,9]
--
-- Mind that the interpreter evaluates scans and folds sequentially, so
-- non-associative combination functions may seem to work fine here -- only to
-- fail spectacularly when testing with a parallel backend on larger inputs. ;)

-- dependent on the headflags functions 
-- every true in flags is the beginning of a new segment
-- so segmented scanl1 applies the function f to all elements in a segment
-- I've broken up the type signature so you'll see what are the inputs and type result. function itself is straight forward
segmentedScanl1 
    :: Elt a 
    => (Exp a -> Exp a -> Exp a) -- combine function 
    -> Acc (Vector Bool) -- head-flags 
    -> Acc (Vector a) -- values
    -> Acc (Vector a) -- segmented scan 
segmentedScanl1 f flags values =
  let
    -- combine flags and values into (flag, value) pairs
    flagged = zipWith (\fl v -> T2 fl v) flags values

    -- normal scanl1, but with segmented combine function
    scanned = scanl1 (segmented f) flagged
  in
  -- Only extract the value component from the pairs
  map (\(T2 _ v) -> v) scanned

-- >>> import Data.Array.Accelerate.Interpreter
-- >>> let flags  = fromList (Z :. 9) [True,False,False,True,True,False,False,False,True]
-- >>> let values = fromList (Z :. 9) [1   ,2    ,3    ,4   ,5   ,6    ,7    ,8    ,9   ] :: Vector Int
-- >>> run $ segmentedScanr1 (+) (use flags) (use values)
--
-- Expected answer:
-- >>> fromList (Z :. 9) [1, 2+3+4, 3+4, 4, 5, 6+7+8+9, 7+8+9, 8+9, 9] :: Vector Int
-- Vector (Z :. 9) [1,9,7,4,5,30,24,17,9]


-- same as segmentedScanl1 but right to left 
-- cannot reuse the same segmented combine function as scanl1 directly because scan1 processes elements from right to left 
-- with a different combine order 
-- so reverse flags and values, reuse segmentedScanl1, and reverse the result again 
segmentedScanr1 
    :: Elt a 
    => (Exp a -> Exp a -> Exp a) -- combine function 
    -> Acc (Vector Bool) -- head-flags 
    -> Acc (Vector a) -- values
    -> Acc (Vector a) -- segmented scan (right-to-left)
segmentedScanr1 f flags values =
  let
    -- reverse both flags and values
    revFlags  = reverse flags
    revValues = reverse values

    -- segmented scan from left-to-right on the reversed arrays
    revResult = segmentedScanl1 f revFlags revValues
  in
    -- reverse the result back to original order
    reverse revResult


-- Given utility functions
-- -----------------------

pointIsLeftOfLine :: Exp Line -> Exp Point -> Exp Bool
pointIsLeftOfLine (T2 (T2 x1 y1) (T2 x2 y2)) (T2 x y) = nx * x + ny * y > c
  where
    nx = y1 - y2
    ny = x2 - x1
    c  = nx * x1 + ny * y1

nonNormalizedDistance :: Exp Line -> Exp Point -> Exp Int
nonNormalizedDistance (T2 (T2 x1 y1) (T2 x2 y2)) (T2 x y) = nx * x + ny * y - c
  where
    nx = y1 - y2
    ny = x2 - x1
    c  = nx * x1 + ny * y1

segmented :: Elt a => (Exp a -> Exp a -> Exp a) -> Exp (Bool, a) -> Exp (Bool, a) -> Exp (Bool, a)
segmented f (T2 aF aV) (T2 bF bV) = T2 (aF || bF) (if bF then bV else f aV bV)

-- | Read a file (such as "inputs/1.dat") and return a vector of points,
-- suitable as input to 'quickhull' or 'initialPartition'. Not to be used in
-- your quickhull algorithm, but can be used to test your functions in ghci.
readInputFile :: P.FilePath -> P.IO (Vector Point)
readInputFile filename =
  (\l -> fromList (Z :. P.length l) l)
  P.. P.map (\l -> let ws = P.words l in (P.read (ws P.!! 0), P.read (ws P.!! 1)))
  P.. P.lines
  P.<$> P.readFile filename
