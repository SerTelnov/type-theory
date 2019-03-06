module Proof

-- задание 4 (для сдавших 21 января)

mulSumStatement : (x: Nat) -> (k ** (2 * k = x + x))
mulSumStatement Z     = (Z ** Refl)
-- mulSumStatement (S x) = ((S x) ** Refl) не может plus k 0 = k
mulSumStatement (S x) = (S x ** (rewrite (plusZeroRightNeutral (S x)) in Refl))

-- если порефакторить

mulSumStatement2 : (x : Nat) -> (k ** (2 * k = x + x))
mulSumStatement2 x = (x ** (rewrite (plusZeroRightNeutral x) in Refl))

-- общее задание 7

-- Идея доказательства
-- докажет два основных утверждения и сведем к постановке задачи
-- 1. a - b <= a + b             lteMinusPlus
-- 2. a <= b ==> a * a <= b * b  lteSquare
--
-- Тогда подставим во 2. {a = x - y} {b = x + y} {x - y <= x + y}
-- и получим (x - y)^2 <= (x + y)^2
-- по определению разности для Nat (a <= b) -> a - b = 0
-- читд (minusSquaresIsZeroStatement)


-- вспомогательные функции (которых почему-то нет в библиотеке)

total
lteAddLeft : (n, m: Nat) -> LTE n (plus m n)
lteAddLeft Z _     = LTEZero
lteAddLeft (S x) k = rewrite (sym $ plusSuccRightSucc k x) in
  rewrite (plusCommutative k x) in LTESucc $ lteAddRight x

total
multRightPlusSucc : (a, b: Nat) -> a * b + a = a * (S b)
multRightPlusSucc x y = replace {P = \w => w = x * (S y)}
  (plusCommutative x (x * y)) (sym $ multRightSuccPlus x y)

-- вспомогательные функции, который понадобились для доказательства

total
lteLeftConsPlus : (a, b, cons: Nat) -> LTE a b -> LTE (plus cons a) (plus cons b)
lteLeftConsPlus Z _ cons _  = rewrite (plusZeroRightNeutral cons) in lteAddRight cons
lteLeftConsPlus (S x) (S y) cons (LTESucc ord) = rewrite (sym $ plusSuccRightSucc cons x) in
  rewrite (sym $ plusSuccRightSucc cons y) in
    LTESucc $ lteLeftConsPlus x y cons ord

total
lteRightConsPlus : (a, b, cons: Nat) -> LTE a b -> LTE (plus a cons) (plus b cons)
lteRightConsPlus Z y cons _ = lteAddLeft cons y
lteRightConsPlus (S x) (S y) cons (LTESucc ord) = LTESucc $
  lteRightConsPlus x y cons ord

total
lte4Plus2 : (a, b, c, d: Nat) -> LTE a b -> LTE c d -> LTE (a + c) (b + d)
lte4Plus2 Z Z c d _ ord = ord
lte4Plus2 a b Z Z ord _ = rewrite (plusZeroRightNeutral a) in
  rewrite (plusZeroRightNeutral b) in ord
lte4Plus2 (S a) (S b) (S c) (S d) (LTESucc x) (LTESucc y) = LTESucc $
  rewrite (sym $ plusSuccRightSucc a c) in
    rewrite (sym $ plusSuccRightSucc b d) in
      LTESucc $ lte4Plus2 a b c d x y

total
lteMult2LeftRightLeft : (a, b: Nat) -> LTE a b -> LTE (a * a) (b * a)
lteMult2LeftRightLeft Z _ _                     = LTEZero
lteMult2LeftRightLeft (S x) (S y) (LTESucc ord) = LTESucc $
  rewrite (sym $ multRightPlusSucc x x) in
    rewrite (sym $ multRightPlusSucc y x) in
      lteLeftConsPlus (plus (mult x x) x) (plus (mult y x) y) x $
      lte4Plus2 (x * x) (y * x) x y (lteMult2LeftRightLeft x y ord) ord

total
lteMultRightLeft2Right : (a, b: Nat) -> LTE a b -> LTE (b * a) (b * b)
lteMultRightLeft2Right Z y _                     = rewrite (multZeroRightZero y) in LTEZero
lteMultRightLeft2Right (S x) (S y) (LTESucc ord) = LTESucc $
  rewrite (sym $ multRightPlusSucc y x) in
    rewrite (sym $ multRightPlusSucc y y) in
      lte4Plus2 x y (plus (mult y x) y) (plus (mult y y) y) ord $
      lteRightConsPlus (y * x) (y * y) y $ lteMultRightLeft2Right x y ord

-- основные утверждения

total
lteMinusPlus : (a, b: Nat) -> LTE (minus a b) (plus a b)
lteMinusPlus Z     _     = LTEZero
lteMinusPlus (S x) Z     = rewrite (plusZeroRightNeutral (S x)) in lteRefl
lteMinusPlus (S x) (S y) = let ih = lteMinusPlus x y in
    rewrite sym $ plusSuccRightSucc x y in
        lteSuccRight $ lteSuccRight ih

total
lteSquare : (a, b: Nat) -> LTE a b -> LTE (a * a) (b * b)
lteSquare x y ord = lteTransitive (lteMult2LeftRightLeft x y ord) (lteMultRightLeft2Right x y ord)

total
lteMinusIsZero : LTE a b -> minus a b = 0
lteMinusIsZero LTEZero     = Refl
lteMinusIsZero (LTESucc x) = lteMinusIsZero x

total
minusSquaresIsZeroStatement : (a, b: Nat) -> minus ((minus a b) * (minus a b)) ((plus a b) * (plus a b)) = 0
minusSquaresIsZeroStatement a b = lteMinusIsZero $ lteSquare (minus a b) (plus a b) (lteMinusPlus a b)
