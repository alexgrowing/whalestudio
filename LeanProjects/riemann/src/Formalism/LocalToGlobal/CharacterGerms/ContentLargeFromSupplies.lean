import Formalism.LocalToGlobal.CharacterGerms.Interface
import Formalism.LocalToGlobal.CharacterGerms.ValuationChoiceHypothesis

noncomputable section
open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds Formalism.UnitaryBoundIntegral Formalism.L2.DIV Formalism.BasicNotions

variable {C : Type} [Field C] {V : VF C} {d : ℕ} [NeZero d] {I J : Fin 2 → Type}
  [∀ g, Fintype (I g)] [∀ g, Fintype (J g)]

def RowData.rk (X : RowData C V d I J) (g : Fin 2) (a : ZMod d) : ℕ :=
  (Finset.univ.filter fun c : I g => (X.G g).ty (Sum.inl c) = a).card

structure Flag (X : RowData C V d I J) where
  en : ∀ g a, Fin (X.rk g a) → I g
  en_inj : ∀ g a, Function.Injective (en g a)
  en_ty : ∀ g a c, (X.G g).ty (Sum.inl (en g a c)) = a

def Flag.letter {X : RowData C V d I J} (F : Flag X) (g : Fin 2) (a : ZMod d) {N : ℕ}
    (x : Fin N × Fin (X.rk g a)) : Fin N × WV I := (x.1, ⟨g, F.en g a x.2⟩)

def bg (a : ZMod d) : Fin 2 := if Even a.val then 0 else 1

inductive GlobalTheory (d : ℕ) where

  | bi (g : Fin 2) (a : ZMod d) (i y : ℕ)

  | ch (g : Fin 2) (a : ZMod d) (u : ℕ)

  | mon (g : Fin 2) (e : ZMod d → ℕ → ℕ) (N : ℕ)

namespace GlobalTheory

def what₂ (n : ℕ) : GlobalTheory d → ℕ
  | bi _ _ _ _ => n
  | ch _ _ _ => n
  | mon _ _ N => N

variable (X : RowData C V d I J) (F : Flag X)

def poly : (b : GlobalTheory d) → MvPolynomial (Fin (b.what₂ X.n) × WV I) C
  | bi g a i y =>
      MvPolynomial.rename (F.letter g a) (minorK C X.n (X.rk g a) X.n) ^ (V.l ^ i * y) *
        MvPolynomial.rename (F.letter (1 - g) (a + (i : ZMod d)))
          (minorK C X.n (X.rk (1 - g) (a + (i : ZMod d))) X.n) ^ y
  | ch g a u => MvPolynomial.rename (F.letter g a) (minorK C X.n (X.rk g a) X.n) ^ u
  | mon g e N => ∏ a : ZMod d, MvPolynomial.rename (F.letter g a) (monP C N (X.rk g a) (e a))

def kind (n : ℕ) : (b : GlobalTheory d) → Fin (b.what₂ n) → Option (Fin 2 × ZMod d × ZMod d)
  | bi g a i _ => fun _ => some (g, a, a + (i : ZMod d))
  | ch _ _ _ => fun _ => none
  | mon _ _ _ => fun _ => none

def wt : GlobalTheory d → Fin 2 → ZMod d → ℕ → ℕ
  | bi g a i y => fun g' a' k =>
      (if g' = g ∧ a' = a ∧ k = X.n then V.l ^ i * y else 0) +
        (if g' = 1 - g ∧ a' = a + (i : ZMod d) ∧ k = X.n then y else 0)
  | ch g a u => fun g' a' k => if g' = g ∧ a' = a ∧ k = X.n then u else 0
  | mon g e N => fun g' a' k => if g' = g ∧ 1 ≤ k ∧ k ≤ min N (X.rk g a') then e a' k else 0

def Attains (b : GlobalTheory d) (c : ℝ) : Prop :=
  ∃ (S : ∀ g, Sys (X.G g)) (t : ∀ g, I g → MvPowerSeries (I g) C), (∀ g, (S g).IsT (t g)) ∧
    ∃ gr : Fin (b.what₂ X.n) → MvPowerSeries (WV I) C, (∀ ρ, gr ρ ∈ IntGerm V t) ∧
      V.v (ValOf X.hL (b.poly X F) (b.kind X.n) gr) ≤ ((c : ℝ) : WithTop ℝ)

end GlobalTheory

def BiSupply : Prop :=
  ∀ (C : Type) [Field C] (V : VF C) (d : ℕ) [NeZero d] (I J : Fin 2 → Type) [∀ g, Fintype (I g)]
    [∀ g, Fintype (J g)] (X : RowData C V d I J) (F : Flag X), X.Alt → 5 ≤ V.l → 1 ≤ X.n →
    ∀ g a, X.big g a → ∀ i : ℕ, Odd i → i < d →
      Windows (S0 V.l i X.n) {y | (GlobalTheory.bi g a i y).Attains X F (blockBd V.l X.n X.m i y)}

def CHSupply : Prop :=
  ∀ (C : Type) [Field C] (V : VF C) (d : ℕ) [NeZero d] (I J : Fin 2 → Type) [∀ g, Fintype (I g)]
    [∀ g, Fintype (J g)] (X : RowData C V d I J) (F : Flag X), ∀ g a, X.big g a → ∀ u : ℕ,
      (X.Alt → (GlobalTheory.ch g a u).Attains X F (chBd V.l X.n X.m u)) ∧
      ((∀ a, X.big g a) → (GlobalTheory.ch g a u).Attains X F ((u : ℝ) * (X.m / ((V.l : ℝ) - 1))))

def monDegAll (X : RowData C V d I J) (g : Fin 2) (e : ZMod d → ℕ → ℕ) (N : ℕ) : ℕ :=
  ∑ a : ZMod d, monDeg N (X.rk g a) (e a)

def UBSupply : Prop :=
  ∀ (C : Type) [Field C] (V : VF C) (d : ℕ) [NeZero d] (I J : Fin 2 → Type) [∀ g, Fintype (I g)]
    [∀ g, Fintype (J g)] (X : RowData C V d I J) (F : Flag X), X.Alt → 5 ≤ V.l → 1 ≤ X.n →
    ∀ g a, X.big g a → ∀ y : ℕ, y + X.n ≤ V.l - 1 →
      (GlobalTheory.bi g a 1 y).Attains X F (2 * (X.m : ℝ) * y)

def MONSupply : Prop :=
  ∀ (C : Type) [Field C] (V : VF C) (d : ℕ) [NeZero d] (I J : Fin 2 → Type) [∀ g, Fintype (I g)]
    [∀ g, Fintype (J g)] (X : RowData C V d I J) (F : Flag X) (g : Fin 2) (e : ZMod d → ℕ → ℕ)
    (N : ℕ),
      (GlobalTheory.mon g e N).Attains X F ((monDegAll X g e N : ℝ) / ((V.l : ℝ) - 1)) ∧
      ((∀ a ρ, monAl N (X.rk g a) (e a) ρ < V.l) → (GlobalTheory.mon g e N).Attains X F 0)

def ValBlocks {Orb : Type} [Fintype Orb] {I J : Orb → Fin 2 → Type} [∀ o g, Fintype (I o g)]
    [∀ o g, Fintype (J o g)] (X : ∀ o, RowData C V d (I o) (J o)) (F : ∀ o, Flag (X o))
    (Z : Finset Orb) (nW : ℕ) (ga : Orb → Fin 2 → ZMod d → ℕ → ℕ) (ν : ℝ) : Prop :=
  ∀ L : Orb → List (GlobalTheory d × ℝ),
    (∀ o ∈ Z, ∀ p ∈ L o, p.1.Attains (X o) (F o) p.2) →
    (∑ o ∈ Z, ((L o).map fun p => p.1.what₂ (X o).n).sum) ≤ nW →
    (∀ o ∈ Z, ∀ g a k, ((L o).map fun p => p.1.wt (X o) g a k).sum = ga o g a k) →
    ν ≤ ∑ o ∈ Z, ((L o).map Prod.snd).sum

def restDeg (bgr : ZMod d → Fin 2) (n : ℕ) (ga : Fin 2 → ZMod d → ℕ → ℕ) (K : ℕ) : ℕ :=
  ∑ g : Fin 2, ∑ a : ZMod d, ∑ k ∈ Finset.Icc 1 K, if g = bgr a ∧ k = n then 0 else k * ga g a k

def totDeg (ga : Fin 2 → ZMod d → ℕ → ℕ) (K : ℕ) : ℕ :=
  ∑ g : Fin 2, ∑ a : ZMod d, ∑ k ∈ Finset.Icc 1 K, k * ga g a k

structure WtHyp (N : NumDatum) (l : ℕ) (Z : Finset (RPl N.R)) (bgr : ZMod (N.ordP l) → Fin 2)
    (rk : RPl N.R → Fin 2 → ZMod (N.ordP l) → ℕ)
    (ga : RPl N.R → Fin 2 → ZMod (N.ordP l) → ℕ → ℕ) (W exc : RPl N.R → ℕ) (rest : ℝ) : Prop where
  supp : ∀ z ∈ Z, ∀ g a k, ga z g a k ≠ 0 → 1 ≤ k ∧ k ≤ rk z g a
  main : ∀ z ∈ Z, ∀ a, ga z (bgr a) a (N.R.k - 1) = alongOrb N l z W a + alongOrb N l z exc a
  rest_eq : rest = ∑ z ∈ Z, ((restDeg bgr (N.R.k - 1) (ga z) N.R.r : ℝ) +
    ∑ a, ((N.R.k : ℝ) - 1) * ((alongOrb N l z exc a : ℕ) : ℝ))

def ContentAt (C1 Cc : ℝ) : Prop :=
  ∀ (N : NumDatum) (j l : ℕ) (Z : Finset (RPl N.R)), l.Prime → 5 ≤ l → IsReps N l Z →
    (N.cls l = PrimeClass.inertClass ∨ N.cls l = PrimeClass.signal) →
    ¬ (N.cls l = PrimeClass.inertClass ∧ N.hP l = 0) →
    ∀ (C : Type) [Field C] (V : VF C), V.l = l →
    ∀ (I J : RPl N.R → Fin 2 → Type) [∀ o g, Fintype (I o g)] [∀ o g, Fintype (J o g)]
      (X : ∀ z, RowData C V (N.ordP l) (I z) (J z)) (F : ∀ z, Flag (X z)),
    (∀ z ∈ Z, (X z).Alt ∧ (X z).n = N.R.k - 1 ∧ (X z).m = N.R.m) →
    ∀ (ga : RPl N.R → Fin 2 → ZMod (N.ordP l) → ℕ → ℕ) (W exc : RPl N.R → ℕ) (nW : ℕ)
      (T θ rest l1 ν : ℝ) (th : RPl N.R → ℝ),
    WtHyp N l Z bg (fun z => (X z).rk) ga W exc rest → 4 * N.R.r * N.R.f ≤ nW →
    DegHyp N j W T θ rest C1 th → ValBlocks X F Z nW ga ν → (l : ℝ) < l1 →
      T * ν ≤ N.FInert j l + errC N j l Cc T l1 ∧
      (l ≠ N.g 0 → l ≠ N.g 1 → (l : ℝ) ≤ N.sc.X'' N.R.n → T * ν ≤ N.FjP j l + errC N j l Cc T l1) ∧
      ((∀ z z', N.w j z' ≤ l * N.w j z) →
        T * ν ≤ ((N.R.k : ℝ) - 1) * (∑ z, N.w j z) / ((l : ℝ) ^ 2 - 1) + errC N j l Cc T l1)

def Content : Prop := ∀ C1 : ℝ, 0 ≤ C1 → ∃ Cc : ℝ, 0 < Cc ∧ ContentAt C1 Cc

def ContentFromSupplies : Prop := BiSupply → CHSupply → MONSupply → ContentInert → Content

def ContentLargeIAt (C1 Cc : ℝ) : Prop :=
  ∀ (N : NumDatum) (j l : ℕ) (Z : Finset (RPl N.R)), l.Prime → 5 ≤ l → IsReps N l Z →
    (N.cls l = PrimeClass.inertClass ∨ N.cls l = PrimeClass.signal) →
    ¬ (N.cls l = PrimeClass.inertClass ∧ N.hP l = 0) →
    2 * (N.R.k - 1) + 2 < l → (N.R.k : ℝ) ^ ((3 : ℝ) / 2) < (l : ℝ) ^ 3 →
    ∀ (C : Type) [Field C] (V : VF C), V.l = l →
    ∀ (I J : RPl N.R → Fin 2 → Type) [∀ o g, Fintype (I o g)] [∀ o g, Fintype (J o g)]
      (X : ∀ z, RowData C V (N.ordP l) (I z) (J z)) (F : ∀ z, Flag (X z)),
    (∀ z ∈ Z, (X z).Alt ∧ (X z).n = N.R.k - 1 ∧ (X z).m = N.R.m) →
    ∀ (ga : RPl N.R → Fin 2 → ZMod (N.ordP l) → ℕ → ℕ) (W exc : RPl N.R → ℕ) (nW : ℕ)
      (T θ rest l1 ν : ℝ) (th : RPl N.R → ℝ),
    WtHyp N l Z bg (fun z => (X z).rk) ga W exc rest →
    (∑ z, ((N.R.k : ℝ) - 1) * (2 * (W z : ℝ) / (l : ℝ) ^ 2 + 4)) + 2 * (N.R.r : ℝ) * N.R.f ≤ (nW : ℝ) →
    DegHyp N j W T θ rest C1 th → ValBlocks X F Z nW ga ν → l1 ≤ (l : ℝ) →
      T * ν ≤ N.FInert j l + errC N j l Cc T l1 ∧
      (l ≠ N.g 0 → l ≠ N.g 1 → (l : ℝ) ≤ N.sc.X'' N.R.n → T * ν ≤ N.FjP j l + errC N j l Cc T l1) ∧
      ((∀ z z', N.w j z' ≤ l * N.w j z) →
        T * ν ≤ ((N.R.k : ℝ) - 1) * (∑ z, N.w j z) / ((l : ℝ) ^ 2 - 1) + errC N j l Cc T l1)

def ContentLargeI : Prop := ∀ C1 : ℝ, 0 ≤ C1 → ∃ Cc : ℝ, 0 < Cc ∧ ContentLargeIAt C1 Cc

def ContentLargeFromSupplies : Prop := UBSupply → CHSupply → MONSupply → ContentLarge → ContentLargeI

def ContentSplitAt : Prop :=
  ∀ (N : NumDatum) (j l : ℕ) (Z : Finset (RPl N.R)), l.Prime → IsReps N l Z →
    N.cls l = PrimeClass.splitK →
    ∀ (C : Type) [Field C] (V : VF C), V.l = l →
    ∀ (I J : RPl N.R → Fin 2 → Type) [∀ o g, Fintype (I o g)] [∀ o g, Fintype (J o g)]
      (X : ∀ z, RowData C V (N.ordP l) (I z) (J z)) (F : ∀ z, Flag (X z)),
    (∀ z ∈ Z, (∀ a, (X z).big 0 a) ∧ (X z).n = N.R.k - 1 ∧ (X z).m = N.R.m) →
    ∀ (ga : RPl N.R → Fin 2 → ZMod (N.ordP l) → ℕ → ℕ) (W exc : RPl N.R → ℕ) (nW : ℕ)
      (T θ rest C1 ν : ℝ) (th : RPl N.R → ℝ),
    WtHyp N l Z (fun _ => 0) (fun z => (X z).rk) ga W exc rest → 4 * N.R.r * N.R.f ≤ nW →
    DegHyp N j W T θ rest C1 th → ValBlocks X F Z nW ga ν →
      T * ν ≤ (N.R.m * (∑ z, N.w j z) + C1 * (N.R.f * N.R.k * (N.Sc + N.eta))) / ((l : ℝ) - 1)

def ContentZeroAt : Prop :=
  ∀ (C : Type) [Field C] (V : VF C) (d : ℕ) [NeZero d] (Orb : Type) [Fintype Orb]
    (I J : Orb → Fin 2 → Type) [∀ o g, Fintype (I o g)] [∀ o g, Fintype (J o g)]
    (X : ∀ o, RowData C V d (I o) (J o)) (F : ∀ o, Flag (X o)) (Z : Finset Orb)
    (ga : Orb → Fin 2 → ZMod d → ℕ → ℕ) (K nW : ℕ) (ν : ℝ),
    (∀ z ∈ Z, ∀ g a k, ga z g a k ≠ 0 → 1 ≤ k ∧ k ≤ (X z).rk g a ∧ k ≤ K) →
    2 * K * Z.card ≤ nW →
    (∑ z ∈ Z, totDeg (ga z) K) < V.l → ValBlocks X F Z nW ga ν → ν ≤ 0

end Formalism.L2.FormalSeriesBounds
