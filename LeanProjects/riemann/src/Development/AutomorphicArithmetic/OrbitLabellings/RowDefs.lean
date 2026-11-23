import Mathlib
import Formalism.LocalToGlobal.CharacterGerms.RestNonneg
import Formalism.LocalToGlobal.CharacterGerms.BlockMembershipSelfConjugate

noncomputable section

open scoped BigOperators
open Classical
open Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.FormalSeriesBounds.RF

namespace UpperTheory.G2

section Blocks

variable {C : Type} [Field C] {V : VF C} {d : ℕ} [NeZero d] {Orb : Type} [Fintype Orb] {I J : Orb → Fin 2 → Type}
  [∀ o g, Fintype (I o g)] [∀ o g, Fintype (J o g)]

def OneType (L : Orb → List (RF.GlobalTheory d × ℝ)) : Prop :=
  ∀ o, ∀ q ∈ L o, ∀ g e N, q.1 = RF.GlobalTheory.mon g e N → ∃ s : ZMod d, ∀ a k, a ≠ s → e a k = 0

def WtSum (hd : ZMod d) (X : ∀ o, RowData C V d (I o) (J o)) (ga : Orb → ZMod d → ℕ → ℕ) (L : Orb → List (RF.GlobalTheory d × ℝ)) : Prop :=
  ∀ o s k, ((L o).map fun q => q.1.wt (X o) 0 s k + q.1.wt (X o) 1 (s + hd) k).sum = ga o s k

def ValBlocksS (hd : ZMod d) (X : ∀ o, RowData C V d (I o) (J o)) (F : ∀ o, RF.Flag (X o)) (nW : ℕ)
    (ga : Orb → ZMod d → ℕ → ℕ) (ν : ℝ) : Prop :=
  ∀ L : Orb → List (RF.GlobalTheory d × ℝ), (∀ o, ∀ q ∈ L o, q.1.Attains (X o) (F o) q.2) → OneType L →
    2 * (∑ o, ((L o).map fun q => q.1.what₂ (X o).n).sum) ≤ nW → WtSum hd X ga L → ν ≤ ∑ o, ((L o).map Prod.snd).sum

def PlaneBlockProductsMemFamily (hd : ZMod d) (X : ∀ o, RowData C V d (I o) (J o)) (n : ℕ) (F : ∀ o, RF.Flag (X o))
    (FFimg : Set (∀ o, MvPolynomial (Fin n × WV (I o)) C)) (ga : Orb → ZMod d → ℕ → ℕ) : Prop :=
  ∀ L : Orb → List (RF.GlobalTheory d × ℝ), OneType L → WtSum hd X ga L → RF.ProdMem X n F FFimg L

end Blocks

def WtTieS {T Orb : Type} {d : ℕ} (r : T → ℕ) (tau : Orb → ZMod d → T) (ga : Orb → ZMod d → ℕ → ℕ) (a : T → ℕ → ℕ) : Prop :=
  (∀ o s (i : ℕ), i < r (tau o s) → a (tau o s) i = ∑ k ∈ Finset.Icc (i + 1) (r (tau o s)), ga o s k) ∧
  ∀ σ, (∀ o s, tau o s ≠ σ) → ∀ i, i < r σ → a σ i = 0

structure RowFamS (P : RF.Par) (l : ℕ) (Z : Finset P.Pl) : Type 1 where
  C : Type
  [fC : Field C]
  V : VF C
  hVl : V.l = l
  I : {z // z ∈ Z} → Fin 2 → Type
  J : {z // z ∈ Z} → Fin 2 → Type
  [fI : ∀ o g, Fintype (I o g)]
  [fJ : ∀ o g, Fintype (J o g)]
  X : ∀ o, RowData C V (2 * P.d) (I o) (J o)
  F : ∀ o, RF.Flag (X o)
  hn : ∀ o, (X o).n = P.k - 1 ∧ (X o).m = P.m
  alt : ∀ o, (X o).Alt

attribute [instance] RowFamS.fC RowFamS.fI RowFamS.fJ

structure PkgCs (P : RF.Par) (l : ℕ) (C1 : ℝ) : Type 1 where
  odd : Odd P.d
  Z : Finset P.Pl
  hZ : RF.IsReps P Z
  R : RowFamS P l Z
  ga : {z // z ∈ Z} → ZMod (2 * P.d) → ℕ → ℕ
  W : P.Pl → ℕ
  nW : ℕ
  T : ℝ
  θ0 : ℝ
  rest : ℝ
  ν : ℝ
  supp : ∀ o s k, ga o s k ≠ 0 → 1 ≤ k ∧ k ≤ (R.X o).rkF 0 s
  main : ∀ o (s : ZMod (2 * P.d)), Even s.val → ga o s (P.k - 1) = W (P.pos o.1 (s.val % P.d))
  rest_eq : rest = ∑ o, ∑ s : ZMod (2 * P.d), ∑ k ∈ Finset.Icc 1 P.r,
    (if Even s.val ∧ k = P.k - 1 then (0 : ℝ) else (k : ℝ) * ga o s k)
  what₂ : P.f * ((RF.i0 P.k l + 1) * (P.k - 1) + 4 * P.r) ≤ nW
  deg : RF.DegHyp2 P W T θ0 rest C1
  val : ValBlocksS (P.d : ZMod (2 * P.d)) R.X R.F nW ga ν

structure PkgZeroCs (P : RF.Par) (l : ℕ) : Type 1 where
  Z : Finset P.Pl
  R : RowFamS P l Z
  ga : {z // z ∈ Z} → ZMod (2 * P.d) → ℕ → ℕ
  K : ℕ
  s : ℕ
  nW : ℕ
  T : ℝ
  ν : ℝ
  T_one : 1 ≤ T
  w_nonneg : ∀ z, 0 ≤ P.w z
  supp : ∀ o σ k, ga o σ k ≠ 0 → 1 ≤ k ∧ k ≤ (R.X o).rkF 0 σ ∧ k ≤ K
  first : ∀ o σ, ∑ k ∈ Finset.Icc 1 K, ga o σ k ≤ s * (l - 1)
  what₂ : 4 * K * s * (Z.card * P.d) ≤ nW
  val : ValBlocksS (P.d : ZMod (2 * P.d)) R.X R.F nW ga ν

end UpperTheory.G2

end
