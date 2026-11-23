import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsStepVecOfIff
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WittHyperbolicRankZeroProjMulEmb

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl ValuativeRel IsLocalRing
open GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.StepData (XIx Ix latOf box LatFrame)
open GlobalTheory.LocMod (GAt PinGBy ofSplit MovedTo)
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (CharUnramAt)
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastPair lastKer)
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedLocalFrameSequences (IsFockOver StepsAll vec atW IsMoved InAt InvOnUnits IsBesFrame IsJacFrame FrameMapsPrefix jacLat ptBF ptFB)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RouteCompare
open GlobalTheory.Mem.Isom

namespace GlobalTheory.OverTgt

variable {D : D7}

def colRow (S T : HSp D) (r : Fin S.rank → AE D) : (Fin T.rank → AE D) →+ WO S T where
  toFun y := Matrix.of fun i j => y i * r j
  map_zero' := by ext i j; simp
  map_add' y y' := by ext i j; simp [add_mul]

theorem mul_colRow {S T T' : HSp D} (M : Mx D T'.rank T.rank) (r : Fin S.rank → AE D) (y : Fin T.rank → AE D) :
    HMul.hMul M (colRow S T r y) = colRow S T' r (M *ᵥ y) := by
  ext i j
  simp [colRow, Matrix.mul_apply, Matrix.mulVec, dotProduct, Finset.sum_mul, mul_assoc]

theorem gen_eq_colRow {S T : HSp D} (α : AF D.host.F) (a : D.host.E) (s : Fin S.rank → D.host.E) (t : Fin T.rank → D.host.E) :
    (Matrix.of fun i j => α ⊗ₜ[D.host.F] (a * t i * ∑ k, star (s k) * S.gram k j) : WO S T) =
      colRow S T (fun j => incA D (a * ∑ k, star (s k) * S.gram k j)) (fun i => α ⊗ₜ[D.host.F] (1 * t i)) := by
  ext i j
  simp only [colRow, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Matrix.of_apply]
  change _ = (α ⊗ₜ[D.host.F] (1 * t i)) * ((1 : AF D.host.F) ⊗ₜ[D.host.F] _)
  rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one]
  congr 1
  ring

theorem colRow_mem_latO {S T : HSp D} {LS : Set (Fin S.rank → D.host.E)} {LT : Lat T} {P : GlobalTheory.FinPl.Pl D → Prop}
    {a : D.host.E} (ha : a ∈ D.host.AA) {s : Fin S.rank → D.host.E} (hs : s ∈ LS) {y : Fin T.rank → AE D}
    (hy : y ∈ latV T LT P) :
    colRow S T (fun j => incA D (a * ∑ k, star (s k) * S.gram k j)) y ∈ latO S T LS (LT : Set _) P := by
  induction hy using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨β, hβi, hβ, c, hc, x, hx, rfl⟩ := hz
    rw [Set.mem_singleton_iff] at hc
    subst hc
    rw [← gen_eq_colRow]
    exact AddSubgroup.subset_closure ⟨β, hβi, hβ, a, ha, s, hs, x, hx, rfl⟩
  | zero => rw [map_zero]; exact zero_mem _
  | add z z' _ _ hz hz' => rw [map_add]; exact add_mem hz hz'
  | neg z _ hz => rw [map_neg]; exact neg_mem hz

theorem mul_mem_latO {S T T' : HSp D} {LS : Set (Fin S.rank → D.host.E)} {LT : Lat T} {LT' : Lat T'}
    {P : GlobalTheory.FinPl.Pl D → Prop} (M : Mx D T'.rank T.rank) (hM : ∀ y ∈ latV T LT P, M *ᵥ y ∈ latV T' LT' P) {w : WO S T}
    (hw : w ∈ latO S T LS (LT : Set _) P) : HMul.hMul M w ∈ latO S T' LS (LT' : Set _) P := by
  induction hw using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨α, hαi, hα, a, ha, s, hs, t, ht, rfl⟩ := hz
    rw [gen_eq_colRow, mul_colRow]
    exact colRow_mem_latO ha hs (hM _ (AddSubgroup.subset_closure ⟨α, hαi, hα, 1, rfl, t, ht, rfl⟩))
  | zero => rw [Matrix.mul_zero]; exact zero_mem _
  | add z z' _ _ hz hz' => rw [Matrix.mul_add]; exact add_mem hz hz'
  | neg z _ hz => rw [Matrix.mul_neg]; exact neg_mem hz

theorem isHalf_mul {m n l : ℕ} {e : AE D} (M : Mx D m l) {u : Mx D l n} (h : IsHalf e u) : IsHalf e (HMul.hMul M u) := by
  intro i j
  simp only [Matrix.mul_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [mul_left_comm, h k j]

section Isometry

variable {V V' : HSp D} (I : IsoMat V V') (S : HSp D)

def conjOp (Tm : (WO S V → ℂ) →ₗ[ℂ] (WO S V → ℂ)) : (WO S V' → ℂ) →ₗ[ℂ] (WO S V' → ℂ) :=
  LinearMap.funLeft ℂ ℂ (I.phi S).symm ∘ₗ Tm ∘ₗ LinearMap.funLeft ℂ ℂ (I.phi S)

variable {Λ : AddSubgroup (WO S V)} {Λ' : AddSubgroup (WO S V')} (hΛ : ∀ u, u ∈ Λ ↔ I.phi S u ∈ Λ')
include hΛ

end Isometry

section Frames

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {p : SplitPt D k}
  {S T T₀ : HSp D} (d : HypDec T T₀ 0) {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']
  (α : GlobalTheory.FinPl.Frame p S n') (β : GlobalTheory.FinPl.Frame p T n) (β₀ : GlobalTheory.FinPl.Frame p T₀ n)

end Frames

end GlobalTheory.OverTgt
