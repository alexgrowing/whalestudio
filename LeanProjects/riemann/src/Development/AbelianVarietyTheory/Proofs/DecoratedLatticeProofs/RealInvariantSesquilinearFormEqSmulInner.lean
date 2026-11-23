import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PrinInf
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TransferOn
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ParamsEx
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdjFormula
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicUnitaryEqRealMulFiniteSplit
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HeckeLPartialContinuationHolds

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift GlobalTheory.Core.Rk.Exh

namespace GlobalTheory.CoefRealSchur

theorem scalar_of_comm {W : Type} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] [Nontrivial W]
    (P : Module.End ℂ W → Prop) (hirr : ∀ U : Submodule ℂ W, (∀ a, P a → U.map a ≤ U) → U = ⊥ ∨ U = ⊤)
    (T₀ : Module.End ℂ W) (hT : ∀ a, P a → a * T₀ = T₀ * a) : ∃ c : ℂ, T₀ = c • 1 := by
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue T₀
  refine ⟨c, ?_⟩
  have hU : ∀ a, P a → (T₀.eigenspace c).map a ≤ T₀.eigenspace c := by
    intro a ha
    rintro _ ⟨v, hv, rfl⟩
    rw [SetLike.mem_coe, Module.End.mem_eigenspace_iff] at hv
    rw [Module.End.mem_eigenspace_iff, ← Module.End.mul_apply, ← hT a ha, Module.End.mul_apply, hv, map_smul]
  rcases hirr _ hU with h | h
  · exact absurd h (Module.End.hasEigenvalue_iff.1 hc)
  · refine LinearMap.ext fun v => ?_
    have hv : v ∈ T₀.eigenspace c := h ▸ Submodule.mem_top
    rw [Module.End.mem_eigenspace_iff] at hv
    rw [hv]
    rfl

def repOp {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
    (B : W →ₗ⋆[ℂ] W →ₗ[ℂ] ℂ) : Module.End ℂ W where
  toFun x := (InnerProductSpace.toDual ℂ W).symm (LinearMap.toContinuousLinearMap (B x))
  map_add' x x' := by
    apply ext_inner_right ℂ
    intro w
    simp [InnerProductSpace.toDual_symm_apply, inner_add_left]
  map_smul' a x := by
    apply ext_inner_right ℂ
    intro w
    simp [InnerProductSpace.toDual_symm_apply, inner_smul_left]

theorem inner_repOp {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
    (B : W →ₗ⋆[ℂ] W →ₗ[ℂ] ℂ) (x y : W) : ⟪repOp B x, y⟫_ℂ = B x y := by
  simp [repOp, InnerProductSpace.toDual_symm_apply]

theorem form_eq_smul_inner : ∀ (D : D7) (V : HSp D) (c : CoefA V), c.Is → ∀ (B : c.W →ₗ⋆[ℂ] c.W →ₗ[ℂ] ℂ), (∀ u ∈ GinfC V, ∀ x y, B (c.ρ u x) (c.ρ u y) = B x y) → ∃ z : ℂ, ∀ x y, B x y = z * ⟪x, y⟫_ℂ := by
  intro D V c hc B hB
  have hirr : ∀ U : Submodule ℂ c.W, (∀ a, (∃ u ∈ GinfC V, c.ρ u = a) → U.map a ≤ U) → U = ⊥ ∨ U = ⊤ := by
    intro U hU
    refine hc.2.2.2.2 U fun h => ?_
    obtain ⟨a, ha, k, hk, rfl⟩ := (GlobalTheory.UnitarySplit.real_finite_split D V).1 h
    rw [map_mul, hc.1 k hk, mul_one]
    exact hU _ ⟨a, ha, rfl⟩
  haveI := hc.2.2.2.1
  have hcomm : ∀ a, (∃ u ∈ GinfC V, c.ρ u = a) → a * repOp B = repOp B * a := by
    rintro _ ⟨u, hu, rfl⟩
    apply LinearMap.ext
    intro x
    apply ext_inner_right ℂ
    intro y
    obtain ⟨y', rfl⟩ : ∃ y', y = c.ρ u y' :=
      ⟨c.ρ u⁻¹ y, by rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]⟩
    rw [Module.End.mul_apply, Module.End.mul_apply, hc.2.1, inner_repOp, inner_repOp, hB u hu]
  obtain ⟨z, hz⟩ := scalar_of_comm _ hirr (repOp B) hcomm
  refine ⟨starRingEnd ℂ z, fun x y => ?_⟩
  rw [← inner_repOp B x y, hz, LinearMap.smul_apply, Module.End.one_apply, inner_smul_left]

end GlobalTheory.CoefRealSchur
