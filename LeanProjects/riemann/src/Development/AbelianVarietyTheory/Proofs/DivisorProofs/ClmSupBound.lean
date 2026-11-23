import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasTemperateGrowthElim

open GlobalTheory.SliceSchwartz
open scoped ContDiff

noncomputable section

namespace GlobalTheory.SliceOp

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]

def padL {κ κ' : Type} (h : κ → V) : κ ⊕ κ' → V := Sum.elim h 0

def qOp {κ κ' κ₁' : Type} [Fintype κ] [Fintype κ'] [Fintype κ₁']
    (P : SchwartzMap (κ' → V) ℂ →L[ℂ] SchwartzMap (κ₁' → V) ℂ) (f : SchwartzMap (κ ⊕ κ' → V) ℂ)
    (s : κ ⊕ κ₁' → V) : ℂ :=
  P (sliceR f (s ∘ Sum.inl)) (s ∘ Sum.inr)

abbrev pd {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] (w : X) :
    SchwartzMap X ℂ →L[ℂ] SchwartzMap X ℂ :=
  LineDeriv.lineDerivOpCLM ℂ (SchwartzMap X ℂ) w

theorem pd_apply {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] (w : X) (f : SchwartzMap X ℂ) (x : X) :
    pd w f x = fderiv ℝ f x w := by
  simp [pd, LineDeriv.lineDerivOpCLM_apply, SchwartzMap.lineDerivOp_apply_eq_fderiv]

theorem clm_sup_bound {X Y : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (T : SchwartzMap X ℂ →L[ℂ] SchwartzMap Y ℂ) (s : Finset (ℕ × ℕ)) :
    ∃ (s' : Finset (ℕ × ℕ)) (C : ℝ), 0 ≤ C ∧ ∀ f : SchwartzMap X ℂ,
      s.sup (schwartzSeminormFamily ℂ Y ℂ) (T f) ≤ C * s'.sup (schwartzSeminormFamily ℂ X ℂ) f := by
  have hp : Continuous ((s.sup (schwartzSeminormFamily ℂ Y ℂ)).comp T.toLinearMap) :=
    (Seminorm.continuous_finsetSup fun i _ => (schwartz_withSeminorms ℂ Y ℂ).continuous_seminorm i).comp
      T.continuous
  obtain ⟨s', C, -, hC⟩ := Seminorm.bound_of_continuous (schwartz_withSeminorms ℂ X ℂ) _ hp
  refine ⟨s', C, C.2, fun f => ?_⟩
  have := hC f
  simpa [Seminorm.smul_apply, NNReal.smul_def] using this

end GlobalTheory.SliceOp
