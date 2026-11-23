import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdjFormula
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdjointFormulaOfKernel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchurConstantsExistOnChainOfCuspRapidDecay
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift
open GlobalTheory.AdjUp

noncomputable section

namespace GlobalTheory.AdjUp

theorem ip_eq_mul_integral_val : GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type)
    (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
    (R : RealDat D A Ks) (F : Face D A), Laws R F → ∀ (i : Fin D.R.m) (v : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ),
    IsUnitVec R i v → ∃ P : ℝ, 0 ≤ P ∧ ∀ y z : (R.HW i (sg0 D A)).H,
      ⟪y, z⟫_ℂ = (P : ℂ) * ∫ g in R.fdW i, star (val R i v y g) * val R i v z g ∂(R.νW i) := by
  intro hC D G _ _ Pl0 T A Ks _ _ _ R F hL i v hv
  obtain ⟨-, hr, hip⟩ := hL.models.HW i (sg0 D A)
  have hmem : ∀ x, (R.HW i (sg0 D A)).e x ∈ R.Wall i (sg0 D A) := fun x => hr ▸ LinearMap.mem_range_self _ x
  have hS := (GlobalTheory.Hk3.schurAll_of_cuspRapidDecay hC R).2.2 i

  set Q : ℝ := ∏ ρ, ((dimK _ _ (kapAt (Wc D i) (sg0 D A) ρ) : ℚ) : ℝ) with hQ
  have hQc : (∏ ρ, ((dimK _ _ (kapAt (Wc D i) (sg0 D A) ρ) : ℚ) : ℂ)) = (Q : ℂ) := by
    rw [hQ, Complex.ofReal_prod]; rfl

  have key : ∀ y z : (R.HW i (sg0 D A)).H,
      ⟪y, z⟫_ℂ = (Q : ℂ) * ∫ g in R.fdW i, star (val R i v y g) * val R i v z g ∂(R.νW i) := by
    intro y z
    obtain ⟨c, hc⟩ := hS hL.models.inf (hL.models.νW i).1.1 (hL.models.νW i).2 _ (hmem y) _ (hmem z)
    have hex : ∃ c, IsMultIP (R.MW i (sg0 D A)) (R.νW i) (R.fdW i) ((R.HW i (sg0 D A)).e y)
        ((R.HW i (sg0 D A)).e z) c := ⟨c, hc⟩
    have hv1 := (hex.choose_spec (fun ρ => v ρ) (fun ρ => v ρ)).2
    have hprod : (∏ ρ, ⟪((v ρ : (R.MW i (sg0 D A)).sm ρ) : (R.MW i (sg0 D A)).H ρ),
        ((v ρ : (R.MW i (sg0 D A)).sm ρ) : (R.MW i (sg0 D A)).H ρ)⟫_ℂ) = 1 := by
      refine Finset.prod_eq_one fun ρ _ => ?_
      rw [inner_self_eq_norm_sq_to_K, hv ρ]
      norm_num
    rw [hip, ipAt, hQc, ipM, dif_pos hex]
    unfold val
    rw [hv1, hprod, mul_one]
  by_cases h0 : 0 ≤ Q
  · exact ⟨Q, h0, key⟩
  ·
    refine ⟨0, le_rfl, fun y z => ?_⟩
    have hy : y = 0 := by
      have e1 := key y y
      have hnn : 0 ≤ ∫ g in R.fdW i, ‖val R i v y g‖ ^ 2 ∂(R.νW i) :=
        MeasureTheory.setIntegral_nonneg_of_ae (Filter.Eventually.of_forall fun _ => by positivity)
      have hI : (∫ g in R.fdW i, star (val R i v y g) * val R i v y g ∂(R.νW i)) =
          ((∫ g in R.fdW i, ‖val R i v y g‖ ^ 2 ∂(R.νW i) : ℝ) : ℂ) := by
        rw [← integral_complex_ofReal]
        refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
        simp only
        rw [Complex.ofReal_pow, ← Complex.conj_mul']
        rfl
      rw [hI] at e1
      have e2 : ‖y‖ ^ 2 = Q * ∫ g in R.fdW i, ‖val R i v y g‖ ^ 2 ∂(R.νW i) := by
        have := congrArg Complex.re e1
        rw [inner_self_eq_norm_sq_to_K] at this
        simpa [← Complex.ofReal_pow, Complex.re_ofReal_mul] using this
      have hle : ‖y‖ ^ 2 ≤ 0 := by
        rw [e2]; exact mul_nonpos_of_nonpos_of_nonneg (le_of_lt (not_le.1 h0)) hnn
      have : ‖y‖ = 0 := by nlinarith [norm_nonneg y]
      exact norm_eq_zero.1 this
    rw [hy, inner_zero_left, Complex.ofReal_zero, zero_mul]

end GlobalTheory.AdjUp

end
