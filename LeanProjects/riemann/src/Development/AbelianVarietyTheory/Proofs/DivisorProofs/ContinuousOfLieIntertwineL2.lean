import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedSpaceVecPairAsAdeles
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IteratedLineDerivMemWeylAlg

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField MeasureTheory
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix ENNReal Classical
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.RealWeil

theorem exists_weylAlg_conj {l : Type} [Fintype l] (L' : (l ⊕ l → ℝ) ≃ₗ[ℝ] (l ⊕ l → ℝ))
    (A' : Sch l →ₗ[ℂ] Sch l) (hI : ∀ w f, A' (dRho w f) = dRho (L' w) (A' f))
    {B : Sch l →L[ℂ] Sch l} (hB : B ∈ weylAlg l) :
    ∃ B' : Sch l →L[ℂ] Sch l, ∀ f, B (A' f) = A' (B' f) := by
  refine weylAlg_induction (P := fun B => ∃ B' : Sch l →L[ℂ] Sch l, ∀ f, B (A' f) = A' (B' f))
    ⟨1, fun f => by simp⟩ ?_ ⟨0, fun f => by simp⟩ ?_ ?_ hB
  · rintro A w ⟨B', h⟩
    refine ⟨B' * dRho (L'.symm w), fun f => ?_⟩
    have e := hI (L'.symm w) f
    rw [LinearEquiv.apply_symm_apply] at e
    rw [ContinuousLinearMap.mul_apply, ContinuousLinearMap.mul_apply, ← e, h]
  · rintro A B ⟨A₁, h₁⟩ ⟨B₁, h₂⟩
    exact ⟨A₁ + B₁, fun f => by simp [h₁, h₂]⟩
  · rintro c A ⟨A₁, h⟩
    exact ⟨c • A₁, fun f => by simp [h]⟩

theorem norm_toLp_le_of_lintegral_le {l : Type} [Fintype l] (A' : Sch l →ₗ[ℂ] Sch l) (C : ℝ≥0∞) (hC : C ≠ ⊤)
    (h : ∀ f, ∫⁻ x, ‖A' f x‖ₑ ^ 2 ≤ C * ∫⁻ x, ‖f x‖ₑ ^ 2) (f : Sch l) :
    ‖(A' f).toLp 2 volume‖ ≤ C.toReal ^ (1 / 2 : ℝ) * ‖f.toLp 2 volume‖ := by
  rw [SchwartzMap.norm_toLp, SchwartzMap.norm_toLp, ENNReal.toReal_rpow, ← ENNReal.toReal_mul]
  refine ENNReal.toReal_mono (ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg (by norm_num) hC)
    (f.eLpNorm_lt_top 2 volume).ne) ?_
  rw [eLpNorm_eq_lintegral_rpow_enorm (by norm_num) (by norm_num),
    eLpNorm_eq_lintegral_rpow_enorm (by norm_num) (by norm_num)]
  simp only [ENNReal.toReal_ofNat, ENNReal.rpow_two]
  rw [← ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
  exact ENNReal.rpow_le_rpow (h f) (by norm_num)

end GlobalTheory.RealWeil

theorem GlobalTheory.RealWeil.continuous_of_dRho_intertwine_of_L2_bound : ∀ (l : Type) [Fintype l] (L' : (l ⊕ l → ℝ) ≃ₗ[ℝ] (l ⊕ l → ℝ))
    (A' : GlobalTheory.RealWeil.Sch l →ₗ[ℂ] GlobalTheory.RealWeil.Sch l) (C : ℝ≥0∞), C ≠ ⊤ →
    (∀ f, ∫⁻ x, ‖A' f x‖ₑ ^ 2 ≤ C * ∫⁻ x, ‖f x‖ₑ ^ 2) →
    (∀ w f, A' (GlobalTheory.RealWeil.dRho w f) = GlobalTheory.RealWeil.dRho (L' w) (A' f)) →
    Continuous A' := by
  intro l _ L' A' C hC h2 hI
  refine WithSeminorms.continuous_of_continuous_comp (schwartz_withSeminorms ℂ (EuclideanSpace ℝ l) ℂ) A'
    fun i => ?_
  obtain ⟨B, hB, hle⟩ := GlobalTheory.RealWeil.exists_seminorm_le (l := l) i.1 i.2
  choose B' hB' using fun r => GlobalTheory.RealWeil.exists_weylAlg_conj L' A' hI (hB r)
  let c : NNReal := Real.toNNReal (C.toReal ^ (1 / 2 : ℝ))
  let q : Seminorm ℂ (GlobalTheory.RealWeil.Sch l) := ∑ r, c • (normSeminorm ℂ (GlobalTheory.RealWeil.L2 l)).comp
    ((GlobalTheory.RealWeil.schwartzToL2 l).comp (B' r)).toLinearMap
  refine Seminorm.continuous_of_le (q := q) (Seminorm.continuous_finsetSum fun r _ => ?_) fun f => ?_
  · change Continuous fun f => (c : ℝ) * ‖(GlobalTheory.RealWeil.schwartzToL2 l) (B' r f)‖
    exact continuous_const.mul (continuous_norm.comp ((GlobalTheory.RealWeil.schwartzToL2 l).comp (B' r)).continuous)
  · have e : q f = ∑ r, (c : ℝ) * ‖(B' r f).toLp 2 volume‖ := by
      simp [q, GlobalTheory.RealWeil.schwartzToL2_apply, NNReal.smul_def, smul_eq_mul]
    rw [e]
    change SchwartzMap.seminorm ℂ i.1 i.2 (A' f) ≤ _
    refine (hle (A' f)).trans (Finset.sum_le_sum fun r _ => ?_)
    rw [hB']
    refine (GlobalTheory.RealWeil.norm_toLp_le_of_lintegral_le A' C hC h2 _).trans (le_of_eq ?_)
    rw [show (c : ℝ) = C.toReal ^ (1 / 2 : ℝ) from Real.coe_toNNReal _ (Real.rpow_nonneg ENNReal.toReal_nonneg _)]

end
