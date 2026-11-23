import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinTwoHomsERegularAssociatedStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinNormEisensteinLeRadiusStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem norm_toDisc_add_le_max (l : ℕ) {A : Type} [CommRing A] (u : A) (ρ : ℝ≥0) (a b : A) :
    ‖toDisc l u ρ (a + b)‖ ≤ max ‖toDisc l u ρ a‖ ‖toDisc l u ρ b‖ := by
  have h1 : ∀ c, ‖toDisc l u ρ c‖ = gauge l u ρ (algebraMap A (PreDisc l u ρ) c) := fun c => norm_ofPre l u ρ _
  rewrite [h1, h1, h1, map_add]
  exact gauge_add_le_max l u ρ _ _

theorem norm_hf_g_X_and_φ_le : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (B : Obj l ↥(OL K)) (f g : Hom bk.prism B), ‖toDisc l (BK.hf f X) bk.ρ₀ (BK.hf g X)‖ ≤ bk.ρ₀ ∧ ‖toDisc l (BK.hf f X) bk.ρ₀ (B.D.φ (BK.hf f X))‖ ≤ bk.ρ₀ := by
  intro l _ K bk B f g
  obtain ⟨hρ0, hρ1, hlρ, hE⟩ := GlobalTheory.T.breuilKisin_norm_eisenstein_le_radius l K bk B.A (BK.hf f)
  have hd := (GlobalTheory.T.breuilKisin_two_homs_E_regular_associated l K bk B f g).2.2
  have h : ‖toDisc l (BK.hf f X) bk.ρ₀ (BK.hf f X ^ 1)‖ ≤ (bk.ρ₀ : ℝ) ^ 1 := norm_toDisc_pow_le 1 hρ0
  have hX : ‖toDisc l (BK.hf f X) bk.ρ₀ (BK.hf f X)‖ ≤ bk.ρ₀ := by simpa only [pow_one] using h
  have key : ∀ a b : B.A, ‖toDisc l (BK.hf f X) bk.ρ₀ (a + b)‖ ≤
      max ‖toDisc l (BK.hf f X) bk.ρ₀ a‖ ‖toDisc l (BK.hf f X) bk.ρ₀ b‖ :=
    norm_toDisc_add_le_max l (BK.hf f X) bk.ρ₀
  refine ⟨?_, ?_⟩
  · obtain ⟨w, hw⟩ := hd
    have e : BK.hf g X = BK.hf f X + BK.hf f bk.E * w := eq_add_of_sub_eq' hw
    rewrite [e]
    refine (key _ _).trans (max_le hX ?_)
    rewrite [map_mul]
    refine (norm_mul_le _ _).trans ?_
    calc ‖toDisc l (BK.hf f X) bk.ρ₀ (BK.hf f bk.E)‖ * ‖toDisc l (BK.hf f X) bk.ρ₀ w‖
        ≤ (l : ℝ)⁻¹ * 1 := mul_le_mul hE (norm_toDisc_le w) (norm_nonneg _) (by positivity)
      _ ≤ bk.ρ₀ := (mul_one _).trans_le hlρ
  · have e1 : B.D.φ (BK.hf f X) = BK.hf f (frobS l bk.a X) :=
      (Hom.f_φ f (show bk.prism.A from X)).symm
    have e : B.D.φ (BK.hf f X) = BK.hf f X ^ l := by
      rw [e1, frobS_X, map_pow]
    refine (congrArg (fun y => ‖toDisc l (BK.hf f X) bk.ρ₀ y‖) e).trans_le ((norm_toDisc_pow_le l hρ0).trans ?_)
    exact pow_le_of_le_one (by positivity) (by exact_mod_cast hρ1.le) (Fact.out : l.Prime).ne_zero

end GlobalTheory.BSP
