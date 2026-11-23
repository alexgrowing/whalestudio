import Mathlib
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LcscAdelicUnitaryGroup
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsLiftAt

open NumberField IsDedekindDomain ReciprocityTheory.Aut Formalism.AUTREP Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2 Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev GlobalTheory.TypeRec GlobalTheory.TypeVec
attribute [local instance] GlobalTheory.TypeRec.factG Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem ringEquiv_symm_continuous_of_continuous {K₁ K₂ : Type*} [NormedField K₁] [NormedField K₂]
    (i : K₁ ≃+* K₂) (hi : Continuous i) (hπ : ∃ π : K₁, 0 < ‖π‖ ∧ ‖π‖ < 1) :
    Continuous i.symm := by

  have small : ∀ δ : ℝ, 0 < δ → ∃ a : K₁, a ≠ 0 ∧ ‖a‖ < δ := by
    intro δ hδ
    obtain ⟨π, hπ0, hπ1⟩ := hπ
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hδ hπ1
    exact ⟨π ^ n, pow_ne_zero _ (norm_pos_iff.mp hπ0), by rwa [norm_pow]⟩

  obtain ⟨δ, hδ, hball⟩ : ∃ δ > 0, ∀ x : K₁, ‖x‖ < δ → ‖i x‖ < 1 := by
    obtain ⟨δ, hδ, h⟩ := Metric.continuous_iff.mp hi 0 1 one_pos
    refine ⟨δ, hδ, fun x hx => ?_⟩
    have := h x (by simpa [dist_eq_norm] using hx)
    simpa [dist_eq_norm] using this

  have key : ∀ y : K₁, ‖i y‖ < 1 → ‖y‖ < 1 := by
    intro y hy
    by_contra hge
    push_neg at hge
    have hy0 : y ≠ 0 := by
      rintro rfl
      norm_num at hge
    have hiy : 0 < ‖i y‖ := norm_pos_iff.mpr ((map_ne_zero i).mpr hy0)
    obtain ⟨a, ha0, ha⟩ := small δ hδ
    have hia : 0 < ‖i a‖ := norm_pos_iff.mpr ((map_ne_zero i).mpr ha0)
    have hgt : 1 < ‖i y‖⁻¹ := (one_lt_inv₀ hiy).mpr hy
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (‖i a‖⁻¹) hgt
    have hsmall : ‖a * y⁻¹ ^ n‖ < δ := by
      rw [norm_mul, norm_pow, norm_inv]
      have h1 : ‖y‖⁻¹ ^ n ≤ 1 := pow_le_one₀ (inv_nonneg.mpr (norm_nonneg _)) (inv_le_one_of_one_le₀ hge)
      calc ‖a‖ * ‖y‖⁻¹ ^ n ≤ ‖a‖ * 1 := by gcongr
        _ < δ := by simpa using ha
    have h2 := hball _ hsmall
    rw [map_mul, map_pow, map_inv₀, norm_mul, norm_pow, norm_inv] at h2
    have h3 : ‖i a‖ * ‖i a‖⁻¹ < ‖i a‖ * ‖i y‖⁻¹ ^ n := mul_lt_mul_of_pos_left hn hia
    rw [mul_inv_cancel₀ hia.ne'] at h3
    linarith

  have zero : ∀ ε > 0, ∃ η > 0, ∀ w : K₂, ‖w‖ < η → ‖i.symm w‖ < ε := by
    intro ε hε
    obtain ⟨a, ha0, ha⟩ := small ε hε
    have ha' : 0 < ‖a‖ := norm_pos_iff.mpr ha0
    have hia : 0 < ‖i a‖ := norm_pos_iff.mpr ((map_ne_zero i).mpr ha0)
    refine ⟨‖i a‖, hia, fun w hw => ?_⟩
    have h1 : ‖i (i.symm w * a⁻¹)‖ < 1 := by
      rw [map_mul, map_inv₀, RingEquiv.apply_symm_apply, norm_mul, norm_inv, mul_inv_lt_iff₀ hia]
      simpa using hw
    have h2 := key _ h1
    rw [norm_mul, norm_inv, mul_inv_lt_iff₀ ha'] at h2
    linarith
  rw [Metric.continuous_iff]
  intro b ε hε
  obtain ⟨η, hη, h⟩ := zero ε hε
  refine ⟨η, hη, fun z hz => ?_⟩
  rw [dist_eq_norm] at hz ⊢
  rw [← map_sub]
  exact h _ hz

theorem GlobalTheory.splitCompletion_symm_continuous : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (s : SplitPlace L) (i : s.v.adicCompletion (maximalRealSubfield L) ≃+* s.w.adicCompletion L), Continuous i → (∀ x : L, i (s.i x) = algebraMap L (s.w.adicCompletion L) x) → Continuous i.symm := by
  intro L _ _ _ s i hi _
  obtain ⟨π, hπ⟩ := s.v.valuation_exists_uniformizer (maximalRealSubfield L)
  have hv : Valued.v (π : s.v.adicCompletion (maximalRealSubfield L)) = WithZero.exp (-1 : ℤ) := by
    simpa using hπ
  refine ringEquiv_symm_continuous_of_continuous i hi ⟨(π : s.v.adicCompletion (maximalRealSubfield L)), ?_, ?_⟩
  · refine norm_pos_iff.mpr fun h => ?_
    rw [h, map_zero] at hv
    exact WithZero.exp_ne_zero hv.symm
  · rw [Valued.toNormedField.norm_lt_one_iff, hv, ← WithZero.exp_zero]
    exact WithZero.exp_lt_exp.mpr (by norm_num)
