import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.HeckeLAdicCharacterDeRham
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.DeRhamJacobian.IsdRJ
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HasPeriods
import Development.WeilBound.CoreStatements.PlaceConnectedComponents.IsOpenQuotientMapArt0
import GroundTheory.LocalFields.ConductorReciprocity
import GroundTheory.LocalFields.KroneckerWeber
import GroundTheory.PAdicHodge.FieldOfNormsCyclBase
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DenseRangeUnits
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GlobalArtinLocalIdeleInjective
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ChevalleyUnits
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge
open scoped Classical
open ValuativeRel GroundTheory.LocalField GroundTheory.LocalField.FormalGroup
open scoped GroundTheory.PAdicHodge.CyclNorms

namespace GlobalTheory.CompanionTheory.LocalNorm

theorem tendsto_pow_zero_of_val_lt_one {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] {x : F} (hx : valuation F x < 1) :
    Filter.Tendsto (fun n : ℕ => x ^ n) Filter.atTop (nhds 0) := by
  intro s hs
  obtain ⟨γ, hγ⟩ := (IsValuativeTopology.mem_nhds_zero_iff s).1 hs
  obtain ⟨n, hn⟩ := exists_pow_lt₀ hx γ
  refine Filter.mem_atTop_sets.2 ⟨n, fun m hm => hγ ?_⟩
  show valuation F (x ^ m) < γ
  rw [map_pow]
  exact lt_of_le_of_lt (pow_le_pow_right_of_le_one' hx.le hm) hn

private theorem norm_lt_one_of_valuation_lt_one' {l : ℕ} [Fact l.Prime] {F : Type} [Field F] [ValuativeRel F]
    [TopologicalSpace F] [IsNonarchimedeanLocalField F] (φ : F →+* Om l) (hφ : Continuous φ)
    {c : F} (hc : valuation F c < 1) : ‖φ c‖ < 1 := by
  have h1 : Filter.Tendsto (fun n : ℕ => φ c ^ n) Filter.atTop (nhds 0) := by
    have h2 := ((hφ.tendsto 0).comp (tendsto_pow_zero_of_val_lt_one hc))
    simpa [Function.comp_def, map_pow, map_zero] using h2
  exact tendsto_pow_atTop_nhds_zero_iff_norm_lt_one.1 h1

theorem norm_le_one_of_val_le_one {l : ℕ} [Fact l.Prime] {F : Type} [Field F] [ValuativeRel F]
    [TopologicalSpace F] [IsNonarchimedeanLocalField F] (φ : F →+* Om l) (hφ : Continuous φ)
    {c : F} (hc : valuation F c ≤ 1) : ‖φ c‖ ≤ 1 := by
  obtain ⟨p, hp, hp1⟩ := (Valuation.IsNontrivial.exists_lt_one (v := valuation F))
  have hpos : 0 < ‖φ p‖ := norm_pos_iff.2 ((map_ne_zero φ).2 hp)
  have key : ∀ n : ℕ, ‖φ p‖ * ‖φ c‖ ^ n < 1 := by
    intro n
    have hv : valuation F (p * c ^ n) < 1 := by
      rw [map_mul, map_pow]
      exact lt_of_le_of_lt (mul_le_of_le_one_right' (pow_le_one' hc n)) hp1
    have h3 := norm_lt_one_of_valuation_lt_one' φ hφ hv
    rwa [map_mul, map_pow, norm_mul, norm_pow] at h3
  refine not_lt.1 fun h => ?_
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (‖φ p‖⁻¹) h
  have h4 := mul_lt_mul_of_pos_left hn hpos
  rw [mul_inv_cancel₀ hpos.ne'] at h4
  exact lt_asymm h4 (key n)

theorem one_lt_norm_of_one_lt_val {l : ℕ} [Fact l.Prime] {F : Type} [Field F] [ValuativeRel F]
    [TopologicalSpace F] [IsNonarchimedeanLocalField F] (φ : F →+* Om l) (hφ : Continuous φ)
    {c : F} (hc : 1 < valuation F c) : 1 < ‖φ c‖ := by
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [map_zero] at hc
    exact not_lt_zero hc
  have h1 : valuation F c⁻¹ < 1 := by
    rw [Valuation.map_inv]
    exact inv_lt_one_of_one_lt₀ hc
  have h2 := norm_lt_one_of_valuation_lt_one' φ hφ h1
  rw [map_inv₀, norm_inv] at h2
  have hpos : 0 < ‖φ c‖ := norm_pos_iff.2 ((map_ne_zero φ).2 hc0)
  exact (inv_lt_one₀ hpos).1 h2

end GlobalTheory.CompanionTheory.LocalNorm

theorem GlobalTheory.CompanionTheory.LocalNorm.vle_iff_norm_le : ∀ {l : ℕ} [Fact l.Prime] {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (φ : F →+* Om l), Continuous φ → ∀ a b : F, a ≤ᵥ b ↔ ‖φ a‖ ≤ ‖φ b‖ := by
  intro l _ F _ _ _ _ φ hφ a b
  rw [Valuation.Compatible.vle_iff_le (v := valuation F) a b]
  by_cases hb : b = 0
  · subst hb
    simp
  · have hbn : 0 < ‖φ b‖ := norm_pos_iff.2 ((map_ne_zero φ).2 hb)
    have hvb : 0 < valuation F b := by
      rw [zero_lt_iff]
      exact (Valuation.ne_zero_iff _).2 hb
    constructor
    · intro h
      have hv : valuation F (a / b) ≤ 1 := by
        rw [map_div₀]
        exact (div_le_one₀ hvb).2 h
      have h3 := GlobalTheory.CompanionTheory.LocalNorm.norm_le_one_of_val_le_one φ hφ hv
      rwa [map_div₀, norm_div, div_le_one hbn] at h3
    · intro h
      refine not_lt.1 fun h' => ?_
      have hv : 1 < valuation F (a / b) := by
        rw [map_div₀]
        exact (one_lt_div₀ hvb).2 h'
      have h3 := GlobalTheory.CompanionTheory.LocalNorm.one_lt_norm_of_one_lt_val φ hφ hv
      rw [map_div₀, norm_div, one_lt_div hbn] at h3
      exact absurd h (not_le.2 h3)
