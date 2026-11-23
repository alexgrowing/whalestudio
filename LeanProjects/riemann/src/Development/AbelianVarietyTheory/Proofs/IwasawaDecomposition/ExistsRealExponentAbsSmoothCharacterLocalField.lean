import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasNormGroups
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ChevalleyUnits
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StandardCosocleGL
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AlgebraMapIntertwiningMapBijectiveOfIsSmooth
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitarisableSegmentTwistPrecedesAddOneLe
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.LocalLanglandsGL
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.JordanHolderMultiplicityNormalizedBorelJacquetUn
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormalizedAbsCharacterization
import Development.AbelianVarietyTheory.Definitions.Divisors.EqOfHasValueAtInfinite
open NumberField IsDedekindDomain ValuativeRel Matrix MeasureTheory TensorProduct Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.SmoothCharNorm

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem finite_image_units (χ : kˣ →* ℂˣ) (hχ : IsSmoothChar χ) :
    (χ '' {x : kˣ | valuation k (x : k) = 1}).Finite := by
  have hS := GlobalTheory.SmGL.UnramFixed.isCompact_unitsO k
  obtain ⟨t, ht⟩ := hS.elim_finite_subcover
    (fun z : kˣ => (fun y => z⁻¹ * y) ⁻¹' (χ.ker : Set kˣ))
    (fun z => (continuous_const.mul continuous_id).isOpen_preimage _ hχ)
    (fun y _ => Set.mem_iUnion.2 ⟨y, by simp⟩)
  refine (t.finite_toSet.image χ).subset ?_
  rintro _ ⟨y, hy, rfl⟩
  obtain ⟨i, hi, hyi⟩ := Set.mem_iUnion₂.1 (ht hy)
  refine ⟨i, hi, ?_⟩
  have : χ (i⁻¹ * y) = 1 := hyi
  rw [map_mul, map_inv, inv_mul_eq_one] at this
  exact this

theorem norm_eq_one_of_valuation_eq_one (χ : kˣ →* ℂˣ) (hχ : IsSmoothChar χ) (u : kˣ)
    (hu : valuation k (u : k) = 1) : ‖(χ u : ℂ)‖ = 1 := by
  by_contra hne
  have hpos : 0 < ‖(χ u : ℂ)‖ := norm_pos_iff.2 (χ u).ne_zero
  have hinj := pow_right_injective₀ hpos hne
  have hinf := Set.infinite_range_of_injective hinj
  apply hinf
  refine ((finite_image_units χ hχ).image (fun w : ℂˣ => ‖(w : ℂ)‖)).subset ?_
  rintro _ ⟨n, rfl⟩
  refine ⟨χ (u ^ n), ⟨u ^ n, ?_, rfl⟩, ?_⟩
  · simp [Units.val_pow_eq_pow_val, map_pow, hu]
  · simp [map_pow, Units.val_pow_eq_pow_val, norm_pow]

noncomputable def ordHom (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] : kˣ →* Multiplicative ℤ where
  toFun x := Multiplicative.ofAdd (ord k x)
  map_one' := by
    have : ord k (1 : kˣ) = 0 := ord_eq_zero_iff.2 (by simp)
    simp [this]
  map_mul' x y := by simp [ord_mul, ofAdd_add]

theorem ord_zpow (x : kˣ) (n : ℤ) : ord k (x ^ n) = n * ord k x := by
  have := congrArg Multiplicative.toAdd (map_zpow (ordHom k) x n)
  simpa [ordHom, toAdd_zpow, smul_eq_mul] using this

end GlobalTheory.SmoothCharNorm

theorem GlobalTheory.SmoothCharNorm.norm_eq_nabs_rpow : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (χ : kˣ →* ℂˣ), IsSmoothChar χ → ∃ s : ℝ, ∀ z : kˣ, ‖(χ z : ℂ)‖ = nabs k z ^ s := by
  intro k _ _ _ _ χ hχ
  obtain ⟨ϖ, hϖ⟩ := exists_uniformizer k
  have hord : ord k ϖ = 1 := ord_eq_one hϖ
  have ha : 0 < ‖(χ ϖ : ℂ)‖ := norm_pos_iff.2 (χ ϖ).ne_zero
  have hq : (1 : ℝ) < (resCard k : ℝ) := by exact_mod_cast GlobalTheory.SplitWeil.one_lt_resCard k
  have hlq : Real.log (resCard k : ℝ) ≠ 0 := (Real.log_pos hq).ne'
  refine ⟨-Real.log ‖(χ ϖ : ℂ)‖ / Real.log (resCard k : ℝ), fun z => ?_⟩
  have hz : ‖(χ z : ℂ)‖ = ‖(χ ϖ : ℂ)‖ ^ ord k z := by
    have hw : valuation k ((ϖ ^ (-ord k z) * z : kˣ) : k) = 1 := by
      rw [← ord_eq_zero_iff, ord_mul, GlobalTheory.SmoothCharNorm.ord_zpow, hord]; ring
    have hdec : z = ϖ ^ (ord k z) * (ϖ ^ (-ord k z) * z) := by group
    conv_lhs => rw [hdec]
    rw [map_mul, Units.val_mul, norm_mul,
      GlobalTheory.SmoothCharNorm.norm_eq_one_of_valuation_eq_one χ hχ _ hw, mul_one, map_zpow,
      Units.val_zpow_eq_zpow_val, norm_zpow]
  rw [hz, GlobalTheory.LGrp.nabs_eq_zpow, ← Real.rpow_intCast, ← Real.rpow_intCast,
    ← Real.rpow_mul (by positivity), Real.rpow_def_of_pos ha,
    Real.rpow_def_of_pos (by positivity)]
  congr 1
  push_cast
  field_simp
