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

namespace GlobalTheory.CompanionTheory.LTLink

theorem eq_one_of_pow_eq_one_of_valuation_sub_lt {K Γ : Type*} [Field K]
    [LinearOrderedCommGroupWithZero Γ] (v : Valuation K Γ) {m : ℕ} {ξ : K}
    (hm : v (m : K) = 1) (hξ : ξ ^ m = 1) (h : v (ξ - 1) < 1) : ξ = 1 := by
  have hv : v ξ ≤ 1 := by
    have e : ξ = (ξ - 1) + 1 := by ring
    rw [e]
    exact (v.map_add _ _).trans (max_le h.le (by simp))
  have hp : ∀ i : ℕ, v (ξ ^ i - 1) < 1 := by
    intro i
    induction i with
    | zero => simp
    | succ i ih =>
      have e : ξ ^ (i + 1) - 1 = ξ * (ξ ^ i - 1) + (ξ - 1) := by ring
      rw [e]
      refine Valuation.map_add_lt v ?_ h
      rw [map_mul]
      exact lt_of_le_of_lt (mul_le_of_le_one_left' hv) ih
  have hs : v ((∑ i ∈ Finset.range m, ξ ^ i) - (m : K)) < 1 := by
    have e : (∑ i ∈ Finset.range m, ξ ^ i) - (m : K) = ∑ i ∈ Finset.range m, (ξ ^ i - 1) := by
      simp [Finset.sum_sub_distrib]
    rw [e]
    exact Valuation.map_sum_lt v one_ne_zero fun i _ => hp i
  have hsum : (∑ i ∈ Finset.range m, ξ ^ i) ≠ 0 := by
    intro h0
    rw [h0, zero_sub, Valuation.map_neg, hm] at hs
    exact lt_irrefl _ hs
  have := mul_geom_sum ξ m
  rw [hξ, sub_self] at this
  exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_right hsum)

theorem natCast_residue_eq_zero {l : ℕ} [Fact l.Prime] {F : Type} [Field F] [ValuativeRel F]
    [TopologicalSpace F] [IsNonarchimedeanLocalField F] [Algebra F (Om l)]
    [ValuativeExtension F (Om l)] : (l : 𝓀[F]) = 0 := by
  have hnl : ¬ ((1 : F) ≤ᵥ (l : F)) := by
    intro h
    have h2 := (ValuativeExtension.vle_iff_vle (A := F) (B := Om l) 1 (l : F)).2 h
    rw [map_one, map_natCast, GroundTheory.PAdicHodge.CyclNorms.vle_iff_norm_le, norm_one,
      ← map_natCast (algebraMap ℚ_[l] (Om l)), PadicAlgCl.norm_extends] at h2
    exact absurd (Padic.norm_natCast_lt_one_iff.mpr (dvd_refl l)) (not_lt.mpr h2)
  have hlt : valuation F (((l : 𝒪[F]) : 𝒪[F]) : F) < 1 := by
    refine not_le.mp fun h => hnl ?_
    rw [Valuation.Compatible.vle_iff_le (v := valuation F), map_one]
    simpa using h
  have hmem : (l : 𝒪[F]) ∈ IsLocalRing.maximalIdeal 𝒪[F] := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
      (Valuation.integer.integers (valuation F)).isUnit_iff_valuation_eq_one]
    exact ne_of_lt hlt
  rw [← map_natCast (IsLocalRing.residue 𝒪[F]), IsLocalRing.residue_eq_zero_iff]
  exact hmem

theorem unramifiedDegree_eq_one_of_mem_inertia : ∀ {l : ℕ} [Fact l.Prime] {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    {A : ValuationSubring Ω} {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
    (Bw : LocBridge l E Ω (Dec (F := E) A) O), GlobalTheory.Pst.Induces Bw →
    ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [Algebra F (Om l)] [ValuativeExtension F (Om l)] [IsSepClosure F (Om l)]
    (σ : ↥(Dec (F := E) A)), (σ : G E Ω) ∈ Ine (F := E) A → ∀ g : Om l ≃ₐ[F] Om l,
    (∀ y, g y = ((Bw.e σ : ↥(GK Bw.Kw)) : GQ l) y) → unramifiedDegree F (Om l) g = 1 := by
  intro l _ E Ω _ _ _ _ _ A O _ _ _ Bw hj F _ _ _ _ _ _ _ σ hσ g hg
  rw [GroundTheory.LocalField.unramifiedDegree_eq_one_iff]
  intro ζ hζ
  obtain ⟨m, hm, hζm⟩ := mem_unramifiedRoots_iff.1 hζ
  have hm0 : m ≠ 0 := by
    rintro rfl
    simp at hm
  have hcop : ¬ l ∣ m := by
    rintro ⟨k, rfl⟩
    apply hm
    rw [Nat.cast_mul, natCast_residue_eq_zero (l := l) (F := F), zero_mul]
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed E
  have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap E Ω).injective
  have : NeZero m := ⟨hm0⟩
  have : NeZero (m : Ω) := ⟨Nat.cast_ne_zero.mpr hm0⟩
  obtain ⟨ζ₀, h₀⟩ : ∃ z : Ω, IsPrimitiveRoot z m := HasEnoughRootsOfUnity.exists_primitiveRoot Ω m
  have hj0 := h₀.map_of_injective Bw.j.injective
  obtain ⟨i, -, hi⟩ := hj0.eq_pow_of_pow_eq_one hζm

  obtain ⟨z, hz, hzm⟩ : ∃ z : Ω, Bw.j z = ζ ∧ z ^ m = 1 :=
    ⟨ζ₀ ^ i, by rw [map_pow, hi], by rw [← pow_mul, mul_comm, pow_mul, h₀.pow_eq_one, one_pow]⟩
  have hz0 : z ≠ 0 := by
    rintro rfl
    simp [hm0] at hzm
  let s : G E Ω := (σ : G E Ω)
  have hgz : g ζ = Bw.j (s z) := by
    rw [hg, ← hz]
    exact Bw.e_comm σ z
  have hnorm : ‖Bw.j z‖ = 1 := by
    refine (pow_eq_one_iff_of_nonneg (norm_nonneg _) hm0).mp ?_
    rw [← norm_pow, ← map_pow, hzm, map_one, norm_one]
  have hzA : A.valuation z ≤ 1 := by
    rw [A.valuation_le_one_iff]
    exact (hj z).mpr hnorm.le
  have hzunit : A.valuation z = 1 :=
    le_antisymm hzA (not_lt.mp fun h => ((hj.valuation_lt_one_iff z).mp h).ne hnorm)
  have hlt : A.valuation (s z - z) < 1 := hσ.2 z hzA
  have hmn : ‖Bw.j (m : Ω)‖ = 1 := by
    rw [map_natCast, ← map_natCast (algebraMap ℚ_[l] (Om l)), PadicAlgCl.norm_extends,
      Padic.norm_natCast_eq_one_iff]
    exact (Nat.Prime.coprime_iff_not_dvd Fact.out).2 hcop
  have hmv : A.valuation (m : Ω) = 1 := by
    refine le_antisymm ?_ (not_lt.mp fun h => ((hj.valuation_lt_one_iff _).mp h).ne hmn)
    rw [A.valuation_le_one_iff]
    exact (hj _).mpr hmn.le
  have hsz : (s z / z) ^ m = 1 := by
    rw [div_pow, ← map_pow, hzm, map_one, div_one]
  have hone : s z / z = 1 := by
    refine eq_one_of_pow_eq_one_of_valuation_sub_lt A.valuation hmv hsz ?_
    have e : s z / z - 1 = (s z - z) / z := by field_simp
    rw [e, map_div₀, hzunit, div_one]
    exact hlt
  rw [hgz, (div_eq_one_iff_eq hz0).mp hone, hz]

end GlobalTheory.CompanionTheory.LTLink
