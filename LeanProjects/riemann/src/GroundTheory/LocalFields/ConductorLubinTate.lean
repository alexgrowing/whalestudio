import Mathlib
import GroundTheory.LocalFields.ConductorFormalGroup
import GroundTheory.LocalFields.LubinTatePrimitive
import GroundTheory.LocalFields.LubinTateTowerMaps
import GroundTheory.LocalFields.LubinTateLimitGalois
import GroundTheory.LocalFields.SeparableClosureValuation
import GroundTheory.LocalFields.Monogenic
import GroundTheory.LocalFields.Different
import GroundTheory.LocalFields.UpperNumbering

noncomputable section

open ValuativeRel IsDiscreteValuationRing GroundTheory.LocalField.FormalGroup

namespace GroundTheory.LocalField

section UnitsMk

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

theorem unitsMk_surjective {π : 𝒪[K]} (hπ : Irreducible π) (n : ℕ) :
    Function.Surjective (unitsMk π n) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · intro v
    refine ⟨1, ?_⟩
    have : Subsingleton (𝒪[K] ⧸ Ideal.span {π ^ 0}) := by
      rw [pow_zero, Ideal.span_singleton_one]
      exact Ideal.Quotient.subsingleton_iff.mpr rfl
    exact Subsingleton.elim _ _
  apply IsLocalRing.surjective_units_map_of_local_ringHom _ Ideal.Quotient.mk_surjective
  constructor
  intro a ha
  by_contra h
  have hm : a ∈ 𝓂[K] := (IsLocalRing.mem_maximalIdeal a).2 h
  obtain ⟨b, rfl⟩ := (mem_maximalIdeal_iff_dvd hπ).1 hm
  have hnil : IsNilpotent (Ideal.Quotient.mk (Ideal.span {π ^ n}) (π * b)) := by
    refine ⟨n, ?_⟩
    rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem, mul_pow]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
  have hne : Nontrivial (𝒪[K] ⧸ Ideal.span {π ^ n}) := by
    rw [Ideal.Quotient.nontrivial_iff, Ne, Ideal.span_singleton_eq_top]
    exact fun hu => hπ.not_isUnit (isUnit_of_dvd_unit (dvd_pow_self π hn.ne') hu)
  exact hnil.not_isUnit ha

end UnitsMk

section LowerIndex

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable {Ω : Type*} [Field Ω] [ValuativeRel Ω] [TopologicalSpace Ω] [IsValuativeTopology Ω]
  [Algebra K Ω] [ValuativeExtension K Ω] [Algebra.IsAlgebraic K Ω] [IsSepClosed Ω]
variable {π : 𝒪[K]} (hπ : Irreducible π) {f : PowerSeries 𝒪[K]}

theorem ordRat_primitive (hf : IsLubinTateSeries π f) {n : ℕ}
    {l : IdealPoint Ω (lubinTateFormalGroup hπ hf)} (hl : l ∈ lubinTateTorsion Ω hf n)
    (hl' : l ∉ lubinTateTorsion Ω hf (n - 1)) :
    ordRat K l.val = 1 / (ramificationIndex K (lubinTateField Ω hπ hf n) : ℚ) := by
  obtain ⟨y, hy⟩ := exists_integer_eq (val_mem_lubinTateField hπ hf hl) l.valuation_lt_one
  have hirr := irreducible_of_primitive hπ hf hl hl' hy
  have h := ordRat_algebraMap_of_finite (K := K) (Ω := Ω) (L := lubinTateField Ω hπ hf n) (y : _)
  rw [ord_uniformizer hirr] at h
  rw [← hy]
  simpa using h

theorem smul_primitive (hf : IsLubinTateSeries π f) {n k : ℕ} (hk : k < n)
    {l : IdealPoint Ω (lubinTateFormalGroup hπ hf)} (hl : l ∈ lubinTateTorsion Ω hf n)
    (hl' : l ∉ lubinTateTorsion Ω hf (n - 1)) {w : 𝒪[K]} (hw : ¬ π ∣ w) :
    (π ^ k * w) • l ∈ lubinTateTorsion Ω hf (n - k) ∧
      (π ^ k * w) • l ∉ lubinTateTorsion Ω hf (n - k - 1) := by
  have hspec := (primitive_spec hπ hf hl hl').1
  rw [mem_lubinTateTorsion] at hl
  refine ⟨?_, ?_⟩
  · rw [mem_lubinTateTorsion, smul_smul, ← mul_assoc, ← pow_add, Nat.sub_add_cancel hk.le,
      mul_comm, mul_smul, hl, smul_zero]
  · rw [mem_lubinTateTorsion, smul_smul, ← mul_assoc, ← pow_add,
      show n - k - 1 + k = n - 1 by omega, hspec, Ideal.mem_span_singleton]
    intro h
    apply hw
    have e : π ^ n = π ^ (n - 1) * π := by rw [← pow_succ, Nat.sub_add_cancel (by omega)]
    rw [e] at h
    exact (mul_dvd_mul_iff_left (pow_ne_zero _ hπ.ne_zero)).1 h

omit [IsSepClosed Ω] in

theorem adjoin_eq_top_of_irreducible_of_residueDegree_eq_one {L : Type*} [Field L] [ValuativeRel L]
    [TopologicalSpace L] [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L]
    [FiniteDimensional K L] (h : residueDegree K L = 1) {x : 𝒪[L]} (hx : Irreducible x) :
    Algebra.adjoin 𝒪[K] {x} = ⊤ := by
  refine adjoin_eq_top_of_residue_of_addVal_eq_one K ?_ (Algebra.self_mem_adjoin_singleton _ _)
    (addVal_uniformizer hx)
  have h1 : Module.finrank 𝓀[K] 𝓀[L] = 1 := by rw [← residueDegree_eq_finrank K L]; exact h
  rw [eq_top_iff, ← Subalgebra.bot_eq_top_of_finrank_eq_one h1]
  exact bot_le

include hπ in

theorem exists_sub_one_eq_pow_mul {k : ℕ} {u : 𝒪[K]ˣ} (hu : u ∈ unitFiltration K k)
    (hu' : u ∉ unitFiltration K (k + 1)) : ∃ w : 𝒪[K], (u : 𝒪[K]) - 1 = π ^ k * w ∧ ¬ π ∣ w := by
  rw [mem_unitFiltration, mem_maximalIdeal_pow_iff hπ] at hu hu'
  obtain ⟨w, hw⟩ := hu
  refine ⟨w, hw, fun hdvd => hu' ?_⟩
  rw [hw, pow_succ]
  exact mul_dvd_mul_left _ hdvd

theorem lowerIndex_lubinTateField (hf : IsLubinTateSeries π f) {n k : ℕ} (hk : k < n)
    (σ : lubinTateField Ω hπ hf n ≃ₐ[K] lubinTateField Ω hπ hf n) (u : 𝒪[K]ˣ)
    (hσ : lubinTateGalEquiv hπ hf n σ = unitsMk π n u) (hu : u ∈ unitFiltration K k)
    (hu' : u ∉ unitFiltration K (k + 1)) :
    lowerIndex K (lubinTateField Ω hπ hf n) σ = ((Nat.card 𝓀[K] ^ k : ℕ) : ℕ∞) := by
  have hn : 0 < n := by omega
  obtain ⟨l, hl, hl'⟩ := exists_primitive hπ hf hn (Ω := Ω)
  obtain ⟨x, hx⟩ := exists_integer_eq (val_mem_lubinTateField hπ hf hl) l.valuation_lt_one
  have hxirr := irreducible_of_primitive hπ hf hl hl' hx
  rw [lowerIndex_eq_addVal_of_adjoin_eq_top (adjoin_eq_top_of_irreducible_of_residueDegree_eq_one
    (residueDegree_lubinTateField hπ hf hn) hxirr) σ]
  obtain ⟨w, hw, hwπ⟩ := exists_sub_one_eq_pow_mul hπ hu hu'
  set μ := (π ^ k * w) • l with hμdef
  have hμ := smul_primitive hπ hf hk hl hl' hwπ
  have hσx : ((integerAlgEquiv K (lubinTateField Ω hπ hf n) σ x : lubinTateField Ω hπ hf n) : Ω) = ((u : 𝒪[K]) • l).val := by
    rw [coe_integerAlgEquiv_apply]
    have e : (x : lubinTateField Ω hπ hf n) = ⟨l.val, val_mem_lubinTateField hπ hf hl⟩ := Subtype.ext hx
    rw [e]
    exact lubinTateGalEquiv_spec hf n σ l hl (u : 𝒪[K]) (by rw [hσ]; rfl)
  have hul : (u : 𝒪[K]) • l = l + μ := by
    rw [hμdef, ← hw, sub_smul, one_smul, add_sub_cancel]
  set z := integerAlgEquiv K (lubinTateField Ω hπ hf n) σ x - x with hzdef
  have hz : ((z : lubinTateField Ω hπ hf n) : Ω) = psEval (lubinTateFormalGroup hπ hf).toPowerSeries ![l.val, μ.val] -
      l.val := by
    rw [hzdef]
    push_cast
    rw [hσx, hul, IdealPoint.val_add, hx]
  have hvz : valuation Ω ((z : lubinTateField Ω hπ hf n) : Ω) = valuation Ω μ.val := by
    rw [hz]
    exact valuation_psEval_sub_left _ l.valuation_lt_one μ.valuation_lt_one
  have hz0 : z ≠ 0 := by
    intro h0
    rw [h0] at hvz
    simp only [ZeroMemClass.coe_zero, map_zero] at hvz
    have h1 : μ.val = 0 := (Valuation.zero_iff _).1 hvz.symm
    apply hμ.2
    rw [← hμdef, show μ = 0 from IdealPoint.ext (by rw [h1, IdealPoint.val_zero])]
    exact Submodule.zero_mem _
  obtain ⟨j, hj⟩ := exists_addVal_eq_coe hz0
  rw [hj]
  have hordj := ord_eq_of_addVal_eq hz0 hj
  have h2 := ordRat_algebraMap_of_finite (K := K) (Ω := Ω) (L := lubinTateField Ω hπ hf n)
    (z : lubinTateField Ω hπ hf n)
  have h3 : ordRat K ((z : lubinTateField Ω hπ hf n) : Ω) =
      1 / (ramificationIndex K (lubinTateField Ω hπ hf (n - k)) : ℚ) := by
    rw [ordRat_congr hvz, hμdef]
    exact ordRat_primitive hπ hf hμ.1 hμ.2
  have he : ramificationIndex K (lubinTateField Ω hπ hf n) =
      ramificationIndex K (lubinTateField Ω hπ hf (n - k)) * Nat.card 𝓀[K] ^ k := by
    rw [ramificationIndex_lubinTateField hπ hf hn,
      ramificationIndex_lubinTateField hπ hf (by omega : 0 < n - k), finrank_lubinTateField hπ hf hn,
      finrank_lubinTateField hπ hf (by omega : 0 < n - k), mul_assoc, ← pow_add]
    congr 2
    omega
  have heM : (0 : ℚ) < ramificationIndex K (lubinTateField Ω hπ hf (n - k)) := by
    exact_mod_cast ramificationIndex_pos K _
  have hq : (0 : ℚ) < (Nat.card 𝓀[K] : ℚ) ^ k := by
    have : 0 < Nat.card 𝓀[K] := Nat.card_pos
    positivity
  rw [IntermediateField.algebraMap_apply, h3, hordj, he] at h2
  push_cast at h2
  field_simp at h2
  have hjq : (j : ℚ) = ((Nat.card 𝓀[K] ^ k : ℕ) : ℚ) := by push_cast; linarith
  exact_mod_cast hjq

def lubinTateUnitSubgroup (hf : IsLubinTateSeries π f) (n j : ℕ) :
    Subgroup (lubinTateField Ω hπ hf n ≃ₐ[K] lubinTateField Ω hπ hf n) :=
  ((unitFiltration K j).map (unitsMk π n)).comap (lubinTateGalEquiv hπ hf n).toMonoidHom

theorem mem_lubinTateUnitSubgroup_iff (hf : IsLubinTateSeries π f) {n j : ℕ} (hj : j ≤ n)
    (σ : lubinTateField Ω hπ hf n ≃ₐ[K] lubinTateField Ω hπ hf n) (u : 𝒪[K]ˣ)
    (hσ : lubinTateGalEquiv hπ hf n σ = unitsMk π n u) :
    σ ∈ lubinTateUnitSubgroup hπ hf n j ↔ u ∈ unitFiltration K j := by
  rw [lubinTateUnitSubgroup, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, hσ, Subgroup.mem_map]
  constructor
  · rintro ⟨u', hu', he⟩
    have h1 : unitsMk π n (u'⁻¹ * u) = 1 := by rw [map_mul, map_inv, he, inv_mul_cancel]
    rw [unitsMk_eq_one_iff hπ] at h1
    have h2 := unitFiltration_antitone K hj h1
    simpa using (unitFiltration K j).mul_mem hu' h2
  · intro hu
    exact ⟨u, hu, rfl⟩

theorem lowerIndex_lubinTateField_cases (hf : IsLubinTateSeries π f) {n : ℕ}
    (σ : lubinTateField Ω hπ hf n ≃ₐ[K] lubinTateField Ω hπ hf n) :
    σ = 1 ∨ ∃ m < n, lowerIndex K (lubinTateField Ω hπ hf n) σ = ((Nat.card 𝓀[K] ^ m : ℕ) : ℕ∞) ∧
      ∀ j, σ ∈ lubinTateUnitSubgroup hπ hf n j ↔ j ≤ m := by
  obtain ⟨u, hu⟩ := unitsMk_surjective hπ n (lubinTateGalEquiv hπ hf n σ)
  by_cases hun : u ∈ unitFiltration K n
  · left
    apply (lubinTateGalEquiv hπ hf n).injective
    rw [← hu, map_one, unitsMk_eq_one_iff hπ]
    exact hun
  right
  have hex : ∃ m, u ∉ unitFiltration K (m + 1) := by
    rcases n with _ | n
    · exact absurd (by rw [unitFiltration_zero]; trivial) hun
    · exact ⟨n, hun⟩
  classical
  set m := Nat.find hex with hm
  have hm1 : u ∉ unitFiltration K (m + 1) := Nat.find_spec hex
  have hm0 : u ∈ unitFiltration K m := by
    rcases Nat.eq_zero_or_pos m with h0 | hpos
    · rw [h0, unitFiltration_zero]; trivial
    · have := Nat.find_min hex (show m - 1 < m by omega)
      rw [not_not, Nat.sub_add_cancel hpos] at this
      exact this
  have hmn : m < n := by
    by_contra h
    exact hun (unitFiltration_antitone K (by omega) hm0)
  refine ⟨m, hmn, lowerIndex_lubinTateField hπ hf hmn σ u hu.symm hm0 hm1, fun j => ?_⟩
  have hq : 1 < Nat.card 𝓀[K] := Finite.one_lt_card
  constructor
  · intro hj
    by_contra hjm
    rcases le_or_gt j n with hjn | hjn
    · rw [mem_lubinTateUnitSubgroup_iff hπ hf hjn σ u hu.symm] at hj
      exact hm1 (unitFiltration_antitone K (by omega) hj)
    · have hj' : σ ∈ lubinTateUnitSubgroup hπ hf n n :=
        Subgroup.comap_mono (Subgroup.map_mono (unitFiltration_antitone K hjn.le)) hj
      rw [mem_lubinTateUnitSubgroup_iff hπ hf le_rfl σ u hu.symm] at hj'
      exact hun hj'
  · intro hjm
    rw [mem_lubinTateUnitSubgroup_iff hπ hf (by omega) σ u hu.symm]
    exact unitFiltration_antitone K hjm hm0

theorem index_lubinTateUnitSubgroup (hf : IsLubinTateSeries π f) {n j : ℕ} (hj : j ≤ n) :
    (lubinTateUnitSubgroup hπ hf n j : Subgroup (lubinTateField Ω hπ hf n ≃ₐ[K] _)).index =
      (unitFiltration K j).index := by
  have h1 := Subgroup.index_comap_of_surjective (H := (unitFiltration K j).map (unitsMk π n))
    (f := (lubinTateGalEquiv (Ω := Ω) hπ hf n).toMonoidHom) (lubinTateGalEquiv (Ω := Ω) hπ hf n).surjective
  refine h1.trans (Subgroup.index_map_eq _ (unitsMk_surjective hπ n) ?_)
  intro u hu
  rw [MonoidHom.mem_ker, unitsMk_eq_one_iff hπ] at hu
  exact unitFiltration_antitone K hj hu

theorem sum_enatMin_lowerIndex_lubinTateField (hf : IsLubinTateSeries π f) {n k : ℕ} (hk : k < n) :
    ∑ σ : lubinTateField Ω hπ hf n ≃ₐ[K] lubinTateField Ω hπ hf n,
        enatMin (lowerIndex K (lubinTateField Ω hπ hf n) σ) ((Nat.card 𝓀[K] : ℝ) ^ k) =
      (k + 1) * Nat.card (lubinTateField Ω hπ hf n ≃ₐ[K] lubinTateField Ω hπ hf n) := by
  classical
  have hq : 1 ≤ Nat.card 𝓀[K] := Finite.one_lt_card.le
  have hqR : (1 : ℝ) ≤ Nat.card 𝓀[K] := by exact_mod_cast hq
  induction k with
  | zero =>
    have h1 : ∀ σ : lubinTateField Ω hπ hf n ≃ₐ[K] lubinTateField Ω hπ hf n,
        enatMin (lowerIndex K (lubinTateField Ω hπ hf n) σ) ((Nat.card 𝓀[K] : ℝ) ^ 0) = 1 := by
      intro σ
      rcases lowerIndex_lubinTateField_cases hπ hf σ with rfl | ⟨m, -, hi, -⟩
      · simp
      · rw [hi, enatMin_coe, pow_zero]
        push_cast
        exact min_eq_right (one_le_pow₀ hqR)
    simp_rw [h1]
    simp [Nat.card_eq_fintype_card]
  | succ k ih =>
    have h1 : ∀ σ : lubinTateField Ω hπ hf n ≃ₐ[K] lubinTateField Ω hπ hf n,
        enatMin (lowerIndex K (lubinTateField Ω hπ hf n) σ) ((Nat.card 𝓀[K] : ℝ) ^ (k + 1)) =
          enatMin (lowerIndex K (lubinTateField Ω hπ hf n) σ) ((Nat.card 𝓀[K] : ℝ) ^ k) +
            (if σ ∈ lubinTateUnitSubgroup hπ hf n (k + 1) then 1 else 0) *
              ((Nat.card 𝓀[K] : ℝ) ^ (k + 1) - (Nat.card 𝓀[K] : ℝ) ^ k) := by
      intro σ
      rcases lowerIndex_lubinTateField_cases hπ hf σ with rfl | ⟨m, -, hi, hS⟩
      · simp [(lubinTateUnitSubgroup hπ hf n (k + 1)).one_mem]
      · rw [hi, enatMin_coe, enatMin_coe, hS]
        push_cast
        by_cases hkm : k + 1 ≤ m
        · rw [if_pos hkm, min_eq_right (pow_le_pow_right₀ hqR hkm),
            min_eq_right (pow_le_pow_right₀ hqR (by omega))]
          ring
        · rw [if_neg hkm, min_eq_left (pow_le_pow_right₀ hqR (by omega)),
            min_eq_left (pow_le_pow_right₀ hqR (by omega))]
          ring
    simp_rw [h1]
    rw [Finset.sum_add_distrib, ih (by omega), ← Finset.sum_mul, Finset.sum_boole, card_filter_mem]
    have hidx := index_lubinTateUnitSubgroup hπ hf (show k + 1 ≤ n by omega) (Ω := Ω)
    rw [index_unitFiltration K (by omega : 1 ≤ k + 1)] at hidx
    have hc := Subgroup.card_mul_index (lubinTateUnitSubgroup hπ hf n (k + 1) (Ω := Ω))
    rw [hidx] at hc
    have hcR : (Nat.card (lubinTateUnitSubgroup hπ hf n (k + 1) (Ω := Ω)) : ℝ) *
        (((Nat.card 𝓀[K] : ℝ) - 1) * (Nat.card 𝓀[K] : ℝ) ^ k) =
          Nat.card (lubinTateField Ω hπ hf n ≃ₐ[K] lubinTateField Ω hπ hf n) := by
      rw [← hc]
      push_cast [Nat.cast_sub hq]
      simp
    rw [show (Nat.card 𝓀[K] : ℝ) ^ (k + 1) - (Nat.card 𝓀[K] : ℝ) ^ k =
      ((Nat.card 𝓀[K] : ℝ) - 1) * (Nat.card 𝓀[K] : ℝ) ^ k by ring, hcR]
    push_cast
    ring

theorem herbrandPhi_lubinTateField (hf : IsLubinTateSeries π f) {n k : ℕ} (hk : k < n) :
    herbrandPhi K (lubinTateField Ω hπ hf n) (((Nat.card 𝓀[K] ^ k : ℕ) : ℝ) - 1) = k := by
  have hn : 0 < n := by omega
  have hq : 1 ≤ Nat.card 𝓀[K] := Finite.one_lt_card.le
  have hqk : (1 : ℝ) ≤ ((Nat.card 𝓀[K] ^ k : ℕ) : ℝ) := by exact_mod_cast Nat.one_le_pow _ _ hq
  rw [herbrandPhi_eq_sum_lowerIndex (by linarith), sub_add_cancel]
  push_cast
  rw [sum_enatMin_lowerIndex_lubinTateField hπ hf hk, card_lowerRamificationGroup_zero,
    ramificationIndex_lubinTateField hπ hf hn, ← IsGalois.card_aut_eq_finrank]
  have hG : (0 : ℝ) < Nat.card (lubinTateField Ω hπ hf n ≃ₐ[K] lubinTateField Ω hπ hf n) := by
    exact_mod_cast Nat.card_pos
  field_simp
  ring

theorem upperRamificationGroup_lubinTateField (hf : IsLubinTateSeries π f) (n : ℕ) (v : ℝ) :
    upperRamificationGroup K (lubinTateField Ω hπ hf n) v =
      lubinTateUnitSubgroup hπ hf n ⌈v⌉.toNat := by
  ext σ
  rcases lowerIndex_lubinTateField_cases hπ hf σ with rfl | ⟨m, hmn, hi, hS⟩
  · simp only [Subgroup.one_mem]
  · rw [mem_upperRamificationGroup_iff_of_lowerIndex_eq hi, herbrandPhi_lubinTateField hπ hf hmn, hS,
      Int.toNat_le, Int.ceil_le]
    push_cast
    rfl

end LowerIndex

end GroundTheory.LocalField
