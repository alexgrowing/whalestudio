import Mathlib
import GroundTheory.LocalFields.Interface
import GroundTheory.LocalFields.Integers
import GroundTheory.LocalFields.IntermediateField

noncomputable section

namespace GroundTheory.LocalField

open ValuativeRel Polynomial IsDiscreteValuationRing
open scoped _root_.IntermediateField

section DVR

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

theorem eq_zero_of_addVal_lt_of_sum_eq_zero {ι : Type*} [DecidableEq ι] {s : Finset ι} {t : ι → R}
    (hs : ∑ i ∈ s, t i = 0) {j : ι} (hj : j ∈ s)
    (hlt : ∀ i ∈ s, i ≠ j → addVal R (t j) < addVal R (t i)) : t j = 0 := by
  by_contra h0
  have htop : addVal R (t j) ≠ ⊤ := fun h => h0 (addVal_eq_top_iff.mp h)
  have hrest : addVal R (t j) < addVal R (∑ i ∈ s.erase j, t i) :=
    (addVal R).map_lt_sum htop fun i hi => hlt i (Finset.mem_of_mem_erase hi)
      (Finset.ne_of_mem_erase hi)
  have := (addVal R).map_add_eq_of_lt_left hrest
  rw [Finset.add_sum_erase s t hj, hs, AddValuation.map_zero] at this
  exact htop this.symm

theorem exists_addVal_eq_coe {x : R} (hx : x ≠ 0) : ∃ k : ℕ, addVal R x = k := by
  obtain ⟨ϖ, hϖ⟩ := exists_irreducible R
  obtain ⟨k, u, rfl⟩ := eq_unit_mul_pow_irreducible hx hϖ
  exact ⟨k, addVal_def' u hϖ k⟩

end DVR

section Local

variable (K L : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]

theorem addVal_algebraMap_integer (x : 𝒪[K]) :
    addVal 𝒪[L] (algebraMap 𝒪[K] 𝒪[L] x) = ramificationIndex K L * addVal 𝒪[K] x := by
  obtain ⟨ϖ, hϖ⟩ := exists_irreducible 𝒪[K]
  obtain ⟨ϖL, hϖL⟩ := exists_irreducible 𝒪[L]
  have key : addVal 𝒪[L] (algebraMap 𝒪[K] 𝒪[L] ϖ) = ramificationIndex K L := by
    have h := map_maximalIdeal K L
    rw [hϖ.maximalIdeal_eq, hϖL.maximalIdeal_eq, Ideal.map_span, Set.image_singleton,
      Ideal.span_singleton_pow, Ideal.span_singleton_eq_span_singleton] at h
    rw [(addVal_eq_iff_associated _ _).mpr h, hϖL.addVal_pow]
  rcases eq_or_ne x 0 with rfl | hx
  · rw [map_zero, addVal_zero, addVal_zero, ENat.mul_top]
    exact_mod_cast (ramificationIndex_pos K L).ne'
  obtain ⟨k, u, rfl⟩ := eq_unit_mul_pow_irreducible hx hϖ
  rw [map_mul, map_pow, addVal_mul, addVal_pow, key, addVal_def' u hϖ k]
  have hu : IsUnit (algebraMap 𝒪[K] 𝒪[L] u) := u.isUnit.map _
  rw [addVal_eq_zero_iff.mpr hu, zero_add, nsmul_eq_mul, mul_comm]

end Local

section DVR2

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

theorem mem_maximalIdeal_pow_iff_le_addVal (k : ℕ) (x : R) :
    x ∈ IsLocalRing.maximalIdeal R ^ k ↔ (k : ℕ∞) ≤ addVal R x := by
  obtain ⟨ϖ, hϖ⟩ := exists_irreducible R
  rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton,
    ← addVal_le_iff_dvd, hϖ.addVal_pow]

theorem addVal_eq_one_of_mem_of_notMem_sq {x : R} (h1 : x ∈ IsLocalRing.maximalIdeal R)
    (h2 : x ∉ IsLocalRing.maximalIdeal R ^ 2) : addVal R x = 1 := by
  rw [← pow_one (IsLocalRing.maximalIdeal R), mem_maximalIdeal_pow_iff_le_addVal] at h1
  rw [mem_maximalIdeal_pow_iff_le_addVal, not_le] at h2
  have h0 : x ≠ 0 := by
    rintro rfl
    simp at h2
  obtain ⟨k, hk⟩ := exists_addVal_eq_coe h0
  rw [hk] at h1 h2 ⊢
  norm_cast at h1 h2 ⊢
  omega

end DVR2

section Forward

variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]

theorem natDegree_mul_addVal_eq_ramificationIndex {f : 𝒪[K][X]}
    (hf : f.IsEisensteinAt (IsLocalRing.maximalIdeal 𝒪[K])) (hn : 0 < f.natDegree)
    {α : 𝒪[L]} (hα : aeval α f = 0) :
    (f.natDegree : ℕ∞) * addVal 𝒪[L] α = ramificationIndex K L := by
  set n := f.natDegree with hn_def
  set e := ramificationIndex K L with he_def
  have he : 0 < e := ramificationIndex_pos K L
  have hinj := algebraMap_integer_injective K L
  have hα0 : α ≠ 0 := by
    rintro rfl
    rw [aeval_def, eval₂_at_zero] at hα
    have : f.coeff 0 = 0 := hinj (by rw [hα, map_zero])
    exact hf.notMem (by rw [this]; exact zero_mem _)
  obtain ⟨m, hm⟩ := exists_addVal_eq_coe hα0
  set t : ℕ → 𝒪[L] := fun i => algebraMap 𝒪[K] 𝒪[L] (f.coeff i) * α ^ i with ht
  have hsum : ∑ i ∈ Finset.range (n + 1), t i = 0 := by
    rw [← hα, aeval_eq_sum_range]
    simp [t, Algebra.smul_def, n]
  have hval : ∀ i, addVal 𝒪[L] (t i) = e * addVal 𝒪[K] (f.coeff i) + i * m := by
    intro i
    simp only [t, addVal_mul, addVal_pow, addVal_algebraMap_integer, hm, nsmul_eq_mul, e]

  have hlow : ∀ i < n, ((e + i * m : ℕ) : ℕ∞) ≤ addVal 𝒪[L] (t i) := by
    intro i hi
    have h1 : (1 : ℕ∞) ≤ addVal 𝒪[K] (f.coeff i) := by
      have := hf.mem hi
      rw [← pow_one (IsLocalRing.maximalIdeal 𝒪[K]), mem_maximalIdeal_pow_iff_le_addVal] at this
      exact_mod_cast this
    rw [hval]
    push_cast
    gcongr
    calc (e : ℕ∞) = e * 1 := (mul_one _).symm
      _ ≤ e * addVal 𝒪[K] (f.coeff i) := by gcongr

  have htop : addVal 𝒪[L] (t n) = ((n * m : ℕ) : ℕ∞) := by
    have hu : IsUnit (f.coeff n) := by
      have := hf.leading
      rw [leadingCoeff] at this
      exact (IsLocalRing.notMem_maximalIdeal.mp this)
    rw [hval, addVal_eq_zero_iff.mpr hu]
    push_cast
    ring

  have hbot : addVal 𝒪[L] (t 0) = (e : ℕ∞) := by
    have h1 : f.coeff 0 ∈ IsLocalRing.maximalIdeal 𝒪[K] := hf.mem hn
    rw [hval, addVal_eq_one_of_mem_of_notMem_sq h1 hf.notMem]
    simp
  have hne_n : t n ≠ 0 := by
    intro h
    rw [h, addVal_zero] at htop
    exact ENat.top_ne_natCast _ htop
  have hne_0 : t 0 ≠ 0 := by
    intro h
    rw [h, addVal_zero] at hbot
    exact ENat.top_ne_natCast _ hbot

  have hA : e ≤ n * m := by
    by_contra hlt
    rw [not_le] at hlt
    refine hne_n (eq_zero_of_addVal_lt_of_sum_eq_zero hsum (Finset.self_mem_range_succ n) ?_)
    intro i hi hin
    have hi' : i < n := lt_of_le_of_ne (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)) hin
    refine lt_of_lt_of_le ?_ (hlow i hi')
    rw [htop]
    exact_mod_cast (by omega : n * m < e + i * m)
  have hm1 : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · rw [h] at hA
      omega
    · exact h

  have hB : n * m ≤ e := by
    by_contra hlt
    rw [not_le] at hlt
    refine hne_0 (eq_zero_of_addVal_lt_of_sum_eq_zero hsum (by simp) ?_)
    intro i hi hi0
    have hi' : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    rw [hbot]
    rcases lt_or_eq_of_le hi' with hlt' | rfl
    · refine lt_of_lt_of_le ?_ (hlow i hlt')
      have : 1 ≤ i * m := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero hi0 (by omega))
      exact_mod_cast (by omega : e < e + i * m)
    · rw [htop]
      exact_mod_cast hlt
  rw [hm]
  exact_mod_cast le_antisymm hB hA

end Forward

section TotallyRamified

variable (K L : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]

theorem residueDegree_eq_one_of_ramificationIndex_eq_finrank
    (h : ramificationIndex K L = Module.finrank K L) : residueDegree K L = 1 := by
  have h1 := ramificationIndex_mul_residueDegree K L
  have h2 := ramificationIndex_pos K L
  rw [h] at h1 h2
  exact (Nat.mul_eq_left h2.ne').mp h1

theorem exists_sub_algebraMap_mem_maximalIdeal (h : residueDegree K L = 1) (w : 𝒪[L]) :
    ∃ c : 𝒪[K], w - algebraMap 𝒪[K] 𝒪[L] c ∈ IsLocalRing.maximalIdeal 𝒪[L] := by
  rw [residueDegree_eq_finrank, finrank_eq_one_iff_of_nonzero' (1 : 𝓀[L]) one_ne_zero] at h
  obtain ⟨c, hc⟩ := h (IsLocalRing.residue 𝒪[L] w)
  obtain ⟨c', rfl⟩ := IsLocalRing.residue_surjective c
  refine ⟨c', ?_⟩
  rw [← IsLocalRing.residue_eq_zero_iff, map_sub, ← hc, Algebra.smul_def, mul_one,
    IsLocalRing.ResidueField.algebraMap_residue, sub_self]

end TotallyRamified

section Eisenstein

variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

theorem isUnit_leadingCoeff_of_isEisensteinAt {f : 𝒪[K][X]}
    (hf : f.IsEisensteinAt (IsLocalRing.maximalIdeal 𝒪[K])) : IsUnit f.leadingCoeff :=
  IsLocalRing.notMem_maximalIdeal.mp hf.leading

theorem isPrimitive_of_isEisensteinAt {f : 𝒪[K][X]}
    (hf : f.IsEisensteinAt (IsLocalRing.maximalIdeal 𝒪[K])) : f.IsPrimitive := by
  intro r hr
  rw [C_dvd_iff_dvd_coeff] at hr
  exact isUnit_of_dvd_unit (hr _) (isUnit_leadingCoeff_of_isEisensteinAt hf)

theorem irreducible_of_isEisensteinAt {f : 𝒪[K][X]}
    (hf : f.IsEisensteinAt (IsLocalRing.maximalIdeal 𝒪[K])) (hn : 0 < f.natDegree) :
    Irreducible f :=
  hf.irreducible (IsLocalRing.maximalIdeal.isMaximal 𝒪[K]).isPrime
    (isPrimitive_of_isEisensteinAt hf) hn

theorem irreducible_map_of_isEisensteinAt {f : 𝒪[K][X]}
    (hf : f.IsEisensteinAt (IsLocalRing.maximalIdeal 𝒪[K])) (hn : 0 < f.natDegree) :
    Irreducible (f.map (algebraMap 𝒪[K] K)) :=
  (isPrimitive_of_isEisensteinAt hf).irreducible_iff_irreducible_map_fraction_map.mp
    (irreducible_of_isEisensteinAt hf hn)

variable [Field L] [Algebra K L]

theorem isIntegral_of_isEisensteinAt {f : 𝒪[K][X]}
    (hf : f.IsEisensteinAt (IsLocalRing.maximalIdeal 𝒪[K])) {α : L} (hα : aeval α f = 0) :
    IsIntegral 𝒪[K] α := by
  obtain ⟨u, hu⟩ := isUnit_leadingCoeff_of_isEisensteinAt hf
  refine ⟨C (↑u⁻¹ : 𝒪[K]) * f, monic_C_mul_of_mul_leadingCoeff_eq_one (by rw [← hu]; simp), ?_⟩
  rw [← aeval_def, map_mul, hα, mul_zero]

theorem finrank_adjoin_le_of_isEisensteinAt {f : 𝒪[K][X]}
    (hf : f.IsEisensteinAt (IsLocalRing.maximalIdeal 𝒪[K])) {α : L} (hα : aeval α f = 0) :
    Module.finrank K K⟮α⟯ ≤ f.natDegree := by
  have hint : IsIntegral K α := (isIntegral_of_isEisensteinAt hf hα).tower_top
  have hinj : Function.Injective (algebraMap 𝒪[K] K) := IsFractionRing.injective 𝒪[K] K
  have hne : f.map (algebraMap 𝒪[K] K) ≠ 0 := by
    rw [Ne, Polynomial.map_eq_zero_iff hinj]
    rintro rfl
    exact hf.leading (by simp)
  rw [IntermediateField.adjoin.finrank hint, ← natDegree_map_eq_of_injective hinj f]
  exact natDegree_le_of_dvd (minpoly.dvd K α (by rw [aeval_map_algebraMap, hα])) hne

theorem minpoly_eq_of_isEisensteinAt {f : 𝒪[K][X]}
    (hf : f.IsEisensteinAt (IsLocalRing.maximalIdeal 𝒪[K])) (hn : 0 < f.natDegree) {α : L}
    (hα : aeval α f = 0) :
    minpoly K α = C (algebraMap 𝒪[K] K f.leadingCoeff)⁻¹ * f.map (algebraMap 𝒪[K] K) := by
  have hinj : Function.Injective (algebraMap 𝒪[K] K) := IsFractionRing.injective 𝒪[K] K
  have hc : algebraMap 𝒪[K] K f.leadingCoeff ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ hinj]
    rintro h
    exact hf.leading (by rw [h]; exact zero_mem _)
  refine (minpoly.eq_of_irreducible_of_monic ?_ ?_ ?_).symm
  · rw [irreducible_isUnit_mul (isUnit_C.mpr (IsUnit.mk0 _ (inv_ne_zero hc)))]
    exact irreducible_map_of_isEisensteinAt hf hn
  · rw [map_mul, aeval_map_algebraMap, hα, mul_zero]
  · refine monic_C_mul_of_mul_leadingCoeff_eq_one ?_
    rw [leadingCoeff_map_of_injective hinj, inv_mul_cancel₀ hc]

end Eisenstein

section Root

variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]
  {f : 𝒪[K][X]}

theorem mem_integer_of_isEisensteinAt (hf : f.IsEisensteinAt (IsLocalRing.maximalIdeal 𝒪[K]))
    {α : L} (hα : aeval α f = 0) : α ∈ 𝒪[L] :=
  (isIntegral_iff K L α).mp (isIntegral_of_isEisensteinAt hf hα)

theorem aeval_integer_eq_zero {α : L} (h : α ∈ 𝒪[L]) (hα : aeval α f = 0) :
    aeval (⟨α, h⟩ : 𝒪[L]) f = 0 := by
  refine Subtype.val_injective ?_
  have h2 : (IsScalarTower.toAlgHom 𝒪[K] 𝒪[L] L) (aeval (⟨α, h⟩ : 𝒪[L]) f) = aeval α f :=
    (aeval_algHom_apply _ _ _).symm
  rw [hα] at h2
  simpa using h2

theorem isEisensteinAt_root_of_finrank_le (hf : f.IsEisensteinAt (IsLocalRing.maximalIdeal 𝒪[K]))
    (hn : 0 < f.natDegree) {α : 𝒪[L]} (hα : aeval α f = 0)
    (hdeg : Module.finrank K L ≤ f.natDegree) :
    ramificationIndex K L = f.natDegree ∧ Module.finrank K L = f.natDegree ∧ Irreducible α := by
  have key := natDegree_mul_addVal_eq_ramificationIndex hf hn hα
  have hα0 : α ≠ 0 := by
    rintro rfl
    rw [addVal_zero, ENat.mul_top (by exact_mod_cast hn.ne')] at key
    exact ENat.top_ne_natCast _ key
  obtain ⟨m, hm⟩ := exists_addVal_eq_coe hα0
  rw [hm] at key
  have key' : f.natDegree * m = ramificationIndex K L := by exact_mod_cast key
  have hef := ramificationIndex_mul_residueDegree K L
  have hf1 := residueDegree_pos K L
  have he := ramificationIndex_pos K L
  have hle : ramificationIndex K L ≤ Module.finrank K L := by
    rw [← hef]
    exact Nat.le_mul_of_pos_right _ hf1
  have hm1 : m = 1 := by
    rcases Nat.lt_or_ge m 1 with h | h
    · have : m = 0 := by omega
      rw [this, mul_zero] at key'
      omega
    · have : f.natDegree * m ≤ f.natDegree * 1 := by omega
      have := Nat.le_of_mul_le_mul_left this hn
      omega
  subst hm1
  rw [mul_one] at key'
  refine ⟨key'.symm, by omega, ?_⟩
  obtain ⟨ϖ, hϖ⟩ := exists_irreducible 𝒪[L]
  have : Associated ϖ α := by
    rw [← addVal_eq_iff_associated, addVal_uniformizer hϖ, hm, Nat.cast_one]
  exact this.irreducible hϖ

variable (hf : f.IsEisensteinAt (IsLocalRing.maximalIdeal 𝒪[K])) (hn : 0 < f.natDegree)
  {α : L} (hα : aeval α f = 0)
include hf hn hα

section Generated

variable (hgen : K⟮α⟯ = ⊤)
include hgen

omit hn in

theorem finrank_le_of_isEisensteinAt : Module.finrank K L ≤ f.natDegree := by
  rw [← IntermediateField.finrank_top', ← hgen]
  exact finrank_adjoin_le_of_isEisensteinAt hf hα

theorem finrank_eq_natDegree_of_isEisensteinAt : Module.finrank K L = f.natDegree :=
  (isEisensteinAt_root_of_finrank_le hf hn (aeval_integer_eq_zero
    (mem_integer_of_isEisensteinAt hf hα) hα) (finrank_le_of_isEisensteinAt hf hα hgen)).2.1

theorem ramificationIndex_eq_natDegree_of_isEisensteinAt : ramificationIndex K L = f.natDegree :=
  (isEisensteinAt_root_of_finrank_le hf hn (aeval_integer_eq_zero
    (mem_integer_of_isEisensteinAt hf hα) hα) (finrank_le_of_isEisensteinAt hf hα hgen)).1

theorem irreducible_of_isEisensteinAt_root :
    Irreducible (⟨α, mem_integer_of_isEisensteinAt hf hα⟩ : 𝒪[L]) :=
  (isEisensteinAt_root_of_finrank_le hf hn (aeval_integer_eq_zero
    (mem_integer_of_isEisensteinAt hf hα) hα) (finrank_le_of_isEisensteinAt hf hα hgen)).2.2

end Generated

end Root

section AdjoinRoot

variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]
  {f : 𝒪[K][X]} (hf : f.IsEisensteinAt (IsLocalRing.maximalIdeal 𝒪[K])) (hn : 0 < f.natDegree)
  {α : L} (hα : aeval α f = 0)

include hf hα

include hn

end AdjoinRoot

section Converse

variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]
  (h : ramificationIndex K L = Module.finrank K L) {ϖ : 𝒪[L]} (hϖ : Irreducible ϖ)
include h hϖ

theorem addVal_term_of_totallyRamified (g : 𝒪[K][X]) (i : ℕ) :
    (∀ k, g.coeff i ∈ IsLocalRing.maximalIdeal 𝒪[K] ^ k →
      ((Module.finrank K L * k + i : ℕ) : ℕ∞) ≤
        addVal 𝒪[L] (algebraMap 𝒪[K] 𝒪[L] (g.coeff i) * ϖ ^ i)) ∧
    (IsUnit (g.coeff i) → addVal 𝒪[L] (algebraMap 𝒪[K] 𝒪[L] (g.coeff i) * ϖ ^ i) = i) := by
  have hval : addVal 𝒪[L] (algebraMap 𝒪[K] 𝒪[L] (g.coeff i) * ϖ ^ i) =
      Module.finrank K L * addVal 𝒪[K] (g.coeff i) + i := by
    rw [addVal_mul, addVal_algebraMap_integer, h, hϖ.addVal_pow]
  refine ⟨fun k hk => ?_, fun hu => ?_⟩
  · rw [mem_maximalIdeal_pow_iff_le_addVal] at hk
    rw [hval]
    push_cast
    gcongr
  · rw [hval, addVal_eq_zero_iff.mpr hu, mul_zero, zero_add]

theorem minpoly_isEisensteinAt_of_irreducible :
    (minpoly 𝒪[K] (ϖ : L)).IsEisensteinAt (IsLocalRing.maximalIdeal 𝒪[K]) ∧
      (minpoly 𝒪[K] (ϖ : L)).natDegree = Module.finrank K L := by
  set g := minpoly 𝒪[K] (ϖ : L) with hg_def
  set n := Module.finrank K L with hn_def
  have hint : IsIntegral 𝒪[K] (ϖ : L) := (isIntegral_iff K L _).mpr ϖ.2
  have hmon : g.Monic := minpoly.monic hint
  set d := g.natDegree with hd_def
  have hd0 : 0 < d := minpoly.natDegree_pos hint
  have hmap : minpoly K (ϖ : L) = g.map (algebraMap 𝒪[K] K) :=
    minpoly.isIntegrallyClosed_eq_field_fractions' K hint
  have hdn : d ≤ n := by
    have := minpoly.natDegree_le (A := K) (ϖ : L)
    rwa [hmap, hmon.natDegree_map] at this
  have hn0 : 0 < n := Module.finrank_pos
  have hroot : aeval ϖ g = 0 := by
    have := aeval_integer_eq_zero (f := g) ϖ.2 (minpoly.aeval 𝒪[K] (ϖ : L))
    simpa using this
  set t : ℕ → 𝒪[L] := fun i => algebraMap 𝒪[K] 𝒪[L] (g.coeff i) * ϖ ^ i with ht
  have hsum : ∑ i ∈ Finset.range (d + 1), t i = 0 := by
    rw [← hroot, aeval_eq_sum_range]
    simp [t, Algebra.smul_def, d]
  have hterm := addVal_term_of_totallyRamified h hϖ g
  have hne : ∀ i, IsUnit (g.coeff i) → t i ≠ 0 := by
    intro i hu h0
    have := (hterm i).2 hu
    simp only [t] at h0
    rw [h0, addVal_zero] at this
    exact ENat.top_ne_natCast _ this
  have hlow : ∀ i, ((i : ℕ) : ℕ∞) ≤ addVal 𝒪[L] (t i) := by
    intro i
    have := (hterm i).1 0 (by simp)
    rw [mul_zero, zero_add] at this
    exact this

  have hmem : ∀ i < d, g.coeff i ∈ IsLocalRing.maximalIdeal 𝒪[K] := by
    by_contra hcon
    push Not at hcon
    have hex : ∃ j, j < d ∧ g.coeff j ∉ IsLocalRing.maximalIdeal 𝒪[K] := hcon
    classical
    let j := Nat.find hex
    have hj : j < d ∧ g.coeff j ∉ IsLocalRing.maximalIdeal 𝒪[K] := Nat.find_spec hex
    have hu : IsUnit (g.coeff j) := IsLocalRing.notMem_maximalIdeal.mp hj.2
    refine hne j hu (eq_zero_of_addVal_lt_of_sum_eq_zero hsum
      (Finset.mem_range.mpr (by omega)) fun i hi hij => ?_)
    rw [(hterm j).2 hu]
    rcases lt_or_gt_of_ne hij with hlt | hgt
    · have hi' : g.coeff i ∈ IsLocalRing.maximalIdeal 𝒪[K] := by
        by_contra hc
        exact Nat.find_min hex hlt ⟨by omega, hc⟩
      have := (hterm i).1 1 (by rwa [pow_one])
      refine lt_of_lt_of_le ?_ this
      exact_mod_cast (by omega : j < n * 1 + i)
    · exact lt_of_lt_of_le (by exact_mod_cast hgt) (hlow i)
  have htop : t d = ϖ ^ d := by
    simp only [t]
    rw [show g.coeff d = 1 from hmon]
    simp
  have htop_val : addVal 𝒪[L] (t d) = d := by rw [htop, hϖ.addVal_pow]
  have htop_ne : t d ≠ 0 := by
    rw [htop]
    exact pow_ne_zero _ hϖ.ne_zero

  have hmid : ∀ i, 0 < i → i < d → ((n + 1 : ℕ) : ℕ∞) ≤ addVal 𝒪[L] (t i) := by
    intro i hi0 hid
    have := (hterm i).1 1 (by rw [pow_one]; exact hmem i hid)
    refine le_trans ?_ this
    exact_mod_cast (by omega : n + 1 ≤ n * 1 + i)

  have hsq : g.coeff 0 ∉ IsLocalRing.maximalIdeal 𝒪[K] ^ 2 := by
    intro hc
    refine htop_ne (eq_zero_of_addVal_lt_of_sum_eq_zero hsum (Finset.self_mem_range_succ d)
      fun i hi hid => ?_)
    have hid' : i < d := lt_of_le_of_ne (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)) hid
    rw [htop_val]
    rcases Nat.eq_zero_or_pos i with rfl | hi0
    · refine lt_of_lt_of_le ?_ ((hterm 0).1 2 hc)
      exact_mod_cast (by omega : d < n * 2 + 0)
    · exact lt_of_lt_of_le (by exact_mod_cast (by omega : d < n + 1)) (hmid i hi0 hid')
  have Heisenberg₂ : g.IsEisensteinAt (IsLocalRing.maximalIdeal 𝒪[K]) :=
    { leading := by
        rw [hmon.leadingCoeff]
        exact fun h1 => (IsLocalRing.maximalIdeal.isMaximal 𝒪[K]).ne_top
          ((Ideal.eq_top_iff_one _).mpr h1)
      mem := fun hi => hmem _ hi
      notMem := hsq }
  refine ⟨Heisenberg₂, le_antisymm hdn ?_⟩

  by_contra hlt
  rw [not_le] at hlt
  have h0val : addVal 𝒪[L] (t 0) = n := by
    simp only [t]
    rw [addVal_mul, addVal_algebraMap_integer, h,
      addVal_eq_one_of_mem_of_notMem_sq (hmem 0 hd0) hsq]
    simp
  refine htop_ne (eq_zero_of_addVal_lt_of_sum_eq_zero hsum (Finset.self_mem_range_succ d)
    fun i hi hid => ?_)
  have hid' : i < d := lt_of_le_of_ne (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)) hid
  rw [htop_val]
  rcases Nat.eq_zero_or_pos i with rfl | hi0
  · rw [h0val]
    exact_mod_cast hlt
  · exact lt_of_lt_of_le (by exact_mod_cast (by omega : d < n + 1)) (hmid i hi0 hid')

theorem minpoly_eq_map_of_irreducible :
    minpoly K (ϖ : L) = (minpoly 𝒪[K] (ϖ : L)).map (algebraMap 𝒪[K] K) :=
  minpoly.isIntegrallyClosed_eq_field_fractions' K ((isIntegral_iff K L _).mpr ϖ.2)

theorem adjoin_eq_top_of_irreducible : K⟮(ϖ : L)⟯ = ⊤ := by
  have hint : IsIntegral K (ϖ : L) := ((isIntegral_iff K L _).mpr ϖ.2).tower_top
  refine IntermediateField.eq_of_le_of_finrank_eq le_top ?_
  rw [IntermediateField.finrank_top', IntermediateField.adjoin.finrank hint, minpoly_eq_map_of_irreducible h hϖ,
    (minpoly.monic ((isIntegral_iff K L _).mpr ϖ.2)).natDegree_map]
  exact (minpoly_isEisensteinAt_of_irreducible h hϖ).2

end Converse

end GroundTheory.LocalField
