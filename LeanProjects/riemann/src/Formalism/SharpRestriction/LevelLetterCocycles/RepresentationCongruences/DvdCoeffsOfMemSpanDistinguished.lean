import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.MemPairOfMemSingle
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Data.Nat.Choose.Factorization

namespace Formalism.MainNotions.N.FrobeniusPowerSeries

open PowerSeries

section ContMAux

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

theorem ContM_dvd_iff_residue {ϖ : O} (hϖ : Irreducible ϖ) (a : O) :
    ϖ ∣ a ↔ IsLocalRing.residue O a = 0 := by
  rw [IsLocalRing.residue_eq_zero_iff, hϖ.maximalIdeal_eq, Ideal.mem_span_singleton]

theorem ContM_dvd_of_map_eq_zero {ϖ : O} (hϖ : Irreducible ϖ) {a : O⟦X⟧}
    (ha : a.map (IsLocalRing.residue O) = 0) : C ϖ ∣ a := by
  have hc : ∀ n, ϖ ∣ coeff n a := fun n => by
    rw [ContM_dvd_iff_residue hϖ]
    have h := congrArg (coeff n) ha
    rwa [coeff_map, map_zero] at h
  choose b hb using hc
  refine ⟨PowerSeries.mk b, ?_⟩
  ext n
  rw [coeff_C_mul, coeff_mk, hb n]

theorem ContM_map_C_unif {ϖ : O} (hϖ : Irreducible ϖ) :
    (C ϖ : O⟦X⟧).map (IsLocalRing.residue O) = 0 := by
  rw [map_C, (ContM_dvd_iff_residue hϖ ϖ).1 dvd_rfl, map_zero]

theorem ContM_cancel_unif {ϖ : O} (hϖ : Irreducible ϖ) {G : O⟦X⟧} (hG : IsDist G) (k : ℕ) :
    ∀ {x a : O⟦X⟧}, C ϖ ^ k * x = a * G → G ∣ x := by
  induction k with
  | zero =>
    intro x a h
    rw [pow_zero, one_mul] at h
    exact ⟨a, by rw [h, mul_comm]⟩
  | succ k ih =>
    intro x a h
    have hmapC := ContM_map_C_unif hϖ
    have hdvd : C ϖ ∣ a * G := ⟨C ϖ ^ k * x, by rw [← h]; ring⟩
    have hmap0 : (a * G).map (IsLocalRing.residue O) = 0 := by
      obtain ⟨q, hq⟩ := hdvd
      rw [hq, map_mul, hmapC, zero_mul]
    rw [map_mul] at hmap0
    rcases mul_eq_zero.1 hmap0 with ha0 | hG0
    · obtain ⟨a', rfl⟩ := ContM_dvd_of_map_eq_zero hϖ ha0
      apply ih (a := a')
      have hne : (C ϖ : O⟦X⟧) ≠ 0 := by
        intro h0
        apply hϖ.ne_zero
        have h1 := congrArg (coeff 0) h0
        simpa using h1
      apply mul_left_cancel₀ hne
      linear_combination h
    · exact absurd hG0 hG

theorem ContM_mem_of_unif_mul {ϖ : O} (hϖ : Irreducible ϖ) {G : O⟦X⟧} (hG : IsDist G) (k : ℕ)
    {H : O⟦X⟧} (h : C ϖ ^ k * H ∈ Ideal.span {G, C ϖ ^ (k + 1)}) :
    H ∈ Ideal.span {G, C ϖ} := by
  rw [Ideal.mem_span_pair] at h
  obtain ⟨a, b, hab⟩ := h
  have h2 : C ϖ ^ k * (H - b * C ϖ) = a * G := by linear_combination -hab
  obtain ⟨t, ht⟩ := ContM_cancel_unif hϖ hG k h2
  rw [Ideal.mem_span_pair]
  exact ⟨t, b, by linear_combination -ht⟩

theorem ContM_order_unit {K : Type*} [Field K] {w : K⟦X⟧} (hw : IsUnit w) : w.order = 0 := by
  obtain ⟨v, rfl⟩ := hw
  have h := order_mul (v : K⟦X⟧) (↑v⁻¹ : K⟦X⟧)
  rw [Units.mul_inv, order_one] at h
  exact (add_eq_zero.1 h.symm).1

variable [IsAdicComplete (IsLocalRing.maximalIdeal O) O]

theorem dvd_coeffs_of_mem_span_distinguished {ϖ : O} (hϖ : Irreducible ϖ) {Xg : O⟦X⟧} (hX : IsDist Xg) (hD : 1 ≤ wdeg Xg)
    (S : Finset ℕ) (y : ℕ) (hS : ∀ i ∈ S, i < y) (u : ℕ → O⟦X⟧) (hu : ∀ i ∈ S, IsUnit (u i))
    (c : ℕ → O) (h : (∑ i ∈ S, u i * C (c i) * Xg ^ i) ∈ Ideal.span {Xg ^ y, C ϖ}) :
    ∀ i ∈ S, ϖ ∣ c i := by
  classical
  set f := IsLocalRing.residue O with hfdef
  set g := Xg.map f with hgdef
  have hg0 : g ≠ 0 := hX
  have hord : g.order = (wdeg Xg : ℕ∞) := by
    unfold wdeg
    rw [ENat.natCast_toNat]
    exact order_eq_top.not.2 hg0
  have hfϖ : f ϖ = 0 := (ContM_dvd_iff_residue hϖ ϖ).1 dvd_rfl
  rw [Ideal.mem_span_pair] at h
  obtain ⟨a, b, hab⟩ := h
  have himg : (∑ i ∈ S, (u i).map f * C (f (c i)) * g ^ i) = a.map f * g ^ y := by
    have h1 := congrArg (PowerSeries.map f) hab
    simp only [map_add, map_mul, map_pow, map_sum, map_C, hfϖ, map_zero, mul_zero, add_zero] at h1
    exact h1.symm
  intro i hi
  by_contra hnd
  have hT : (S.filter fun i => f (c i) ≠ 0).Nonempty :=
    ⟨i, Finset.mem_filter.2 ⟨hi, fun h0 => hnd ((ContM_dvd_iff_residue hϖ _).2 h0)⟩⟩
  obtain ⟨i₀, hi₀T, hmin⟩ := Finset.exists_min_image _ id hT
  rw [Finset.mem_filter] at hi₀T
  have hlt : i₀ * wdeg Xg < y * wdeg Xg := by nlinarith [hS i₀ hi₀T.1]
  have hL : coeff (i₀ * wdeg Xg) (a.map f * g ^ y) = 0 := by
    apply coeff_of_lt_order
    rw [order_mul, order_pow, hord]
    calc ((i₀ * wdeg Xg : ℕ) : ℕ∞) < ((y * wdeg Xg : ℕ) : ℕ∞) := by exact_mod_cast hlt
      _ = y • (wdeg Xg : ℕ∞) := by
        rw [nsmul_eq_mul]
        push_cast
        rfl
      _ ≤ (a.map f).order + y • (wdeg Xg : ℕ∞) := le_add_self
  have hterm : ∀ i ∈ S, f (c i) ≠ 0 →
      ((u i).map f * C (f (c i)) * g ^ i).order = ((i * wdeg Xg : ℕ) : ℕ∞) := by
    intro i hi hci
    rw [order_mul, order_mul, order_pow, hord, ContM_order_unit ((hu i hi).map (PowerSeries.map f)),
      ContM_order_unit ((isUnit_iff_ne_zero.2 hci).map C), zero_add, zero_add, nsmul_eq_mul]
    push_cast
    rfl
  have hR : coeff (i₀ * wdeg Xg) (∑ i ∈ S, (u i).map f * C (f (c i)) * g ^ i) ≠ 0 := by
    rw [map_sum, Finset.sum_eq_single i₀]
    · have ho := hterm i₀ hi₀T.1 hi₀T.2
      have hne : ((u i₀).map f * C (f (c i₀)) * g ^ i₀) ≠ 0 := by
        intro h0
        rw [h0, order_zero] at ho
        exact ENat.top_ne_natCast _ ho
      have h1 := coeff_order hne
      rwa [ho, ENat.toNat_natCast] at h1
    · intro j hj hne
      by_cases hcj : f (c j) = 0
      · rw [hcj, map_zero, mul_zero, zero_mul, map_zero]
      · apply coeff_of_lt_order
        rw [hterm j hj hcj]
        have hle : i₀ ≤ j := hmin j (Finset.mem_filter.2 ⟨hj, hcj⟩)
        have hlt' : i₀ < j := lt_of_le_of_ne hle (Ne.symm hne)
        have hD' : 1 ≤ wdeg Xg := hD
        exact_mod_cast (by nlinarith : i₀ * wdeg Xg < j * wdeg Xg)
    · intro h0
      exact absurd hi₀T.1 h0
  exact hR (by rw [himg]; exact hL)

theorem ContM_Kk {ϖ : O} (hϖ : Irreducible ϖ) {Xg : O⟦X⟧} (hX : IsDist Xg) (hD : 1 ≤ wdeg Xg)
    (S : Finset ℕ) (y : ℕ) (hS : ∀ i ∈ S, i < y) (u : ℕ → O⟦X⟧) (hu : ∀ i ∈ S, IsUnit (u i)) :
    ∀ (k : ℕ) (c : ℕ → O), (∑ i ∈ S, u i * C (c i) * Xg ^ i) ∈ Ideal.span {Xg ^ y, C ϖ ^ k} →
      ∀ i ∈ S, ϖ ^ k ∣ c i := by
  intro k
  induction k with
  | zero =>
    intro c _ i _
    simp
  | succ k ih =>
    intro c h i hi
    have hle : Ideal.span {Xg ^ y, C ϖ ^ (k + 1)} ≤ Ideal.span {Xg ^ y, (C ϖ : O⟦X⟧) ^ k} := by
      rw [Ideal.span_le]
      intro z hz
      rcases hz with rfl | rfl
      · exact Ideal.subset_span (Set.mem_insert _ _)
      · rw [pow_succ]
        exact Ideal.mul_mem_right _ _ (Ideal.subset_span (Set.mem_insert_of_mem _ rfl))
    have hdk := ih c (hle h)
    choose! c' hc' using hdk
    have hF : (∑ i ∈ S, u i * C (c i) * Xg ^ i) = C ϖ ^ k * ∑ i ∈ S, u i * C (c' i) * Xg ^ i := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      rw [hc' j hj, map_mul, map_pow]
      ring
    rw [hF] at h
    have hXy : IsDist (Xg ^ y) := by
      show (Xg ^ y).map _ ≠ 0
      rw [map_pow]
      exact pow_ne_zero _ hX
    have h1 := ContM_mem_of_unif_mul hϖ hXy k h
    obtain ⟨e, he⟩ := dvd_coeffs_of_mem_span_distinguished hϖ hX hD S y hS u hu c' h1 i hi
    rw [hc' i hi, he]
    exact ⟨e, by ring⟩

theorem ContM_iSup_le (m : ℕ∞) : ⨆ (k : ℕ) (_ : (k : ℕ∞) ≤ m), (k : ℕ∞) = m := by
  apply le_antisymm
  · exact iSup₂_le fun k hk => hk
  · exact Cont.enat_le_of_forall fun k hk => le_iSup₂_of_le k hk le_rfl

end ContMAux

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
variable {ϖ : O} (hϖ : Irreducible ϖ)
include hϖ

theorem Mprime {Xg : O⟦X⟧} (hX : IsDist Xg) (hD : 1 ≤ wdeg Xg) (I : Finset ℕ)
    (u : ℕ → O⟦X⟧) (hu : ∀ i ∈ I, IsUnit (u i)) (c : ℕ → O) (hc : ∀ i ∈ I, c i ≠ 0) (y k : ℕ) :
    (∑ i ∈ I, u i * C (c i) * Xg ^ i) ∈ Ideal.span {Xg ^ y, C ϖ ^ k} ↔
      ∀ i ∈ I, i < y → (k : ℕ∞) ≤ IsDiscreteValuationRing.addVal O (c i) := by
  classical
  have hdv : ∀ i, ((k : ℕ∞) ≤ IsDiscreteValuationRing.addVal O (c i) ↔ ϖ ^ k ∣ c i) := by
    intro i
    rw [← IsDiscreteValuationRing.addVal_le_iff_dvd, IsDiscreteValuationRing.addVal_pow,
      IsDiscreteValuationRing.addVal_uniformizer hϖ, nsmul_one]
  have hbig : ∀ i, y ≤ i → u i * C (c i) * Xg ^ i ∈ Ideal.span {Xg ^ y, (C ϖ : O⟦X⟧) ^ k} := by
    intro i hi
    have hpow : Xg ^ i = Xg ^ y * Xg ^ (i - y) := by
      rw [← pow_add]
      congr 1
      omega
    rw [hpow]
    exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_right _ _ (Ideal.subset_span (Set.mem_insert _ _)))
  constructor
  · intro h i hi hiy
    rw [hdv]
    have hsplit : (∑ j ∈ I.filter (· < y), u j * C (c j) * Xg ^ j) ∈
        Ideal.span {Xg ^ y, (C ϖ : O⟦X⟧) ^ k} := by
      have heq := Finset.sum_filter_add_sum_filter_not I (· < y) (fun j => u j * C (c j) * Xg ^ j)
      have hnot : (∑ j ∈ I.filter (fun j => ¬ j < y), u j * C (c j) * Xg ^ j) ∈
          Ideal.span {Xg ^ y, (C ϖ : O⟦X⟧) ^ k} := by
        apply Ideal.sum_mem
        intro j hj
        rw [Finset.mem_filter] at hj
        exact hbig j (by omega)
      have h3 : (∑ j ∈ I.filter (· < y), u j * C (c j) * Xg ^ j) =
          (∑ j ∈ I, u j * C (c j) * Xg ^ j) - ∑ j ∈ I.filter (fun j => ¬ j < y), u j * C (c j) * Xg ^ j := by
        rw [← heq, add_sub_cancel_right]
      rw [h3]
      exact Ideal.sub_mem _ h hnot
    exact ContM_Kk hϖ hX hD (I.filter (· < y)) y (fun j hj => (Finset.mem_filter.1 hj).2) u
      (fun j hj => hu j (Finset.mem_filter.1 hj).1) k c hsplit i (Finset.mem_filter.2 ⟨hi, hiy⟩)
  · intro h
    apply Ideal.sum_mem
    intro i hi
    by_cases hiy : i < y
    · obtain ⟨e, he⟩ := (hdv i).1 (h i hi hiy)
      rw [he, map_mul, map_pow]
      have hmem : (C ϖ : O⟦X⟧) ^ k ∈ Ideal.span {Xg ^ y, (C ϖ : O⟦X⟧) ^ k} :=
        Ideal.subset_span (Set.mem_insert_of_mem _ rfl)
      have h4 : u i * (C ϖ ^ k * C e) * Xg ^ i = C ϖ ^ k * (u i * C e * Xg ^ i) := by ring
      rw [h4]
      exact Ideal.mul_mem_right _ _ hmem
    · exact hbig i (by omega)

theorem Mprime_cont {Xg : O⟦X⟧} (hX : IsDist Xg) (hD : 1 ≤ wdeg Xg) (I : Finset ℕ)
    (u : ℕ → O⟦X⟧) (hu : ∀ i ∈ I, IsUnit (u i)) (c : ℕ → O) (hc : ∀ i ∈ I, c i ≠ 0) (y : ℕ) :
    cont ϖ (Xg ^ y) (∑ i ∈ I, u i * C (c i) * Xg ^ i) =
      ⨅ i ∈ I.filter (· < y), IsDiscreteValuationRing.addVal O (c i) := by
  unfold cont
  have hm : ∀ k : ℕ, (∑ i ∈ I, u i * C (c i) * Xg ^ i) ∈ Ideal.span {C ϖ ^ k, Xg ^ y} ↔
      (k : ℕ∞) ≤ ⨅ i ∈ I.filter (· < y), IsDiscreteValuationRing.addVal O (c i) := by
    intro k
    rw [Set.pair_comm, Mprime hϖ hX hD I u hu c hc y k, le_iInf₂_iff]
    simp only [Finset.mem_filter]
    constructor
    · intro h i hi
      exact h i hi.1 hi.2
    · intro h i hi hiy
      exact h i ⟨hi, hiy⟩
  simp_rw [hm]
  exact ContM_iSup_le _

end Formalism.MainNotions.N.FrobeniusPowerSeries
