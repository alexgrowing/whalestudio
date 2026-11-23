import Mathlib
import Formalism.HermitianLattices.StatementLat

noncomputable section

namespace Formalism.HermitianLatticesTheory

theorem exampleZ_mem_one (x : ℚ) : x ∈ (1 : Submodule ℤ ℚ) ↔ ∃ n : ℤ, (n : ℚ) = x := by
  rw [Submodule.mem_one]
  simp

theorem exampleZ_mem_span (c x : ℚ) : x ∈ Submodule.span ℤ {c} ↔ ∃ n : ℤ, (n : ℚ) * c = x := by
  rw [Submodule.mem_span_singleton]
  simp [zsmul_eq_mul]

theorem exampleZ_mem_dual (h : ℚ →ₗ⋆[ℚ] ℚ →ₗ[ℚ] ℚ) (L : Submodule ℤ ℚ) (x : ℚ) :
    x ∈ dual h L ↔ ∀ y ∈ L, h y x ∈ (1 : Submodule ℤ ℚ) := by
  unfold dual Formalism.E.hdual
  simp only [Submodule.mem_iInf, Submodule.mem_comap, LinearMap.coe_restrictScalars]

theorem exampleZ_mem_locP (p : Ideal ℤ) [p.IsPrime] (L : Submodule ℤ ℚ) (x : ℚ) :
    x ∈ localization₂ p L ↔ ∃ s : ℤ, s ∉ p ∧ (s : ℚ) * x ∈ L := by
  unfold localization₂ locS
  change (∃ s ∈ p.primeCompl, s • x ∈ L) ↔ _
  simp [zsmul_eq_mul, Ideal.primeCompl]

theorem exampleZ_len_top {M : Type*} [AddCommGroup M] [Module ℤ M] (N : Submodule ℤ M)
    (hN : N = ⊤) : (Module.length ℤ (M ⧸ N)).toNat = 0 := by
  subst hN
  rw [Module.length_eq_zero_iff.mpr inferInstance]
  rfl

theorem exampleZ_odd {s : ℤ} (hs : s ∉ Ideal.span {(2 : ℤ)}) : Odd s := by
  rw [Ideal.mem_span_singleton, ← even_iff_two_dvd, Int.not_even_iff_odd] at hs
  exact hs

theorem exampleZ_not_mem_of_odd {s : ℤ} (hs : Odd s) : s ∉ Ideal.span {(2 : ℤ)} := by
  rw [Ideal.mem_span_singleton, ← even_iff_two_dvd, Int.not_even_iff_odd]
  exact hs

theorem exampleZ_two_le : Submodule.span ℤ {(2 : ℚ)} ≤ (1 : Submodule ℤ ℚ) := by
  rw [Submodule.span_le, Set.singleton_subset_iff]
  exact (exampleZ_mem_one 2).mpr ⟨2, by norm_num⟩

theorem exampleZ_inf : (1 : Submodule ℤ ℚ) ⊓ Submodule.span ℤ {(2 : ℚ)} =
    Submodule.span ℤ {(2 : ℚ)} := inf_of_le_right exampleZ_two_le

theorem exampleZ_coatom (p : Ideal ℤ) [p.IsPrime] (hp : p = Ideal.span {2}) :
    IsCoatom ((localization₂ p (Submodule.span ℤ {(2 : ℚ)})).comap (localization₂ p (1 : Submodule ℤ ℚ)).subtype) := by
  have memL : ∀ (L : Submodule ℤ ℚ) (x : ℚ), x ∈ localization₂ p L ↔ ∃ s : ℤ, Odd s ∧ (s : ℚ) * x ∈ L := by
    intro L x
    rw [exampleZ_mem_locP, hp]
    constructor
    · rintro ⟨s, hs, h⟩; exact ⟨s, exampleZ_odd hs, h⟩
    · rintro ⟨s, hs, h⟩; exact ⟨s, exampleZ_not_mem_of_odd hs, h⟩
  constructor
  · intro htop
    have h1 : (1 : ℚ) ∈ localization₂ p (1 : Submodule ℤ ℚ) :=
      (memL _ _).mpr ⟨1, odd_one, (exampleZ_mem_one _).mpr ⟨1, by norm_num⟩⟩
    have h2 : (⟨1, h1⟩ : localization₂ p (1 : Submodule ℤ ℚ)) ∈
        (localization₂ p (Submodule.span ℤ {(2 : ℚ)})).comap (localization₂ p (1 : Submodule ℤ ℚ)).subtype := by
      rw [htop]; trivial
    rw [Submodule.mem_comap] at h2
    obtain ⟨s, hs, h⟩ := (memL _ _).mp h2
    obtain ⟨n, hn⟩ := (exampleZ_mem_span _ _).mp h
    simp only [Submodule.coe_subtype, mul_one] at hn
    have : n * 2 = s := by exact_mod_cast hn
    obtain ⟨k, hk⟩ := hs
    omega
  · intro b hb
    obtain ⟨x, hxb, hxN⟩ := SetLike.exists_of_lt hb
    rw [Submodule.mem_comap, Submodule.coe_subtype, memL] at hxN
    obtain ⟨t, ht, hx⟩ := (memL _ _).mp x.2
    obtain ⟨m, hm⟩ := (exampleZ_mem_one _).mp hx
    have hmodd : Odd m := by
      rw [← Int.not_even_iff_odd]
      rintro ⟨j, hj⟩
      apply hxN
      refine ⟨t, ht, (exampleZ_mem_span _ _).mpr ⟨j, ?_⟩⟩
      rw [← hm, hj]; push_cast; ring
    rw [eq_top_iff]
    intro y _
    obtain ⟨u, hu, hy⟩ := (memL _ _).mp y.2
    obtain ⟨k, hk⟩ := (exampleZ_mem_one _).mp hy
    rcases Int.even_or_odd k with ⟨j, hj⟩ | hkodd
    · apply hb.le
      rw [Submodule.mem_comap, Submodule.coe_subtype, memL]
      refine ⟨u, hu, (exampleZ_mem_span _ _).mpr ⟨j, ?_⟩⟩
      rw [← hk, hj]; push_cast; ring
    · have hev : Even (t * k - u * m) := Odd.sub_odd (ht.mul hkodd) (hu.mul hmodd)
      obtain ⟨j, hj⟩ := hev
      have hj' : ((t : ℚ) * k - u * m) = j + j := by exact_mod_cast hj
      have hyx : y - x ∈ (localization₂ p (Submodule.span ℤ {(2 : ℚ)})).comap
          (localization₂ p (1 : Submodule ℤ ℚ)).subtype := by
        rw [Submodule.mem_comap, Submodule.coe_subtype, memL]
        refine ⟨t * u, ht.mul hu, (exampleZ_mem_span _ _).mpr ⟨j, ?_⟩⟩
        simp only [Submodule.coe_sub]
        push_cast
        linear_combination (u : ℚ) * hm.symm - (t : ℚ) * hk.symm - hj'
      have := b.add_mem (hb.le hyx) hxb
      simpa using this

theorem exampleZ_all (p : Ideal ℤ) [p.IsPrime] (hp : p = Ideal.span {3}) :
    (localization₂ p (Submodule.span ℤ {(2 : ℚ)})).comap (localization₂ p (1 : Submodule ℤ ℚ)).subtype = ⊤ := by
  rw [eq_top_iff]
  intro x _
  rw [Submodule.mem_comap, Submodule.coe_subtype, exampleZ_mem_locP]
  obtain ⟨s, hs, hx⟩ := (exampleZ_mem_locP _ _ _).mp x.2
  obtain ⟨n, hn⟩ := (exampleZ_mem_one _).mp hx
  have h2 : (2 : ℤ) ∉ p := by
    rw [hp, Ideal.mem_span_singleton]; decide
  refine ⟨2 * s, fun h => (Ideal.IsPrime.mem_or_mem ‹_› h).elim h2 hs,
    (exampleZ_mem_span _ _).mpr ⟨n, ?_⟩⟩
  push_cast
  rw [mul_assoc, ← hn]; ring

theorem exampleZ_len_self (p : Ideal ℤ) [p.IsPrime] (B : Submodule ℤ ℚ) :
    locLen p B B = 0 := by
  unfold locLen
  exact exampleZ_len_top _ (Submodule.comap_subtype_self _)

theorem exampleZ : ExampleZ := by
  intro h hh
  have hd : ∀ (L : Submodule ℤ ℚ) (x : ℚ), x ∈ dual h L ↔ ∀ y ∈ L, y * x ∈ (1 : Submodule ℤ ℚ) := by
    intro L x
    rw [exampleZ_mem_dual]
    simp only [hh]
  have hdual2 : dual h (Submodule.span ℤ {(2 : ℚ)}) = Submodule.span ℤ {(1 / 2 : ℚ)} := by
    ext x
    rw [hd, exampleZ_mem_span]
    constructor
    · intro H
      obtain ⟨n, hn⟩ := (exampleZ_mem_one _).mp (H 2 (Submodule.mem_span_singleton_self _))
      exact ⟨n, by rw [hn]; ring⟩
    · rintro ⟨n, rfl⟩ y hy
      obtain ⟨m, rfl⟩ := (exampleZ_mem_span _ _).mp hy
      exact (exampleZ_mem_one _).mpr ⟨m * n, by push_cast; ring⟩
  refine ⟨?_, ?_, ?_, hdual2, ?_, ?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · rw [Submodule.one_eq_span]; exact Submodule.fg_span_singleton _
    · rw [eq_top_iff]
      intro x _
      have h1 : (1 : ℚ) ∈ ((1 : Submodule ℤ ℚ) : Set ℚ) := (exampleZ_mem_one _).mpr ⟨1, by norm_num⟩
      have := Submodule.smul_mem (Submodule.span ℚ ((1 : Submodule ℤ ℚ) : Set ℚ)) x
        (Submodule.subset_span h1)
      simpa using this
  · unfold IsUnimodular
    ext x
    rw [hd]
    constructor
    · intro H
      simpa using H 1 ((exampleZ_mem_one _).mpr ⟨1, by norm_num⟩)
    · intro hx y hy
      obtain ⟨n, rfl⟩ := (exampleZ_mem_one _).mp hy
      obtain ⟨m, rfl⟩ := (exampleZ_mem_one _).mp hx
      exact (exampleZ_mem_one _).mpr ⟨n * m, by push_cast; ring⟩
  · intro x hx y hy
    rw [hh]
    obtain ⟨n, rfl⟩ := (exampleZ_mem_span _ _).mp hx
    obtain ⟨m, rfl⟩ := (exampleZ_mem_span _ _).mp hy
    exact (exampleZ_mem_one _).mpr ⟨n * 2 * (m * 2), by push_cast; ring⟩
  · intro H
    unfold IsUnimodular at H
    rw [hdual2] at H
    have : (1 / 2 : ℚ) ∈ Submodule.span ℤ {(2 : ℚ)} := by
      rw [← H]; exact Submodule.mem_span_singleton_self _
    obtain ⟨n, hn⟩ := (exampleZ_mem_span _ _).mp this
    have h4 : (n : ℚ) * 4 = 1 := by linear_combination 2 * hn
    have h4' : n * 4 = 1 := by exact_mod_cast h4
    omega
  · intro p _ hp
    unfold lidx
    rw [exampleZ_inf, exampleZ_len_self]
    unfold locLen
    rw [Module.length_eq_one_iff.mpr ((isSimpleModule_iff_isCoatom).mpr (exampleZ_coatom p hp))]
    rfl
  · intro p _ hp
    unfold lidx
    rw [exampleZ_inf, exampleZ_len_self]
    unfold locLen
    rw [exampleZ_len_top _ (exampleZ_all p hp)]
    rfl

end Formalism.HermitianLatticesTheory
