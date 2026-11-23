import Mathlib

open TensorProduct nonZeroDivisors

namespace GlobalTheory.SepIdem

theorem formallyUnramified_of_isReduced (K A : Type) [Field K] [PerfectField K] [CommRing A]
    [Algebra K A] [Module.Finite K A] [IsReduced A] : Algebra.FormallyUnramified K A := by
  have : IsArtinianRing A := IsArtinianRing.of_finite K A
  have : Finite (MaximalSpectrum A) := inferInstance
  have h : Algebra.FormallyUnramified K (∀ I : MaximalSpectrum A, A ⧸ I.asIdeal) := by
    rw [Algebra.FormallyUnramified.pi_iff]
    intro I
    have := I.isMaximal
    letI := Ideal.Quotient.field I.asIdeal
    exact Algebra.FormallyUnramified.of_isSeparable K _
  exact Algebra.FormallyUnramified.of_equiv ((IsArtinianRing.equivPi A).restrictScalars K).symm

theorem exists_smul_kaehler_eq_zero (O : Type) [CommRing O] [Module.Finite ℤ O] [IsReduced O] :
    ∃ N : ℕ, 0 < N ∧ ∀ ω : Ω[O⁄ℤ], (N : O) • ω = 0 := by
  let A := ℚ ⊗[ℤ] O
  letI : Algebra O A := Algebra.TensorProduct.rightAlgebra
  have hloc : IsLocalization (Algebra.algebraMapSubmonoid O ℤ⁰) A :=
    IsLocalization.tensorRight ℚ ℤ⁰
  have : IsReduced A := isReduced_localizationPreserves (Algebra.algebraMapSubmonoid O ℤ⁰) A inferInstance
  have : Algebra.FormallyUnramified ℚ A := formallyUnramified_of_isReduced ℚ A
  have : Algebra.FormallyUnramified ℤ ℚ := Algebra.FormallyUnramified.of_isLocalization ℤ⁰
  have hA : Algebra.FormallyUnramified ℤ A := Algebra.FormallyUnramified.comp ℤ ℚ A
  have : Algebra.FormallyEtale O A :=
    Algebra.FormallyEtale.of_isLocalization (Algebra.algebraMapSubmonoid O ℤ⁰)
  have hm := KaehlerDifferential.isLocalizedModule_map ℤ O A (Algebra.algebraMapSubmonoid O ℤ⁰)
  have key : ∀ ω : Ω[O⁄ℤ], ∃ n : ℤ, n ≠ 0 ∧ (n : O) • ω = 0 := by
    intro ω
    have h0 : KaehlerDifferential.map ℤ ℤ O A ω = 0 := Subsingleton.elim _ _
    obtain ⟨⟨s, n, hn, rfl⟩, hs⟩ :=
      (IsLocalizedModule.eq_zero_iff (Algebra.algebraMapSubmonoid O ℤ⁰) _).1 h0
    exact ⟨n, nonZeroDivisors.ne_zero hn, by simpa using hs⟩
  obtain ⟨S, hS⟩ := Module.Finite.fg_top (R := O) (M := Ω[O⁄ℤ])
  choose n hn0 hn using key
  refine ⟨∏ x ∈ S, (n x).natAbs, Finset.prod_pos fun x _ => Int.natAbs_pos.2 (hn0 x), ?_⟩
  intro ω
  have hω : ω ∈ Submodule.span O (S : Set Ω[O⁄ℤ]) := hS ▸ Submodule.mem_top
  induction hω using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨k, hk⟩ := Finset.dvd_prod_of_mem (fun x => (n x).natAbs) hx
    obtain ⟨j, hj⟩ : n x ∣ ((n x).natAbs : ℤ) := Int.dvd_natAbs.2 dvd_rfl
    have : (((n x).natAbs : ℕ) : O) = (j : O) * (n x : O) := by
      rw [← Int.cast_natCast, hj]; push_cast; ring
    rw [hk, Nat.cast_mul, this, mul_comm, ← mul_assoc, mul_smul, hn, smul_zero]
  | zero => simp
  | add x y _ _ hx hy => rw [smul_add, hx, hy, add_zero]
  | smul a x _ hx => rw [smul_comm, hx, smul_zero]

theorem exists_separability_element (O : Type) [CommRing O] [Module.Free ℤ O] [Module.Finite ℤ O]
    [IsReduced O] :
    ∃ (N : ℕ) (e : TensorProduct ℤ O O), 0 < N ∧ Algebra.TensorProduct.lmul' ℤ e = (N : O) ∧
      ∀ c : O, (TensorProduct.tmul ℤ c (1 : O) - TensorProduct.tmul ℤ (1 : O) c) * e = 0 := by
  obtain ⟨N, hN, hΩ⟩ := exists_smul_kaehler_eq_zero O
  set I := KaehlerDifferential.ideal ℤ O with hI
  have hfg : I.FG := KaehlerDifferential.ideal_fg ℤ O
  have : Module.Finite (O ⊗[ℤ] O) I := Module.Finite.iff_fg.2 hfg
  have hsq : ∀ x ∈ I, (N : O ⊗[ℤ] O) * x ∈ I ^ 2 := by
    intro x hx
    have h := hΩ (I.toCotangent ⟨x, hx⟩)
    have h2 : I.toCotangent ((N : O ⊗[ℤ] O) • ⟨x, hx⟩) = 0 := by
      rw [Nat.cast_smul_eq_nsmul, map_nsmul]
      exact (Nat.cast_smul_eq_nsmul O N (show Ω[O⁄ℤ] from I.toCotangent ⟨x, hx⟩)).symm.trans h
    exact (Ideal.toCotangent_eq_zero I _).1 h2
  obtain ⟨p, hp, -, hc, h0⟩ :=
    LinearMap.exists_monic_and_natDegree_eq_and_coeff_mem_pow_and_aeval_eq_zero (O ⊗[ℤ] O)
      (algebraMap (O ⊗[ℤ] O) (Module.End (O ⊗[ℤ] O) I) (N : O ⊗[ℤ] O)) I (by
        rintro _ ⟨⟨x, hx⟩, rfl⟩
        rw [Submodule.mem_smul_top_iff, smul_eq_mul, ← pow_two]
        exact hsq x hx)
  rw [Polynomial.aeval_algebraMap_apply] at h0
  refine ⟨N ^ p.natDegree, Polynomial.aeval (N : O ⊗[ℤ] O) p, pow_pos hN _, ?_, fun c => ?_⟩
  · rw [Polynomial.aeval_eq_sum_range, Finset.sum_range_succ, map_add, hp.coeff_natDegree,
      one_smul, map_sum, Finset.sum_eq_zero, zero_add, map_pow, map_natCast, Nat.cast_pow]
    intro k hk
    have : p.coeff k ∈ I :=
      Ideal.pow_le_self (Nat.sub_ne_zero_of_lt (Finset.mem_range.1 hk)) (hc k)
    have h : Algebra.TensorProduct.lmul' ℤ (p.coeff k) = 0 := this
    rw [smul_eq_mul, map_mul, h, zero_mul]
  · have hm := KaehlerDifferential.one_smul_sub_smul_one_mem_ideal ℤ c
    have := congrArg Subtype.val (LinearMap.congr_fun h0 ⟨_, hm⟩)
    have h : Polynomial.aeval (N : O ⊗[ℤ] O) p * ((1 : O) ⊗ₜ[ℤ] c - c ⊗ₜ[ℤ] (1 : O)) = 0 := this
    rw [← neg_sub, neg_mul, mul_comm, h, neg_zero]

end GlobalTheory.SepIdem
