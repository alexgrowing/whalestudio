import Mathlib
import Formalism.FrobeniusOrbits.Statement
import Formalism.TameInertiaTowers.CentralOrderTwo.OddEqOneOfSubOneMem
import Formalism.TameInertiaTowers.CentralOrderTwo.DecompositionSubgroupIndex

open NumberField IntermediateField Ideal
open scoped Pointwise

noncomputable section

namespace Formalism.FrobeniusOrbits.SplitK

open Formalism.TwoAdicCyclotomicDecomposition

variable {L : Type} [Field L] [NumberField L] {b : L} {d : ℕ}

def bK (b : L) : Kd b := ⟨b, mem_adjoin_simple_self ℚ b⟩

theorem bK_sq (hb : b ^ 2 = -(d : L)) : bK b ^ 2 = -(d : Kd b) := by
  first
  | exact Subtype.ext (by simp [bK, hb])
  | (apply Subtype.ext; simp [bK, hb])
  | (apply Subtype.ext; push_cast [bK]; exact hb)

theorem b_not_rat (hd : 0 < d) (hb : b ^ 2 = -(d : L)) : b ∉ (⊥ : IntermediateField ℚ L) := by
  intro h
  rw [IntermediateField.mem_bot] at h
  obtain ⟨q, hq⟩ := h
  have key : (algebraMap ℚ L) (q ^ 2) = (algebraMap ℚ L) (-(d : ℚ)) := by
    rw [map_pow, hq, hb, map_neg, map_natCast]
  have h2 : q ^ 2 = -(d : ℚ) := (algebraMap ℚ L).injective key
  have h3 : (0 : ℚ) < d := by exact_mod_cast hd
  nlinarith [sq_nonneg q]

private theorem isIntegral_b : IsIntegral ℚ b := by
  first
  | exact IsIntegral.of_finite ℚ b
  | exact Algebra.IsIntegral.isIntegral b

private theorem aeval_X_sq_add_C_eq_zero_of_sq_eq_neg (hb : b ^ 2 = -(d : L)) :
    Polynomial.aeval b (Polynomial.X ^ 2 + Polynomial.C (d : ℚ)) = 0 := by
  first
  | simp [hb]
  | (rw [map_add, map_pow, Polynomial.aeval_X, Polynomial.aeval_C, hb]; simp)

private theorem minpoly_natDegree_eq_two_of_sq_eq_neg (hd : 0 < d) (hb : b ^ 2 = -(d : L)) :
    (minpoly ℚ b).natDegree = 2 := by
  have hint : IsIntegral ℚ b := isIntegral_b
  have hmon : (Polynomial.X ^ 2 + Polynomial.C (d : ℚ)).Monic := by
    first
    | exact Polynomial.monic_X_pow_add_C _ two_ne_zero
    | monicity!
  have hle : (minpoly ℚ b).natDegree ≤ 2 := by
    have h1 := Polynomial.natDegree_le_of_dvd (minpoly.dvd ℚ b (aeval_X_sq_add_C_eq_zero_of_sq_eq_neg hb)) hmon.ne_zero
    first
    | rwa [Polynomial.natDegree_X_pow_add_C] at h1
    | exact h1.trans (by compute_degree)
  have hne1 : (minpoly ℚ b).natDegree ≠ 1 := by
    intro h1
    first
    | (rw [minpoly.natDegree_eq_one_iff] at h1; obtain ⟨q, hq⟩ := h1; exact b_not_rat hd hb (IntermediateField.mem_bot.mpr ⟨q, hq⟩))
    | (have h2 : Module.finrank ℚ ℚ⟮b⟯ = 1 := by rw [IntermediateField.adjoin.finrank hint, h1]
       exact b_not_rat hd hb (IntermediateField.adjoin_simple_eq_bot_iff.mp (IntermediateField.finrank_eq_one_iff.mp h2)))
  have hpos := minpoly.natDegree_pos hint
  omega

theorem finrank_K (hd : 0 < d) (hb : b ^ 2 = -(d : L)) : Module.finrank ℚ (Kd b) = 2 := by
  show Module.finrank ℚ ℚ⟮b⟯ = 2
  rw [IntermediateField.adjoin.finrank isIntegral_b, minpoly_natDegree_eq_two_of_sq_eq_neg hd hb]

theorem quad_K (hd : 0 < d) (hb : b ^ 2 = -(d : L)) : Algebra.IsQuadraticExtension ℚ (Kd b) := by
  first
  | exact ⟨finrank_K hd hb⟩
  | exact { finrank_eq_two' := finrank_K hd hb }
  | exact { toFree := inferInstance, finrank_eq_two' := finrank_K hd hb }
  | (constructor <;> first | exact finrank_K hd hb | exact inferInstance)

private theorem Kd_algEquiv_ext_of_apply_bK_eq (σ τ : Kd b ≃ₐ[ℚ] Kd b) (h : σ (bK b) = τ (bK b)) : σ = τ := by
  have hint : IsIntegral ℚ b := isIntegral_b
  have key : (σ : Kd b →ₐ[ℚ] Kd b) = (τ : Kd b →ₐ[ℚ] Kd b) := by
    apply (IntermediateField.adjoin.powerBasis hint).algHom_ext
    first
    | exact h
    | (rw [IntermediateField.adjoin.powerBasis_gen]; exact h)
    | (simp only [IntermediateField.adjoin.powerBasis_gen, AlgEquiv.coe_algHom]; exact h)
  exact AlgEquiv.ext fun x => AlgHom.congr_fun key x

theorem gal_eq_one_of_fix (σ : Kd b ≃ₐ[ℚ] Kd b) (h : σ (bK b) = bK b) : σ = 1 := by
  apply Kd_algEquiv_ext_of_apply_bK_eq σ 1
  first
  | (rw [h]; rfl)
  | simpa using h
  | (rw [AlgEquiv.one_apply]; exact h)

private theorem Kd_algEquiv_bK_eq_or_eq_neg (hb : b ^ 2 = -(d : L)) (σ : Kd b ≃ₐ[ℚ] Kd b) :
    σ (bK b) = bK b ∨ σ (bK b) = -bK b := by
  have h1 : σ (bK b) ^ 2 = bK b ^ 2 := by
    first
    | rw [← map_pow, bK_sq hb, map_neg, map_natCast]
    | (rw [← map_pow, bK_sq hb]; simp)
  have h2 : (σ (bK b) - bK b) * (σ (bK b) + bK b) = 0 := by linear_combination h1
  rcases mul_eq_zero.mp h2 with h | h
  · left
    linear_combination h
  · right
    linear_combination h

private theorem minpoly_eq_X_sq_add_C_of_sq_eq_neg (hd : 0 < d) (hb : b ^ 2 = -(d : L)) :
    minpoly ℚ b = Polynomial.X ^ 2 + Polynomial.C (d : ℚ) := by
  have hint : IsIntegral ℚ b := isIntegral_b
  have hmon : (Polynomial.X ^ 2 + Polynomial.C (d : ℚ)).Monic := by
    first
    | exact Polynomial.monic_X_pow_add_C _ two_ne_zero
    | monicity!
  obtain ⟨r, hr⟩ := minpoly.dvd ℚ b (aeval_X_sq_add_C_eq_zero_of_sq_eq_neg hb)
  have hr0 : r ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hr
    exact hmon.ne_zero hr
  have hdeg := congrArg Polynomial.natDegree hr
  rw [(minpoly.monic hint).natDegree_mul' hr0, Polynomial.natDegree_X_pow_add_C,
    minpoly_natDegree_eq_two_of_sq_eq_neg hd hb] at hdeg
  have hrm : r.Monic := (minpoly.monic hint).of_mul_monic_left (hr ▸ hmon)
  have hr0d : r.natDegree = 0 := by omega
  have hr1 : r = 1 := by
    first
    | exact (Polynomial.Monic.natDegree_eq_zero hrm).mp hr0d
    | exact Polynomial.eq_one_of_monic_natDegree_zero hrm hr0d
    | (rw [Polynomial.eq_C_of_natDegree_eq_zero hr0d]; have h5 := hrm.leadingCoeff; rw [Polynomial.leadingCoeff, hr0d] at h5; rw [h5, map_one])
  rw [hr, hr1, mul_one]

private theorem Kd_exists_algEquiv_bK_eq_neg (hd : 0 < d) (hb : b ^ 2 = -(d : L)) :
    ∃ σ : Kd b ≃ₐ[ℚ] Kd b, σ (bK b) = -bK b := by
  have hint : IsIntegral ℚ b := isIntegral_b
  set pb : PowerBasis ℚ (Kd b) := IntermediateField.adjoin.powerBasis hint with hpb
  have hgen : pb.gen = bK b := by
    first
    | rfl
    | (rw [hpb, IntermediateField.adjoin.powerBasis_gen]; rfl)
  have hmin : minpoly ℚ pb.gen = minpoly ℚ b := by
    first
    | exact (minpoly.algebraMap_eq (algebraMap (Kd b) L).injective pb.gen).symm
    | exact IntermediateField.minpoly_eq pb.gen
    | (rw [hpb, IntermediateField.adjoin.powerBasis_gen]; exact IntermediateField.minpoly_gen b)
    | (rw [hpb, IntermediateField.adjoin.powerBasis_gen]; exact IntermediateField.minpoly_gen ℚ b)
  have hroot : Polynomial.aeval (-pb.gen) (minpoly ℚ pb.gen) = 0 := by
    rw [hmin, minpoly_eq_X_sq_add_C_of_sq_eq_neg hd hb, hgen]
    first
    | (simp only [map_add, map_pow, Polynomial.aeval_X, Polynomial.aeval_C, map_natCast]; linear_combination bK_sq hb)
    | (simp; linear_combination bK_sq hb)
    | (simp; rw [neg_sq, bK_sq hb]; ring)
    | (simp only [map_add, map_pow, Polynomial.aeval_X, Polynomial.aeval_C]; rw [neg_sq, bK_sq hb]; simp)
  have hbij : Function.Bijective (pb.lift (-pb.gen) hroot) := by
    first
    | exact AlgHom.bijective _
    | exact ⟨(pb.lift (-pb.gen) hroot).toRingHom.injective,
        LinearMap.injective_iff_surjective.mp (pb.lift (-pb.gen) hroot).toRingHom.injective⟩
  refine ⟨AlgEquiv.ofBijective _ hbij, ?_⟩
  have hl : pb.lift (-pb.gen) hroot (bK b) = -bK b := by
    rw [← hgen]
    exact pb.lift_gen _ hroot
  first
  | exact hl
  | (rw [AlgEquiv.ofBijective_apply]; exact hl)

private theorem bK_ne_neg_bK_of_sq_eq_neg (hd : 0 < d) (hb : b ^ 2 = -(d : L)) : bK b ≠ -bK b := by
  intro h
  have h2 : b = -b := by
    first
    | exact congrArg Subtype.val h
    | simpa [bK] using congrArg Subtype.val h
  have h3 : b = 0 := by
    have h4 : (2 : L) * b = 0 := by linear_combination h2
    rcases mul_eq_zero.mp h4 with h5 | h5
    · norm_num at h5
    · exact h5
  rw [h3] at hb
  have h6 : (d : L) = 0 := by linear_combination hb
  have h7 : d = 0 := by exact_mod_cast h6
  omega

theorem card_gal (hd : 0 < d) (hb : b ^ 2 = -(d : L)) : Nat.card (Kd b ≃ₐ[ℚ] Kd b) = 2 := by
  obtain ⟨τ, hτ⟩ := Kd_exists_algEquiv_bK_eq_neg hd hb
  have hne := bK_ne_neg_bK_of_sq_eq_neg hd hb
  let f : (Kd b ≃ₐ[ℚ] Kd b) → ({bK b, -bK b} : Set (Kd b)) := fun σ =>
    ⟨σ (bK b), by rcases Kd_algEquiv_bK_eq_or_eq_neg hb σ with h | h <;> simp [h]⟩
  have hinj : Function.Injective f := fun σ σ' h => Kd_algEquiv_ext_of_apply_bK_eq σ σ' (congrArg Subtype.val h)
  haveI : Finite (Kd b ≃ₐ[ℚ] Kd b) := Finite.of_injective f hinj
  have hτ1 : τ ≠ 1 := by
    intro h1
    apply hne
    rw [h1] at hτ
    first | exact hτ | simpa using hτ
  haveI : Nontrivial (Kd b ≃ₐ[ℚ] Kd b) := ⟨⟨τ, 1, hτ1⟩⟩
  apply le_antisymm
  · calc Nat.card (Kd b ≃ₐ[ℚ] Kd b) ≤ Nat.card ({bK b, -bK b} : Set (Kd b)) :=
          Nat.card_le_card_of_injective f hinj
      _ = 2 := by
        first
        | rw [Nat.card_coe_set_eq, Set.ncard_pair hne]
        | (rw [← Set.ncard_pair hne]; rfl)
        | (rw [← Set.ncard_pair hne, Set.ncard_def]; simp)
        | (rw [← Set.ncard_pair hne]; exact (Set.ncard_eq_toFinset_card' _).symm.trans (by simp))
  · exact Finite.one_lt_card

theorem bK_sq_int (hb : b ^ 2 = -(d : L)) : bK b ^ 2 = ((-(d : ℤ) : ℤ) : Kd b) := by
  rw [bK_sq hb]
  first
  | simp
  | (push_cast; rfl)
  | norm_num

theorem bK_ne_zero (hd0 : 0 < d) (hb : b ^ 2 = -(d : L)) : bK b ≠ 0 := by
  intro h
  apply bK_ne_neg_bK_of_sq_eq_neg hd0 hb
  rw [h, neg_zero]

theorem exists_ne_one (hd0 : 0 < d) (hb : b ^ 2 = -(d : L)) : ∃ ι : Kd b ≃ₐ[ℚ] Kd b, ι ≠ 1 := by
  obtain ⟨τ, hτ⟩ := Kd_exists_algEquiv_bK_eq_neg hd0 hb
  refine ⟨τ, fun h1 => bK_ne_neg_bK_of_sq_eq_neg hd0 hb ?_⟩
  rw [h1] at hτ
  first | exact hτ | simpa using hτ

theorem apply_bK_of_ne (hd0 : 0 < d) (hb : b ^ 2 = -(d : L)) (ι : Kd b ≃ₐ[ℚ] Kd b) (hι : ι ≠ 1) :
    ι (bK b) = -bK b := by
  rcases Kd_algEquiv_bK_eq_or_eq_neg hb ι with h | h
  · exact absurd (gal_eq_one_of_fix ι h) hι
  · exact h

theorem eq_of_ne_one (hd0 : 0 < d) (hb : b ^ 2 = -(d : L)) (σ τ : Kd b ≃ₐ[ℚ] Kd b) (hσ : σ ≠ 1)
    (hτ : τ ≠ 1) : σ = τ := by
  apply Kd_algEquiv_ext_of_apply_bK_eq
  rw [apply_bK_of_ne hd0 hb σ hσ, apply_bK_of_ne hd0 hb τ hτ]

theorem span_prime (p : ℕ) [hp : Fact p.Prime] : (span {(p : ℤ)}).IsPrime := by
  first
  | exact (Ideal.span_singleton_prime (by exact_mod_cast hp.out.ne_zero)).mpr (Nat.prime_iff_prime_int.mp hp.out)
  | exact (Int.ideal_span_isMaximal_of_prime p).isPrime
  | exact inferInstance

private theorem Kd_isGalois_of_sq_eq_neg (hd : 0 < d) (hb : b ^ 2 = -(d : L)) : IsGalois ℚ (Kd b) := by
  first
  | exact IsGalois.of_card_aut_eq_finrank (by rw [card_gal hd hb, finrank_K hd hb])
  | exact IsGalois.of_card_aut_eq_finrank ℚ (Kd b) (by rw [card_gal hd hb, finrank_K hd hb])
  | (haveI := quad_K hd hb; exact inferInstance)

theorem fund (hd0 : 0 < d) (hb : b ^ 2 = -(d : L)) (p : ℕ) [Fact p.Prime]
    (P : Ideal (𝓞 (Kd b))) [P.IsPrime] [P.LiesOver (span {(p : ℤ)})] :
    (primesOver (span {(p : ℤ)}) (𝓞 (Kd b))).ncard * (P.ramificationIdx ℤ * P.inertiaDeg ℤ) = 2 := by
  haveI : NumberField (Kd b) := by
    first
    | exact inferInstance
    | exact NumberField.mk
    | exact ⟨⟩
  haveI : IsGalois ℚ (Kd b) := Kd_isGalois_of_sq_eq_neg hd0 hb
  haveI : Finite (Kd b ≃ₐ[ℚ] Kd b) := Nat.finite_of_card_ne_zero (by rw [card_gal hd0 hb]; norm_num)
  haveI := span_prime p
  have h := Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn (span {(p : ℤ)})
    (𝓞 (Kd b)) (Kd b ≃ₐ[ℚ] Kd b)
  rw [Ideal.ramificationIdxIn_eq_ramificationIdx (span {(p : ℤ)}) P (Kd b ≃ₐ[ℚ] Kd b),
    Ideal.inertiaDegIn_eq_inertiaDeg (span {(p : ℤ)}) P (Kd b ≃ₐ[ℚ] Kd b), card_gal hd0 hb] at h
  exact h

theorem ncard_one (hd0 : 0 < d) (hb : b ^ 2 = -(d : L)) (p : ℕ) [Fact p.Prime]
    (P : Ideal (𝓞 (Kd b))) [P.IsPrime] [P.LiesOver (span {(p : ℤ)})]
    (h : ∀ σ : Kd b ≃ₐ[ℚ] Kd b, σ • P = P) :
    (primesOver (span {(p : ℤ)}) (𝓞 (Kd b))).ncard = 1 := by
  haveI : NumberField (Kd b) := by
    first
    | exact inferInstance
    | exact NumberField.mk
    | exact ⟨⟩
  haveI : IsGalois ℚ (Kd b) := Kd_isGalois_of_sq_eq_neg hd0 hb
  haveI : Finite (Kd b ≃ₐ[ℚ] Kd b) := Nat.finite_of_card_ne_zero (by rw [card_gal hd0 hb]; norm_num)
  haveI := span_prime p
  have hP : P ∈ primesOver (span {(p : ℤ)}) (𝓞 (Kd b)) := by
    first
    | exact ⟨inferInstance, inferInstance⟩
    | exact ⟨‹_›, ‹_›⟩
    | (simp only [Ideal.primesOver, Set.mem_setOf_eq]; exact ⟨inferInstance, inferInstance⟩)
  rw [Set.ncard_eq_one]
  refine ⟨P, Set.eq_singleton_iff_unique_mem.mpr ⟨hP, fun Q hQ => ?_⟩⟩
  have hex : ∃ σ : Kd b ≃ₐ[ℚ] Kd b, σ • P = Q := by
    first
    | (obtain ⟨σ, hσ⟩ := MulAction.exists_smul_eq (Kd b ≃ₐ[ℚ] Kd b) (⟨P, hP⟩ : primesOver (span {(p : ℤ)}) (𝓞 (Kd b))) ⟨Q, hQ⟩; exact ⟨σ, congrArg Subtype.val hσ⟩)
    | (haveI := hQ.1; haveI := hQ.2; exact Ideal.exists_smul_eq_of_isGaloisGroup (span {(p : ℤ)}) P Q (Kd b ≃ₐ[ℚ] Kd b))
  obtain ⟨σ, h1⟩ := hex
  rw [← h1, h σ]

theorem ncard_two (hd0 : 0 < d) (hb : b ^ 2 = -(d : L)) (p : ℕ) [Fact p.Prime]
    (P : Ideal (𝓞 (Kd b))) [P.IsPrime] [P.LiesOver (span {(p : ℤ)})]
    (σ : Kd b ≃ₐ[ℚ] Kd b) (h : σ • P ≠ P) :
    (primesOver (span {(p : ℤ)}) (𝓞 (Kd b))).ncard = 2 := by
  have hf := fund hd0 hb p P
  haveI : NumberField (Kd b) := by
    first
    | exact inferInstance
    | exact NumberField.mk
    | exact ⟨⟩
  haveI : IsGalois ℚ (Kd b) := Kd_isGalois_of_sq_eq_neg hd0 hb
  haveI : Finite (Kd b ≃ₐ[ℚ] Kd b) := Nat.finite_of_card_ne_zero (by rw [card_gal hd0 hb]; norm_num)
  haveI := span_prime p
  have hP : P ∈ primesOver (span {(p : ℤ)}) (𝓞 (Kd b)) := by
    first
    | exact ⟨inferInstance, inferInstance⟩
    | exact ⟨‹_›, ‹_›⟩
    | (simp only [Ideal.primesOver, Set.mem_setOf_eq]; exact ⟨inferInstance, inferInstance⟩)
  have hσP : σ • P ∈ primesOver (span {(p : ℤ)}) (𝓞 (Kd b)) := by
    first
    | exact (σ • (⟨P, hP⟩ : primesOver (span {(p : ℤ)}) (𝓞 (Kd b)))).2
    | exact ⟨inferInstance, inferInstance⟩
  have hdvd : (primesOver (span {(p : ℤ)}) (𝓞 (Kd b))).ncard ∣ 2 := Dvd.intro _ hf
  have hle : (primesOver (span {(p : ℤ)}) (𝓞 (Kd b))).ncard ≤ 2 := Nat.le_of_dvd two_pos hdvd
  have hne1 : (primesOver (span {(p : ℤ)}) (𝓞 (Kd b))).ncard ≠ 1 := by
    intro h1
    obtain ⟨Q, hQ⟩ := Set.ncard_eq_one.mp h1
    rw [hQ, Set.mem_singleton_iff] at hP hσP
    exact h (hσP.trans hP.symm)
  have hne0 : (primesOver (span {(p : ℤ)}) (𝓞 (Kd b))).ncard ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hf
    exact absurd hf (by norm_num)
  omega

theorem smul_mem_of_eq (σ : Kd b ≃ₐ[ℚ] Kd b) (P : Ideal (𝓞 (Kd b))) (h : σ • P = P)
    (y : 𝓞 (Kd b)) (hy : y ∈ P) : σ • y ∈ P := by
  first
  | (have h1 := Ideal.smul_mem_pointwise_smul σ y P hy; rwa [h] at h1)
  | (rw [← h]; exact Ideal.smul_mem_pointwise_smul σ y P hy)
  | (rw [← h]; exact Ideal.mem_map_of_mem _ hy)

theorem smul_intCast (σ : Kd b ≃ₐ[ℚ] Kd b) (n : ℤ) : σ • (n : 𝓞 (Kd b)) = n := by
  first
  | exact map_intCast (MulSemiringAction.toRingHom (Kd b ≃ₐ[ℚ] Kd b) (𝓞 (Kd b)) σ) n
  | simp
  | (rw [← MulSemiringAction.toRingHom_apply, map_intCast])

theorem two_case (hd0 : 0 < d) (hd7 : d % 8 = 7) (hb : b ^ 2 = -(d : L)) (p : ℕ) [Fact p.Prime]
    (hp2 : p = 2) (P : Ideal (𝓞 (Kd b))) [P.IsPrime] [P.LiesOver (span {(p : ℤ)})] :
    (primesOver (span {(p : ℤ)}) (𝓞 (Kd b))).ncard = 2 := by
  obtain ⟨ι, hι⟩ := exists_ne_one hd0 hb
  apply ncard_two hd0 hb p P ι
  intro heq
  have : P.LiesOver (span {(2 : ℤ)}) := by
    subst hp2
    simpa using (inferInstance : P.LiesOver (span {((2 : ℕ) : ℤ)}))
  obtain ⟨c, hc⟩ : ∃ c : ℤ, -(d : ℤ) = 4 * (2 * c) + 1 := ⟨(-(d : ℤ) - 1) / 8, by omega⟩
  have hx : bK b ^ 2 = ((4 * (2 * c) + 1 : ℤ) : Kd b) := by rw [← hc, bK_sq_int hb]
  have hfix := stab_fix (bK b) c hx P ι (MulAction.mem_stabilizer_iff.mpr heq)
  rw [apply_bK_of_ne hd0 hb ι hι] at hfix
  apply bK_ne_zero hd0 hb
  have h2 : (2 : Kd b) * bK b = 0 := by linear_combination -hfix
  simpa using h2

theorem ram_case (hd : d.Prime) (hb : b ^ 2 = -(d : L)) (p : ℕ) [Fact p.Prime] (hpd : p = d)
    (P : Ideal (𝓞 (Kd b))) [hP : P.IsPrime] [P.LiesOver (span {(p : ℤ)})] :
    (primesOver (span {(p : ℤ)}) (𝓞 (Kd b))).ncard = 1 := by
  subst hpd
  have hd0 : 0 < p := hd.pos
  obtain ⟨B, hB, hB2⟩ := odd_lift (bK b) (-(p : ℤ)) (bK_sq_int hb)
  have hdP : ((p : ℤ) : 𝓞 (Kd b)) ∈ P := (odd_intCast_mem_iff p P _).mpr dvd_rfl
  have hBP : B ∈ P := by
    apply hP.mem_of_pow_mem 2
    rw [hB2, Int.cast_neg]
    exact P.neg_mem hdP
  have hmap : map (algebraMap ℤ (𝓞 (Kd b))) (span {(p : ℤ)}) = span {((p : ℤ) : 𝓞 (Kd b))} := by
    rw [Ideal.map_span, Set.image_singleton]
    simp
  have hle : span {((p : ℤ) : 𝓞 (Kd b))} ≤ P ^ 2 := by
    rw [Ideal.span_singleton_le_iff_mem]
    have : ((p : ℤ) : 𝓞 (Kd b)) = -(B ^ 2) := by
      rw [hB2]
      simp
    rw [this]
    exact (P ^ 2).neg_mem (Ideal.pow_mem_pow hBP 2)
  have hne : map (algebraMap ℤ (𝓞 (Kd b))) (span {(p : ℤ)}) ≠ ⊥ := by
    rw [hmap, Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast hd.ne_zero
  have he : 2 ≤ P.ramificationIdx ℤ := by
    rw [IsDedekindDomain.ramificationIdx_eq_multiplicity (span {(p : ℤ)}) P hne]
    apply FiniteMultiplicity.le_multiplicity_of_pow_dvd
    · exact FiniteMultiplicity.of_not_isUnit (Ideal.isUnit_iff.not.mpr hP.ne_top) hne
    · rw [Ideal.dvd_iff_le, hmap]
      exact hle
  have hf := P.inertiaDeg_pos ℤ
  have hm := fund hd0 hb p P
  set g := (primesOver (span {(p : ℤ)}) (𝓞 (Kd b))).ncard
  set e := P.ramificationIdx ℤ
  set f := P.inertiaDeg ℤ
  have hef : 2 ≤ e * f := by nlinarith
  rcases Nat.lt_or_ge g 2 with hg | hg
  · interval_cases g
    · simp at hm
    · rfl
  · nlinarith

theorem odd_case (hd : d.Prime) (hb : b ^ 2 = -(d : L)) (p : ℕ) [hp : Fact p.Prime] (hp2 : p ≠ 2)
    (hpd : p ≠ d) (P : Ideal (𝓞 (Kd b))) [hP : P.IsPrime] [P.LiesOver (span {(p : ℤ)})] :
    (primesOver (span {(p : ℤ)}) (𝓞 (Kd b))).ncard = 2 ↔ jacobiSym (-(d : ℤ)) p = 1 := by
  have hd0 := hd.pos
  have := quad_K hd0 hb
  have hpb : span {(p : ℤ)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast hp.out.ne_zero
  have : Finite (𝓞 (Kd b) ⧸ P) :=
    Ring.HasFiniteQuotients.finiteQuotient (Ideal.ne_bot_of_liesOver_of_ne_bot hpb P)
  obtain ⟨τ, hτ⟩ := IsArithFrobAt.exists_of_isInvariant ℤ (Kd b ≃ₐ[ℚ] Kd b) P
  have hnd : ¬ (p : ℤ) ∣ -(d : ℤ) := by
    rw [dvd_neg]
    intro h'
    exact hpd ((Nat.prime_dvd_prime_iff_eq hp.out hd).mp (by exact_mod_cast h'))
  have hsgn := odd_frob_sgn p hp2 P τ hτ (bK b) _ (bK_sq_int hb) hnd
  have hcop : Int.gcd (-(d : ℤ)) p = 1 := by
    rw [Int.neg_gcd, Int.gcd_natCast_natCast]
    exact (Nat.coprime_primes hd hp.out).mpr (Ne.symm hpd)
  rcases jacobiSym.eq_one_or_neg_one hcop with hj | hj
  · simp only [hj, iff_true]
    obtain ⟨ι, hι⟩ := exists_ne_one hd0 hb
    apply ncard_two hd0 hb p P ι
    intro heq
    have hleg : legendreSym p (-(d : ℤ)) = 1 := by
      rw [jacobiSym.legendreSym.to_jacobiSym]
      exact hj
    have h0 : ((-(d : ℤ) : ℤ) : ZMod p) ≠ 0 := by
      rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
      exact hnd
    obtain ⟨r, hr⟩ := (legendreSym.eq_one_iff p h0).mp hleg
    set t : ℤ := (r.val : ℤ) with ht
    have htd : (p : ℤ) ∣ t ^ 2 + d := by
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
      push_cast
      rw [ht, Int.cast_natCast, ZMod.natCast_zmod_val]
      push_cast at hr
      linear_combination -hr
    obtain ⟨B, hB, hB2⟩ := odd_lift (bK b) (-(d : ℤ)) (bK_sq_int hb)
    have hιB : ι • B = -B := by
      apply RingOfIntegers.coe_injective
      show ((ι • B : 𝓞 (Kd b)) : Kd b) = ((-B : 𝓞 (Kd b)) : Kd b)
      rw [odd_coe_smul, hB, apply_bK_of_ne hd0 hb ι hι]
      simp [hB]
    have hprod : (B - (t : 𝓞 (Kd b))) * (B + (t : 𝓞 (Kd b))) ∈ P := by
      have he : (B - (t : 𝓞 (Kd b))) * (B + (t : 𝓞 (Kd b))) = -((t ^ 2 + d : ℤ) : 𝓞 (Kd b)) := by
        rw [show (B - (t : 𝓞 (Kd b))) * (B + (t : 𝓞 (Kd b))) = B ^ 2 - (t : 𝓞 (Kd b)) ^ 2 by ring,
          hB2]
        push_cast
        ring
      rw [he]
      exact P.neg_mem ((odd_intCast_mem_iff p P _).mpr htd)
    have h2t : ((2 * t : ℤ) : 𝓞 (Kd b)) ∈ P := by
      rcases hP.mem_or_mem hprod with h | h
      · have h' := smul_mem_of_eq ι P heq _ h
        rw [smul_sub, hιB, smul_intCast] at h'
        have := P.neg_mem (P.add_mem h h')
        convert this using 1
        push_cast
        ring
      · have h' := smul_mem_of_eq ι P heq _ h
        rw [smul_add, hιB, smul_intCast] at h'
        have := P.add_mem h h'
        convert this using 1
        push_cast
        ring
    rw [odd_intCast_mem_iff p P] at h2t
    have hpt : (p : ℤ) ∣ t := by
      rcases (Nat.prime_iff_prime_int.mp hp.out).dvd_or_dvd h2t with h | h
      · exfalso
        have : p ∣ 2 := by exact_mod_cast h
        exact hp2 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).mp this)
      · exact h
    apply hnd
    have h1 : (p : ℤ) ∣ t ^ 2 := dvd_pow hpt two_ne_zero
    exact dvd_neg.mpr ((dvd_add_right h1).mp htd)
  · rw [hj]
    have hne : τ ≠ 1 := by
      intro h1
      rw [h1, hj] at hsgn
      simp [sgn] at hsgn
    have hall : ∀ σ : Kd b ≃ₐ[ℚ] Kd b, σ • P = P := by
      intro σ
      by_cases hσ : σ = 1
      · rw [hσ]
        exact one_smul _ _
      · rw [eq_of_ne_one hd0 hb σ τ hσ hne]
        exact MulAction.mem_stabilizer_iff.mp (IsArithFrobAt.mem_stabilizer hτ)
    rw [ncard_one hd0 hb p P hall]
    norm_num

private theorem Kd_exists_isPrime_liesOver (p : ℕ) [hp : Fact p.Prime] :
    ∃ P : Ideal (𝓞 (Kd b)), P.IsPrime ∧ P.LiesOver (span {(p : ℤ)}) := by
  haveI hmax : (span {(p : ℤ)}).IsMaximal := by
    first
    | exact Int.ideal_span_isMaximal_of_prime p
    | exact (span_prime p).isMaximal (by simp [hp.out.ne_zero])
    | exact Ideal.IsPrime.isMaximal (span_prime p) (by simp [hp.out.ne_zero])
  first
  | (obtain ⟨P, hP⟩ := Ideal.nonempty_primesOver (S := 𝓞 (Kd b)) (span {(p : ℤ)}); exact ⟨P, hP.1, hP.2⟩)
  | (obtain ⟨P, hP, hPl⟩ := Ideal.exists_ideal_liesOver_maximal_of_isIntegral (span {(p : ℤ)}) (𝓞 (Kd b)); exact ⟨P, hP.isPrime, hPl⟩)
  | (obtain ⟨Q, hQ, hQc⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := 𝓞 (Kd b)) (span {(p : ℤ)}) (by rw [(RingHom.injective_iff_ker_eq_bot _).mp (algebraMap ℤ (𝓞 (Kd b))).injective_int]; exact bot_le); exact ⟨Q, hQ.isPrime, ⟨hQc.symm⟩⟩)

theorem clause (hd : d.Prime) (hd7 : d % 8 = 7) (hb : b ^ 2 = -(d : L)) (p : ℕ) (hp : p.Prime) :
    (primesOver (span {(p : ℤ)}) (𝓞 (Kd b))).ncard = 2 ↔
      (p = 2 ∨ (p ≠ 2 ∧ jacobiSym (-(d : ℤ)) p = 1)) := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨P, hP1, hP2⟩ := Kd_exists_isPrime_liesOver (b := b) p
  haveI := hP1
  haveI := hP2
  by_cases h2 : p = 2
  · have h3 := two_case hd.pos hd7 hb p h2 P
    exact ⟨fun _ => Or.inl h2, fun _ => h3⟩
  · by_cases hpd : p = d
    · have h3 := ram_case hd hb p hpd P
      have hJ : jacobiSym (-(d : ℤ)) p = 0 := by
        subst hpd
        first
        | (rw [jacobiSym.mod_left, Int.emod_eq_zero_of_dvd (by simp), jacobiSym.zero_left hp.one_lt])
        | (rw [jacobiSym.eq_zero_iff_not_coprime]; simp [Int.gcd_neg, Int.gcd_self]; exact hp.one_lt.ne')
      rw [h3, hJ]
      simp [h2]
    · have h3 := odd_case hd hb p h2 hpd P
      constructor
      · intro h
        exact Or.inr ⟨h2, h3.mp h⟩
      · rintro (h | ⟨-, h⟩)
        · exact absurd h h2
        · exact h3.mpr h

theorem ram_ncard (hd : d.Prime) (hb : b ^ 2 = -(d : L)) :
    (primesOver (span {(d : ℤ)}) (𝓞 (Kd b))).ncard = 1 := by
  haveI : Fact d.Prime := ⟨hd⟩
  obtain ⟨P, hP1, hP2⟩ := Kd_exists_isPrime_liesOver (b := b) d
  haveI := hP1
  haveI := hP2
  exact ram_case hd hb d rfl P

end Formalism.FrobeniusOrbits.SplitK

namespace Formalism.FrobeniusOrbits

theorem hostSplitK_of (hFrob : HostFrob) : HostSplitK := by
  intro e q d hH L _ _ ζ a b hL
  obtain ⟨hq, hd, hq8, hd16, hJq⟩ := hH
  have hb : b ^ 2 = -(d : L) := hL.2.2.1
  have hd7 : d % 8 = 7 := by omega
  have hq2 : q ≠ 2 := by
    rintro rfl
    norm_num at hq8
  have hd2 : d ≠ 2 := by
    rintro rfl
    norm_num at hd16
  have hqd : q ≠ d := by
    rintro rfl
    omega
  refine ⟨fun p hp => SplitK.clause hd hd7 hb p hp, SplitK.ram_ncard hd hb,
    (SplitK.clause hd hd7 hb q hq).mpr (Or.inr ⟨hq2, hJq⟩), ?_⟩
  intro p hfp hp2 hpq hpd P _ _ σ hσ
  have hF := ((hFrob e q d ⟨hq, hd, hqd, hq2, hd2⟩ L ζ a b hL p hp2 hpq hpd P).2.1 σ).mp hσ
  have h2 := hF.2.1
  rw [SplitK.clause hd hd7 hb p hfp.out]
  show galE e ζ a b σ ∈ (chD e).ker ↔ _
  rw [MonoidHom.mem_ker]
  show (galE e ζ a b σ).1.2 = 1 ↔ _
  constructor
  · intro h
    refine Or.inr ⟨hp2, ?_⟩
    rw [← h2, h]
    first | rfl | simp
  · rintro (h | ⟨-, h⟩)
    · exact absurd h hp2
    · apply Units.ext
      rw [h2, h]
      first | rfl | simp

end Formalism.FrobeniusOrbits
