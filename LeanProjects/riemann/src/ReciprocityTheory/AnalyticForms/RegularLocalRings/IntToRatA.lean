import Mathlib
import ReciprocityTheory.CommutativeAlgebra.PolynomialHeights.HeightAddRingKrullDimQuotientMvPolynomialField

namespace ReciprocityTheory.AnForm.R.IntegerToRational

open MvPolynomial

variable {σ : Type} [Fintype σ]

noncomputable def ChZero (q : Ideal (MvPolynomial σ ℤ)) : Prop := ∀ m : ℤ, (C m : MvPolynomial σ ℤ) ∈ q → m = 0

noncomputable abbrev intS (σ : Type) : Submonoid (MvPolynomial σ ℤ) := (nonZeroDivisors ℤ).map (C (σ := σ))

attribute [local instance] MvPolynomial.algebraMvPolynomial

lemma disj_intS (P : Ideal (MvPolynomial σ ℤ)) (hP : ChZero P) :
    Disjoint ((intS σ : Submonoid _) : Set (MvPolynomial σ ℤ)) (P : Set _) := by
  rw [Set.disjoint_left]
  rintro _ ⟨m, hm, rfl⟩ hmP
  exact nonZeroDivisors.ne_zero hm (hP m hmP)

lemma map_isPrime (P : Ideal (MvPolynomial σ ℤ)) [P.IsPrime] (hP : ChZero P) :
    (Ideal.map (MvPolynomial.map (Int.castRingHom ℚ)) P).IsPrime := by
  have hA : algebraMap (MvPolynomial σ ℤ) (MvPolynomial σ ℚ) = MvPolynomial.map (Int.castRingHom ℚ) := by
    rw [MvPolynomial.algebraMap_def, algebraMap_int_eq]
  rw [← hA]
  exact IsLocalization.isPrime_of_isPrime_disjoint (intS σ) (MvPolynomial σ ℚ) P ‹_› (disj_intS P hP)

lemma comap_map_eq (P : Ideal (MvPolynomial σ ℤ)) [P.IsPrime] (hP : ChZero P) :
    (Ideal.map (MvPolynomial.map (Int.castRingHom ℚ)) P).comap
      (MvPolynomial.map (Int.castRingHom ℚ)) = P := by
  have hA : algebraMap (MvPolynomial σ ℤ) (MvPolynomial σ ℚ) = MvPolynomial.map (Int.castRingHom ℚ) := by
    rw [MvPolynomial.algebraMap_def, algebraMap_int_eq]
  rw [← hA]
  exact IsLocalization.under_map_of_isPrime_disjoint (intS σ) (MvPolynomial σ ℚ) ‹_› (disj_intS P hP)

lemma chZero_comap (Q : Ideal (MvPolynomial σ ℚ)) [Q.IsPrime] :
    ChZero (Q.comap (MvPolynomial.map (Int.castRingHom ℚ))) := by
  intro m hm
  rw [Ideal.mem_comap, MvPolynomial.map_C] at hm
  by_contra h
  have hu : IsUnit (C (Int.castRingHom ℚ m) : MvPolynomial σ ℚ) :=
    (isUnit_iff_ne_zero.mpr (by simpa using h)).map C
  exact (‹Q.IsPrime›).ne_top (Ideal.eq_top_of_isUnit_mem Q hm hu)

lemma comap_strictMono :
    StrictMono (fun Q : Ideal (MvPolynomial σ ℚ) => Q.comap (MvPolynomial.map (Int.castRingHom ℚ))) := by
  have hA : algebraMap (MvPolynomial σ ℤ) (MvPolynomial σ ℚ) = MvPolynomial.map (Int.castRingHom ℚ) := by
    rw [MvPolynomial.algebraMap_def, algebraMap_int_eq]
  rw [← hA]
  exact (IsLocalization.orderEmbedding (intS σ) (MvPolynomial σ ℚ)).strictMono

theorem isJacobsonRing_int : IsJacobsonRing ℤ := by
  rw [isJacobsonRing_iff_prime_eq]
  intro P hP
  by_cases h : P = ⊥
  · subst h
    refine le_antisymm (fun x hx => ?_) Ideal.le_jacobson
    rw [Ideal.mem_jacobson_bot] at hx
    rw [Ideal.mem_bot]
    rcases Int.isUnit_iff.mp (hx x) with hu | hu
    · exact mul_self_eq_zero.mp (by linarith)
    · nlinarith [mul_self_nonneg x]
  · have := hP
    have : P.IsMaximal := IsPrime.to_maximal_ideal h
    exact Ideal.jacobson_eq_self_of_isMaximal

lemma ringKrullDim_quotient_eq_coheight {A : Type*} [CommRing A] (I : Ideal A) [hI : I.IsPrime] :
    ringKrullDim (A ⧸ I) = (Order.coheight (⟨I, hI⟩ : PrimeSpectrum A) : WithBot ℕ∞) := by
  rw [Order.coheight_eq_krullDim_Ici]
  unfold ringKrullDim
  rw [Order.krullDim_eq_of_orderIso (Ideal.primeSpectrumQuotientOrderIsoZeroLocus I)]
  exact Order.krullDim_eq_of_orderIso (OrderIso.setCongr _ _ (Set.ext fun p => Iff.rfl))

lemma eq_zero_of_aeval_mem {ι : Type*} (q : Ideal (MvPolynomial σ ℤ)) [q.IsPrime] (hq : ChZero q)
    (p : ℕ) (hp : 1 < p) (x : ι → MvPolynomial σ ℤ)
    (hred : ∀ G : MvPolynomial ι ℤ, aeval x G ∈ q → map (Int.castRingHom (ZMod p)) G = 0)
    (G : MvPolynomial ι ℤ) (hG : aeval x G ∈ q) : G = 0 := by
  have : NeZero p := ⟨by omega⟩
  have hp0 : (C (p : ℤ) : MvPolynomial σ ℤ) ∉ q := fun h => by
    have := hq _ h
    omega
  have key : ∀ k : ℕ, ∀ G : MvPolynomial ι ℤ, aeval x G ∈ q → ∀ s, ((p : ℤ) ^ k) ∣ G.coeff s := by
    intro k
    induction k with
    | zero => intros; simp
    | succ k ih =>
      intro G hG s
      have hdiv : C (p : ℤ) ∣ G := by
        rw [MvPolynomial.C_dvd_iff_dvd_coeff]
        intro i
        have h0 := congrArg (MvPolynomial.coeff i) (hred G hG)
        rw [MvPolynomial.coeff_map, MvPolynomial.coeff_zero, eq_intCast,
          ZMod.intCast_zmod_eq_zero_iff_dvd] at h0
        exact h0
      obtain ⟨H, rfl⟩ := hdiv
      have hH : aeval x H ∈ q := by
        rw [map_mul, MvPolynomial.aeval_C] at hG
        exact (‹q.IsPrime›.mem_or_mem hG).resolve_left (by simpa using hp0)
      rw [MvPolynomial.coeff_C_mul, pow_succ']
      exact mul_dvd_mul_left _ (ih H hH s)
  ext s
  rw [MvPolynomial.coeff_zero]
  by_contra hne
  have hd := key (G.coeff s).natAbs G hG s
  have h1 := Int.natAbs_dvd_natAbs.mpr hd
  rw [Int.natAbs_pow, Int.natAbs_natCast] at h1
  have h2 := Nat.le_of_dvd (Int.natAbs_pos.mpr hne) h1
  have h3 : (G.coeff s).natAbs < p ^ (G.coeff s).natAbs := Nat.lt_pow_self hp
  omega

lemma dim_le_of_charP (q q' : Ideal (MvPolynomial σ ℤ)) [q.IsPrime] [q'.IsPrime] (hle : q ≤ q')
    (hq : ChZero q) (hq' : ¬ ChZero q') :
    ringKrullDim (MvPolynomial σ ℤ ⧸ q') ≤
      ringKrullDim (MvPolynomial σ ℚ ⧸ Ideal.map (MvPolynomial.map (Int.castRingHom ℚ)) q) := by
  classical
  obtain ⟨m, hmq', hm0⟩ : ∃ m : ℤ, (C m : MvPolynomial σ ℤ) ∈ q' ∧ m ≠ 0 := by
    by_contra h
    exact hq' fun m hm => by_contra fun hne => h ⟨m, hm, hne⟩

  have hgen := Ideal.span_singleton_generator (q'.comap (C : ℤ →+* MvPolynomial σ ℤ))
  obtain ⟨g, hg⟩ : ∃ g : ℤ, Ideal.span {g} = q'.comap (C : ℤ →+* MvPolynomial σ ℤ) := ⟨_, hgen⟩
  have hspan : Ideal.span {((g.natAbs : ℕ) : ℤ)} = q'.comap (C : ℤ →+* MvPolynomial σ ℤ) := by
    rw [Int.span_natAbs, hg]
  have hmemC : ∀ n : ℤ, (C n : MvPolynomial σ ℤ) ∈ q' ↔ ((g.natAbs : ℕ) : ℤ) ∣ n := by
    intro n
    rw [← Ideal.mem_span_singleton, hspan]
    rfl
  have hp0 : ((g.natAbs : ℕ) : ℤ) ≠ 0 := by
    intro h
    have := (hmemC m).mp hmq'
    rw [h, zero_dvd_iff] at this
    exact hm0 this
  have hpP : Nat.Prime g.natAbs := by
    have hpr : (Ideal.span {((g.natAbs : ℕ) : ℤ)}).IsPrime := by
      rw [hspan]
      infer_instance
    have := (Ideal.span_singleton_prime hp0).mp hpr
    rw [Int.prime_iff_natAbs_prime, Int.natAbs_natCast] at this
    exact this
  set p := g.natAbs with hpdef
  have : Fact p.Prime := ⟨hpP⟩

  have : CharP (MvPolynomial σ ℤ ⧸ q') p := ⟨fun n => by
    rw [← map_natCast (Ideal.Quotient.mk q'), Ideal.Quotient.eq_zero_iff_mem,
      ← map_natCast (C : ℤ →+* MvPolynomial σ ℤ), hmemC, Int.natCast_dvd_natCast]⟩
  let : Algebra (ZMod p) (MvPolynomial σ ℤ ⧸ q') := ZMod.algebra _ p
  have : Algebra.FiniteType ℤ (MvPolynomial σ ℤ ⧸ q') :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ ℤ q') (Ideal.Quotient.mkₐ_surjective ℤ q')
  have : Algebra.FiniteType (ZMod p) (MvPolynomial σ ℤ ⧸ q') :=
    Algebra.FiniteType.of_restrictScalars_finiteType ℤ (ZMod p) _
  obtain ⟨d, hdB, htrB⟩ := ReciprocityTheory.CA.exists_dim_trdeg_field (K := ZMod p) (A := MvPolynomial σ ℤ ⧸ q')
  have : FaithfulSMul (ZMod p) (MvPolynomial σ ℤ ⧸ q') :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (RingHom.injective _)
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis (ZMod p) (MvPolynomial σ ℤ ⧸ q')

  let x : s → MvPolynomial σ ℤ := fun i => (Ideal.Quotient.mk_surjective (i : MvPolynomial σ ℤ ⧸ q')).choose
  have hx : ∀ i, Ideal.Quotient.mk q' (x i) = i := fun i =>
    (Ideal.Quotient.mk_surjective (i : MvPolynomial σ ℤ ⧸ q')).choose_spec
  have hred : ∀ G : MvPolynomial s ℤ, aeval x G ∈ q → map (Int.castRingHom (ZMod p)) G = 0 := by
    intro G hG
    apply hs.1.eq_zero_of_aeval_eq_zero
    rw [← algebraMap_int_eq, MvPolynomial.aeval_map_algebraMap,
      show ((↑) : s → MvPolynomial σ ℤ ⧸ q') = fun i => Ideal.Quotient.mkₐ ℤ q' (x i) from
        funext fun i => (hx i).symm,
      ← MvPolynomial.comp_aeval_apply, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem]
    exact hle hG
  have hinj := eq_zero_of_aeval_mem q hq p hpP.one_lt x hred

  have := map_isPrime q hq
  have : Algebra.FiniteType ℚ (MvPolynomial σ ℚ ⧸ Ideal.map (MvPolynomial.map (Int.castRingHom ℚ)) q) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ ℚ _) (Ideal.Quotient.mkₐ_surjective ℚ _)
  obtain ⟨e, hdC, htrC⟩ := ReciprocityTheory.CA.exists_dim_trdeg_field (K := ℚ)
    (A := MvPolynomial σ ℚ ⧸ Ideal.map (MvPolynomial.map (Int.castRingHom ℚ)) q)
  let φ : MvPolynomial σ ℤ →ₐ[ℤ] MvPolynomial σ ℚ ⧸ Ideal.map (MvPolynomial.map (Int.castRingHom ℚ)) q :=
    ((Ideal.Quotient.mk _).comp (MvPolynomial.map (Int.castRingHom ℚ))).toIntAlgHom
  let y : s → MvPolynomial σ ℚ ⧸ Ideal.map (MvPolynomial.map (Int.castRingHom ℚ)) q := fun i => φ (x i)
  have hy : AlgebraicIndependent ℚ y := by
    rw [algebraicIndependent_iff]
    intro H hH
    obtain ⟨⟨G, c⟩, hGH⟩ := IsLocalization.surj ((nonZeroDivisors ℤ).map (C (σ := s))) H
    obtain ⟨n, hn, hnc⟩ := Submonoid.mem_map.mp c.2
    have hG0 : G = 0 := by
      apply hinj G
      have h1 := congrArg (MvPolynomial.aeval y) hGH
      rw [map_mul, hH, zero_mul, MvPolynomial.algebraMap_def, MvPolynomial.aeval_map_algebraMap,
        ← MvPolynomial.comp_aeval_apply] at h1
      have h2 : Ideal.Quotient.mk _ (MvPolynomial.map (Int.castRingHom ℚ) (aeval x G)) = 0 := h1.symm
      rw [Ideal.Quotient.eq_zero_iff_mem] at h2
      rw [← comap_map_eq q hq]
      exact h2
    rw [hG0, map_zero] at hGH
    have hc0 : algebraMap (MvPolynomial s ℤ) (MvPolynomial s ℚ) (c : MvPolynomial s ℤ) ≠ 0 := by
      rw [← hnc, MvPolynomial.algebraMap_def, MvPolynomial.map_C, Ne, MvPolynomial.C_eq_zero]
      simpa using nonZeroDivisors.ne_zero hn
    exact (mul_eq_zero.mp hGH).resolve_right hc0
  have hle' := hy.cardinalMk_le_trdeg
  rw [hs.cardinalMk_eq_trdeg, htrB, htrC] at hle'
  have hde : d ≤ e := by exact_mod_cast hle'
  rw [hdB, hdC]
  exact_mod_cast hde

end ReciprocityTheory.AnForm.R.IntegerToRational
