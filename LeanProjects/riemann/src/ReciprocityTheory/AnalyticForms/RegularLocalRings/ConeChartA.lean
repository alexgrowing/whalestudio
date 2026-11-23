import ReciprocityTheory.AnalyticForms.RegularLocalRings.ProjHyp
import ReciprocityTheory.CommutativeAlgebra.PolynomialHeights.HeightAddRingKrullDimQuotientMvPolynomialField

namespace ReciprocityTheory.AnForm.R

open MvPolynomial Algebra

theorem ringKrullDim_le_of_forall_quotient {A : Type*} [CommRing A] (d : WithBot ℕ∞)
    (h : ∀ P : Ideal A, P.IsPrime → ringKrullDim (A ⧸ P) ≤ d) : ringKrullDim A ≤ d := by
  refine iSup_le fun p => ?_
  let P : Ideal A := (p.toFun 0).asIdeal
  have hP : P.IsPrime := (p.toFun 0).isPrime
  have hmem : ∀ i, p.toFun i ∈ PrimeSpectrum.zeroLocus (P : Set A) := fun i =>
    (PrimeSpectrum.mem_zeroLocus _ _).2
      ((PrimeSpectrum.asIdeal_le_asIdeal _ _).2 (p.monotone (Fin.zero_le i)))
  let q : LTSeries (PrimeSpectrum.zeroLocus (P : Set A)) :=
    { length := p.length, toFun := fun i => ⟨p.toFun i, hmem i⟩, step := fun i => p.step i }
  exact (Order.LTSeries.length_le_krullDim q).trans
    ((ringKrullDim_quotient P).symm.le.trans (h P hP))

theorem ptIdealOf_isMaximal {σ : Type} (z : σ → ℂ) : (ptIdealOf z).IsMaximal :=
  RingHom.ker_isMaximal_of_surjective _ fun x => ⟨MvPolynomial.C x, MvPolynomial.eval_C x⟩

theorem ringKrullDim_locAt {σ : Type} (J : Ideal (MvPolynomial σ ℂ)) (z : σ → ℂ)
    (hJ : J ≤ ptIdealOf z) :
    ringKrullDim (locAt J z) = ((ptIdealOf z).map (Ideal.Quotient.mk J)).height := by
  haveI hm : (ptIdealOf z).IsPrime := (ptIdealOf_isMaximal z).isPrime
  have hmem : ∀ a : MvPolynomial σ ℂ,
      Ideal.Quotient.mk J a ∈ (ptIdealOf z).map (Ideal.Quotient.mk J) ↔ a ∈ ptIdealOf z :=
    fun a => Ideal.mem_quotient_iff_mem hJ
  haveI hm' : ((ptIdealOf z).map (Ideal.Quotient.mk J)).IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rw [Ideal.mk_ker]; exact hJ)
  haveI : IsLocalization.AtPrime (locAt J z) ((ptIdealOf z).map (Ideal.Quotient.mk J)) := by
    refine ⟨?_, ?_, ?_⟩
    · rintro ⟨r, hr⟩
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective r
      have hr' : Ideal.Quotient.mk J a ∉ (ptIdealOf z).map (Ideal.Quotient.mk J) := hr
      have ha : a ∉ ptIdealOf z := fun h => hr' ((hmem a).2 h)
      exact (IsLocalization.map_units (Localization.AtPrime (ptIdealOf z))
        (⟨a, ha⟩ : (ptIdealOf z).primeCompl)).map (Ideal.Quotient.mk _)
    · intro w
      obtain ⟨u, rfl⟩ := Ideal.Quotient.mk_surjective w
      obtain ⟨⟨a, s⟩, hu⟩ := IsLocalization.surj (ptIdealOf z).primeCompl u
      have hs' : (s : MvPolynomial σ ℂ) ∉ ptIdealOf z := s.2
      have hs : Ideal.Quotient.mk J (s : MvPolynomial σ ℂ) ∉ (ptIdealOf z).map (Ideal.Quotient.mk J) :=
        fun h => hs' ((hmem _).1 h)
      refine ⟨(Ideal.Quotient.mk J a, ⟨Ideal.Quotient.mk J s, hs⟩), ?_⟩
      show Ideal.Quotient.mk _ u *
          Ideal.Quotient.mk _ (algebraMap (MvPolynomial σ ℂ) (Localization.AtPrime (ptIdealOf z)) s) =
        Ideal.Quotient.mk _ (algebraMap (MvPolynomial σ ℂ) (Localization.AtPrime (ptIdealOf z)) a)
      rw [← map_mul]
      exact congrArg (Ideal.Quotient.mk _) hu
    · intro x y hxy
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
      obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
      have hxy' : Ideal.Quotient.mk (J.map (algebraMap (MvPolynomial σ ℂ) (Localization.AtPrime (ptIdealOf z))))
            (algebraMap (MvPolynomial σ ℂ) (Localization.AtPrime (ptIdealOf z)) a) =
          Ideal.Quotient.mk _ (algebraMap (MvPolynomial σ ℂ) (Localization.AtPrime (ptIdealOf z)) b) := hxy
      have h1 := Ideal.Quotient.eq.1 hxy'
      rw [← map_sub] at h1
      obtain ⟨⟨i, s⟩, hs⟩ :=
        (IsLocalization.mem_map_algebraMap_iff (ptIdealOf z).primeCompl
          (Localization.AtPrime (ptIdealOf z))).1 h1
      rw [← map_mul, IsLocalization.eq_iff_exists (ptIdealOf z).primeCompl] at hs
      obtain ⟨c, hc⟩ := hs
      have hc' : (c : MvPolynomial σ ℂ) ∉ ptIdealOf z := c.2
      have hs' : (s : MvPolynomial σ ℂ) ∉ ptIdealOf z := s.2
      have hcs : (c : MvPolynomial σ ℂ) * s ∉ ptIdealOf z := fun h => (hm.mem_or_mem h).elim hc' hs'
      refine ⟨⟨Ideal.Quotient.mk J ((c : MvPolynomial σ ℂ) * s), fun h => hcs ((hmem _).1 h)⟩, ?_⟩
      show Ideal.Quotient.mk J ((c : MvPolynomial σ ℂ) * s) * Ideal.Quotient.mk J a =
        Ideal.Quotient.mk J ((c : MvPolynomial σ ℂ) * s) * Ideal.Quotient.mk J b
      rw [← map_mul, ← map_mul, Ideal.Quotient.eq]
      have e : (c : MvPolynomial σ ℂ) * s * a - c * s * b = c * i := by
        linear_combination hc
      rw [e]
      exact J.mul_mem_left _ i.2
  exact IsLocalization.AtPrime.ringKrullDim_eq_height _ (locAt J z)

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem aeval_smul_of_isMultiHomog {T : Type*} [CommRing T] [Algebra ℂ T]
    {f : MvPolynomial (Σ k, ι k) ℂ} {a : K → ℕ}
    (hf : IsMultiHomog f a) (c : K → T) (y : (Σ k, ι k) → T) :
    aeval (fun q => c q.1 * y q) f = (∏ k, c k ^ a k) * aeval y f := by
  classical
  conv_lhs => rw [f.as_sum]
  conv_rhs => rw [f.as_sum]
  simp only [map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [aeval_monomial, aeval_monomial, Finsupp.prod_pow, Finsupp.prod_pow]
  have e : ∏ q : (Σ k, ι k), (c q.1 * y q) ^ m q = (∏ k, c k ^ a k) * ∏ q, y q ^ m q := by
    simp_rw [mul_pow]
    rw [Finset.prod_mul_distrib, Fintype.prod_sigma]
    congr 1
    refine Finset.prod_congr rfl fun k _ => ?_
    show ∏ i, c k ^ m ⟨k, i⟩ = c k ^ a k
    rw [Finset.prod_pow_eq_pow_sum, hf m hm k]
  rw [e]
  ring

theorem ringKrullDim_quotient_le_of_chartIdeal_le {P : Ideal (MvPolynomial (Σ k, ι k) ℂ)}
    (hP : IsMultiHomogIdeal P) (e : ℕ)
    (hdim : ∀ Q ∈ P.minimalPrimes,
      ringKrullDim (MvPolynomial (Σ k, ι k) ℂ ⧸ Q) = ((e + Fintype.card K : ℕ) : WithBot ℕ∞))
    (p : (k : K) → ι k) (𝔮 : Ideal (MvPolynomial (Σ k, ι k) ℂ)) [𝔮.IsPrime]
    (h𝔮 : chartIdeal P p ≤ 𝔮) :
    ringKrullDim (MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔮) ≤ e := by
  classical
  have : IsDomain (MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔮) := Ideal.Quotient.isDomain 𝔮
  let y : (Σ k, ι k) → MvPolynomial K (MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔮) := fun q => C (Ideal.Quotient.mk 𝔮 (X q))
  let θ : (MvPolynomial (Σ k, ι k) ℂ) →ₐ[ℂ] MvPolynomial K (MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔮) := aeval (fun q => (X q.1 : MvPolynomial K (MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔮)) * y q)
  have hy : ∀ f : (MvPolynomial (Σ k, ι k) ℂ), aeval y f = C (Ideal.Quotient.mk 𝔮 f) := by
    intro f
    have : (aeval y : (MvPolynomial (Σ k, ι k) ℂ) →ₐ[ℂ] MvPolynomial K (MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔮)) =
        (IsScalarTower.toAlgHom ℂ (MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔮) (MvPolynomial K (MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔮))).comp (Ideal.Quotient.mkₐ ℂ 𝔮) := by
      apply MvPolynomial.algHom_ext
      intro q
      simp [y, MvPolynomial.algebraMap_eq]
    rw [this]
    simp [MvPolynomial.algebraMap_eq]
  have hPθ : P ≤ RingHom.ker θ := by
    obtain ⟨S, hS, hPS⟩ := hP
    have hle : Ideal.span S ≤ RingHom.ker θ := by
      rw [Ideal.span_le]
      intro f hf
      obtain ⟨a, ha⟩ := hS f hf
      have hfP : f ∈ P := by rw [hPS]; exact Ideal.subset_span hf
      have hf𝔮 : f ∈ 𝔮 := h𝔮 (Ideal.mem_sup_left hfP)
      show θ f = 0
      simp only [θ]
      rw [aeval_smul_of_isMultiHomog ha (X : K → MvPolynomial K (MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔮)) y, hy,
        Ideal.Quotient.eq_zero_iff_mem.mpr hf𝔮, map_zero, mul_zero]
    rw [hPS]
    exact hle
  have : (RingHom.ker θ).IsPrime := RingHom.ker_isPrime θ
  obtain ⟨Q, hQmin, hQle⟩ := Ideal.exists_minimalPrimes_le hPθ
  have hdimR : ringKrullDim θ.range ≤ ((e + Fintype.card K : ℕ) : WithBot ℕ∞) := by
    rw [← hdim Q hQmin]
    let g : (MvPolynomial (Σ k, ι k) ℂ) ⧸ Q →+* θ.range := Ideal.Quotient.lift Q (θ.rangeRestrict : (MvPolynomial (Σ k, ι k) ℂ) →+* θ.range)
      (fun a ha => Subtype.ext (by simpa using hQle ha))
    refine ringKrullDim_le_of_surjective g ?_
    intro x
    obtain ⟨a, ha⟩ := θ.rangeRestrict_surjective x
    exact ⟨Ideal.Quotient.mk Q a, ha⟩
  have : Algebra.FiniteType ℂ θ.range :=
    Algebra.FiniteType.of_surjective θ.rangeRestrict θ.rangeRestrict_surjective
  have : Algebra.FiniteType ℂ (MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔮) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ ℂ 𝔮) (Ideal.Quotient.mkₐ_surjective ℂ 𝔮)
  obtain ⟨sA, hAdim, hAtr⟩ := ReciprocityTheory.CA.exists_dim_trdeg_field (K := ℂ) (A := (MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔮))
  obtain ⟨sR, hRdim, hRtr⟩ := ReciprocityTheory.CA.exists_dim_trdeg_field (K := ℂ) (A := θ.range)
  have : FaithfulSMul ℂ (MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔮) :=
    (faithfulSMul_iff_algebraMap_injective ℂ (MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔮)).mpr (algebraMap ℂ (MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔮)).injective
  have : FaithfulSMul (MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔮) (MvPolynomial K (MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔮)) :=
    (faithfulSMul_iff_algebraMap_injective (MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔮) (MvPolynomial K (MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔮))).mpr (MvPolynomial.C_injective K (MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔮))
  have : FaithfulSMul ℂ θ.range :=
    (faithfulSMul_iff_algebraMap_injective ℂ θ.range).mpr (algebraMap ℂ θ.range).injective
  have : FaithfulSMul θ.range (MvPolynomial K (MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔮)) :=
    (faithfulSMul_iff_algebraMap_injective θ.range (MvPolynomial K (MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔮))).mpr Subtype.val_injective
  have hT1 : trdeg ℂ (MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔮) + trdeg (MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔮) (MvPolynomial K (MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔮)) = trdeg ℂ (MvPolynomial K (MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔮)) :=
    trdeg_add_eq ℂ (MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔮)

  have h1 : ∀ k, Ideal.Quotient.mk 𝔮 (X ⟨k, p k⟩ : (MvPolynomial (Σ k, ι k) ℂ)) = 1 := by
    intro k
    rw [← map_one (Ideal.Quotient.mk 𝔮), Ideal.Quotient.eq]
    exact h𝔮 (Ideal.mem_sup_right (Ideal.subset_span ⟨k, rfl⟩))
  have hXk : ∀ k, (X k : MvPolynomial K (MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔮)) ∈ θ.range := by
    intro k
    refine (θ.mem_range).mpr ⟨X ⟨k, p k⟩, ?_⟩
    simp only [θ, y, aeval_X, h1, map_one, mul_one]
  have hXq : ∀ q, (X q.1 : MvPolynomial K (MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔮)) * y q ∈ θ.range := fun q =>
    (θ.mem_range).mpr ⟨X q, by simp only [θ, aeval_X]⟩
  let AC := Subalgebra.algebraicClosure θ.range (MvPolynomial K (MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔮))
  have hRAC : ∀ t ∈ θ.range, t ∈ AC := fun t ht =>
    (Subalgebra.mem_algebraicClosure _ _).mpr (isAlgebraic_algebraMap (⟨t, ht⟩ : θ.range))
  have hyAC : ∀ q, y q ∈ AC := fun q =>
    (Subalgebra.mem_algebraicClosure _ _).mpr (IsAlgebraic.of_mul
      (mem_nonZeroDivisors_of_ne_zero (X_ne_zero q.1))
      ((Subalgebra.mem_algebraicClosure _ _).mp (hRAC _ (hXk q.1)))
      ((Subalgebra.mem_algebraicClosure _ _).mp (hRAC _ (hXq q))))
  have hCAC : ∀ f : (MvPolynomial (Σ k, ι k) ℂ), C (Ideal.Quotient.mk 𝔮 f) ∈ AC := by
    intro f
    refine MvPolynomial.induction_on (motive := fun f => C (Ideal.Quotient.mk 𝔮 f) ∈ AC) f ?_ ?_ ?_
    · intro c
      apply hRAC
      refine (θ.mem_range).mpr ⟨C c, ?_⟩
      simp only [θ, aeval_C, MvPolynomial.algebraMap_apply]
      rfl
    · intro f g hf hg
      rw [map_add, map_add]
      exact AC.add_mem hf hg
    · intro f q hf
      rw [map_mul, map_mul]
      exact AC.mul_mem hf (hyAC q)
  have hall : ∀ t : MvPolynomial K (MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔮), t ∈ AC := by
    intro t
    refine MvPolynomial.induction_on (motive := fun t => t ∈ AC) t ?_ ?_ ?_
    · intro a
      obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective a
      exact hCAC f
    · intro f g hf hg
      exact AC.add_mem hf hg
    · intro f k hf
      exact AC.mul_mem hf (hRAC _ (hXk k))
  have : Algebra.IsAlgebraic θ.range (MvPolynomial K (MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔮)) :=
    ⟨fun t => (Subalgebra.mem_algebraicClosure _ _).mp (hall t)⟩
  have hT2 : trdeg ℂ θ.range + trdeg θ.range (MvPolynomial K (MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔮)) = trdeg ℂ (MvPolynomial K (MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔮)) :=
    trdeg_add_eq ℂ θ.range
  have h0 : trdeg θ.range (MvPolynomial K (MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔮)) = 0 := trdeg_eq_zero
  rw [h0, add_zero] at hT2
  have hK : trdeg (MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔮) (MvPolynomial K (MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔮)) = (Fintype.card K : Cardinal) := by
    rw [MvPolynomial.trdeg_of_isDomain, Cardinal.lift_id, Cardinal.mk_fintype]
  rw [hK, hAtr, ← hT2, hRtr] at hT1
  have hnat : sA + Fintype.card K = sR := by exact_mod_cast hT1
  rw [hRdim] at hdimR
  have hsR : sR ≤ e + Fintype.card K := by exact_mod_cast hdimR
  rw [hAdim]
  exact_mod_cast (by omega : sA ≤ e)

open Classical in

noncomputable def blockWt (k : K) (q : Σ k, ι k) : ℕ := if q.1 = k then 1 else 0

theorem isWeightedHomogeneous_blockWt {f : MvPolynomial (Σ k, ι k) ℂ} {dg : K → ℕ}
    (hf : IsMultiHomog f dg) (k : K) : IsWeightedHomogeneous (blockWt k) f (dg k) := by
  intro d hd
  have hs : d ∈ f.support := MvPolynomial.mem_support_iff.mpr hd
  rw [← hf d hs k]
  simp only [Finsupp.weight_apply, smul_eq_mul]
  rw [Finsupp.sum_fintype _ _ (by simp)]
  rw [Fintype.sum_sigma, Fintype.sum_eq_single k]
  · simp [blockWt]
  · intro k' hk'
    simp [blockWt, hk']

theorem sum_blockWt_eval {f : MvPolynomial (Σ k, ι k) ℂ} {dg : K → ℕ} (hf : IsMultiHomog f dg)
    (k : K) (z : (Σ k, ι k) → ℂ) :
    ∑ q, (blockWt k q : ℂ) * (z q * eval z (pderiv q f)) = (dg k : ℂ) * eval z f := by
  have h := congrArg (eval z) (isWeightedHomogeneous_blockWt hf k).sum_weight_X_mul_pderiv
  simpa [map_sum, nsmul_eq_mul] using h

end ReciprocityTheory.AnForm.R
