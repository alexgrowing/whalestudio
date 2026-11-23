import Mathlib
import ReciprocityTheory.CommutativeAlgebra.PolynomialHeights.HeightAddRingKrullDimQuotientMvPolynomialField
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsRingKrullDimQuotientMvPolynomialEqNat
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LeadingCoeffNonnegOfEventuallyEvalNat

open Polynomial Filter Module

namespace GlobalTheory

attribute [local instance] MvPolynomial.gradedAlgebra

theorem height_add_ringKrullDim_quotient_of_finiteType (k : Type*) {A : Type*} [Field k]
    [CommRing A] [IsDomain A] [Algebra k A] [Algebra.FiniteType k A] (q : Ideal A) [q.IsPrime] :
    (q.height : WithBot ℕ∞) + ringKrullDim (A ⧸ q) = ringKrullDim A := by
  obtain ⟨s, g, hinj, hint⟩ := exists_integral_inj_algHom_of_fg k A
  let : Algebra (MvPolynomial (Fin s) k) A := g.toRingHom.toAlgebra
  have : Algebra.IsIntegral (MvPolynomial (Fin s) k) A := ⟨hint⟩
  have hinj' : Function.Injective (algebraMap (MvPolynomial (Fin s) k) A) := hinj
  have : FaithfulSMul (MvPolynomial (Fin s) k) A :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr hinj'
  have : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing k A
  set p := q.comap (algebraMap (MvPolynomial (Fin s) k) A) with hp
  have : q.LiesOver p := ⟨rfl⟩
  have h1 : p.height ≤ q.height := by
    rw [Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown p q]
    exact le_self_add
  have h2 : q.height ≤ p.height := by
    have e1 := PrimeSpectrum.height_eq_orderHeight (⟨q, inferInstance⟩ : PrimeSpectrum A)
    have e2 := PrimeSpectrum.height_eq_orderHeight (⟨p, inferInstance⟩ : PrimeSpectrum _)
    simp only at e1 e2
    rw [e1, e2]
    exact Order.height_le_height_apply_of_strictMono
      (fun P : PrimeSpectrum A => (⟨P.asIdeal.comap (algebraMap (MvPolynomial (Fin s) k) A),
        inferInstance⟩ : PrimeSpectrum _))
      (fun P Q hPQ => Ideal.IsIntegral.comap_lt_comap (R := MvPolynomial (Fin s) k)
        (show P.asIdeal < Q.asIdeal from hPQ)) _
  rw [le_antisymm h2 h1,
    ReciprocityTheory.CA.ringKrullDim_quotient_eq_quotient_comap_of_isIntegral
      (A := MvPolynomial (Fin s) k) q,
    ReciprocityTheory.CA.height_add_ringKrullDim_quotient_mvPolynomial_field,
    ReciprocityTheory.CA.ringKrullDim_eq_of_isIntegral_of_injective hinj',
    MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field]
  simp

theorem ringKrullDim_quotient_add_one_of_mem_minimalPrimes_sup (k : Type*) {A : Type*} [Field k]
    [CommRing A] [Algebra k A] [Algebra.FiniteType k A] {P Q : Ideal A} [P.IsPrime] {f : A}
    (hf : f ∉ P) (hQ : Q ∈ (P ⊔ Ideal.span {f}).minimalPrimes) :
    ringKrullDim (A ⧸ Q) + 1 = ringKrullDim (A ⧸ P) := by
  have : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing k A
  have : Q.IsPrime := hQ.1.1
  have hPQ : P ≤ Q := le_sup_left.trans hQ.1.2
  have hfQ : f ∈ Q := hQ.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self f))
  have : (Q.map (Ideal.Quotient.mk P)).IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rw [Ideal.mk_ker]; exact hPQ)
  have h1 := Ideal.map_height_le_one_of_mem_minimalPrimes hQ
  have h2 : (Q.map (Ideal.Quotient.mk P)).height ≠ 0 := by
    rw [Ne, Ideal.height_eq_zero_iff, IsDomain.minimalPrimes_eq_singleton_bot,
      Set.mem_singleton_iff]
    intro h
    have := Ideal.mem_map_of_mem (Ideal.Quotient.mk P) hfQ
    rw [h, Ideal.mem_bot, Ideal.Quotient.eq_zero_iff_mem] at this
    exact hf this
  have h3 : (Q.map (Ideal.Quotient.mk P)).height = 1 :=
    le_antisymm h1 (Order.one_le_iff_ne_zero.2 h2)
  have h4 := height_add_ringKrullDim_quotient_of_finiteType k (Q.map (Ideal.Quotient.mk P))
  rw [h3, ringKrullDim_eq_of_ringEquiv (DoubleQuot.quotQuotEquivQuotOfLE hPQ), add_comm] at h4
  exact h4

open MvPolynomial DirectSum

variable {ι k : Type*} [Field k]

theorem isHomogeneous_sup_span_singleton {I : Ideal (MvPolynomial ι k)}
    (hI : I.IsHomogeneous (homogeneousSubmodule ι k)) {f : MvPolynomial ι k} {d : ℕ}
    (hf : f.IsHomogeneous d) : (I ⊔ Ideal.span {f}).IsHomogeneous (homogeneousSubmodule ι k) :=
  hI.sup (Ideal.homogeneous_span _ _ (by rintro x rfl; exact ⟨d, hf⟩))

theorem isHomogeneous_colon_singleton {I : Ideal (MvPolynomial ι k)}
    (hI : I.IsHomogeneous (homogeneousSubmodule ι k)) {f : MvPolynomial ι k} {d : ℕ}
    (hf : f.IsHomogeneous d) :
    (Submodule.colon I {f}).IsHomogeneous (homogeneousSubmodule ι k) := by
  intro n g hg
  rw [Submodule.mem_colon_singleton, smul_eq_mul] at hg ⊢
  rw [← coe_decompose_mul_add_of_right_mem (homogeneousSubmodule ι k) (j := d) hf]
  exact hI _ hg

variable [Finite ι]

theorem finrank_quotPiece_sup_add_colon {I : Ideal (MvPolynomial ι k)}
    (hI : I.IsHomogeneous (homogeneousSubmodule ι k)) {f : MvPolynomial ι k} {d : ℕ}
    (hf : f.IsHomogeneous d) (n : ℕ) :
    finrank k (quotPiece (I ⊔ Ideal.span {f}) (n + d : ℕ)) +
      finrank k (quotPiece (Submodule.colon I {f}) n) = finrank k (quotPiece I (n + d : ℕ)) := by
  have h1 := finrank_quotPiece_add (I ⊔ Ideal.span {f}) (n + d)
  have h2 := finrank_quotPiece_add (Submodule.colon I {f}) n
  have h3 := finrank_quotPiece_add I (n + d)
  have e := GradedHilbert.finrank_sup_map_add_finrank_inf_comap (LinearMap.mulRight k f)
    (homogeneousSubmodule ι k n) (I.restrictScalars k ⊓ homogeneousSubmodule ι k (n + d))
  have a₁ : (I ⊔ Ideal.span {f}).restrictScalars k ⊓ homogeneousSubmodule ι k (n + d) =
      (I.restrictScalars k ⊓ homogeneousSubmodule ι k (n + d)) ⊔
        (homogeneousSubmodule ι k n).map (LinearMap.mulRight k f) := by
    apply le_antisymm
    · rintro m ⟨hm, hmn⟩
      obtain ⟨a, ha, _, hb, rfl⟩ := Submodule.mem_sup.1 hm
      obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.1 hb
      rw [← decompose_of_mem_same (homogeneousSubmodule ι k) hmn, decompose_add, DirectSum.add_apply,
        Submodule.coe_add, coe_decompose_mul_add_of_right_mem _ (j := d) hf]
      exact Submodule.add_mem_sup ⟨hI _ ha, SetLike.coe_mem _⟩ ⟨_, SetLike.coe_mem _, rfl⟩
    · refine sup_le (inf_le_inf_right _ fun m hm => Submodule.mem_sup_left hm) ?_
      rintro _ ⟨m, hm, rfl⟩
      exact ⟨Ideal.mem_sup_right (Ideal.mem_span_singleton'.2 ⟨m, rfl⟩),
        IsHomogeneous.mul hm hf⟩
  have a₂ : (Submodule.colon I {f}).restrictScalars k ⊓ homogeneousSubmodule ι k n =
      homogeneousSubmodule ι k n ⊓ (I.restrictScalars k ⊓
        homogeneousSubmodule ι k (n + d)).comap (LinearMap.mulRight k f) := by
    apply le_antisymm
    · rintro m ⟨hm, hmn⟩
      exact ⟨hmn, Submodule.mem_colon_singleton.1 hm, IsHomogeneous.mul hmn hf⟩
    · rintro m ⟨hm, hm', -⟩
      exact ⟨Submodule.mem_colon_singleton.2 hm', hm⟩
  rw [a₁] at h1
  rw [a₂] at h2
  omega

theorem idealHilbertPoly_eq_sup_add_colon {I : Ideal (MvPolynomial ι k)}
    (hI : I.IsHomogeneous (homogeneousSubmodule ι k)) {f : MvPolynomial ι k} {d : ℕ}
    (hf : f.IsHomogeneous d) :
    idealHilbertPoly I = idealHilbertPoly (I ⊔ Ideal.span {f}) +
      (idealHilbertPoly (Submodule.colon I {f})).comp (Polynomial.X - Polynomial.C (d : ℚ)) := by
  apply polynomial_eq_of_eventually_eval_nat
  obtain ⟨N, hN⟩ := eventually_atTop.1
    (eventually_finrank_quotPiece (isHomogeneous_colon_singleton hI hf))
  filter_upwards [eventually_finrank_quotPiece hI,
    eventually_finrank_quotPiece (isHomogeneous_sup_span_singleton hI hf),
    eventually_ge_atTop (N + d)] with n h1 h2 h3
  obtain ⟨n, rfl⟩ : ∃ m, n = m + d := ⟨n - d, by omega⟩
  rw [Polynomial.eval_add, ← h1, ← h2, ← finrank_quotPiece_sup_add_colon hI hf n, Nat.cast_add,
    hN n (by omega)]
  simp

theorem idealHilbertPoly_sup_of_isPrime {P : Ideal (MvPolynomial ι k)} [hP : P.IsPrime]
    (hI : P.IsHomogeneous (homogeneousSubmodule ι k)) {f : MvPolynomial ι k} {d : ℕ}
    (hf : f.IsHomogeneous d) (hfP : f ∉ P) :
    idealHilbertPoly (P ⊔ Ideal.span {f}) = idealHilbertPoly P -
      (idealHilbertPoly P).comp (Polynomial.X - Polynomial.C (d : ℚ)) := by
  have h := idealHilbertPoly_eq_sup_add_colon hI hf
  have e : Submodule.colon P {f} = P := by
    ext g
    rw [Submodule.mem_colon_singleton, smul_eq_mul, hP.mul_mem_iff_mem_or_mem]
    simp [hfP]
  rw [e] at h
  linear_combination -h

theorem degree_idealHilbertPoly_anti {I J : Ideal (MvPolynomial ι k)}
    (hI : I.IsHomogeneous (homogeneousSubmodule ι k))
    (hJ : J.IsHomogeneous (homogeneousSubmodule ι k)) (h : I ≤ J) :
    (idealHilbertPoly J).degree ≤ (idealHilbertPoly I).degree := by
  refine degree_le_of_eventually_eval_nat (eventually_idealHilbertPoly_nonneg hJ) ?_
  filter_upwards [eventually_finrank_quotPiece hI, eventually_finrank_quotPiece hJ] with n h1 h2
  have h3 := finrank_quotPiece_add I n
  have h4 := finrank_quotPiece_add J n
  have h5 : finrank k (I.restrictScalars k ⊓ homogeneousSubmodule ι k n : Submodule k _) ≤
      finrank k (J.restrictScalars k ⊓ homogeneousSubmodule ι k n : Submodule k _) :=
    Submodule.finrank_mono (inf_le_inf_right _ fun x hx => h hx)
  rw [← h1, ← h2]
  exact_mod_cast (by omega)

theorem idealHilbertPoly_eq_zero_of_forall_X_mem {I : Ideal (MvPolynomial ι k)}
    (hI : I.IsHomogeneous (homogeneousSubmodule ι k))
    (h : ∀ i, (X i : MvPolynomial ι k) ∈ I) : idealHilbertPoly I = 0 := by
  apply polynomial_eq_of_eventually_eval_nat
  filter_upwards [eventually_finrank_quotPiece hI, eventually_ge_atTop 1] with n h1 h2
  have : quotPiece I n = ⊥ := by
    rw [quotPiece_natCast, eq_bot_iff]
    rintro _ ⟨p, hp, rfl⟩
    have h3 := mem_idealOfVars_pow_of_isHomogeneous hp h2
    rw [pow_one] at h3
    have h4 : idealOfVars ι k ≤ I := by
      rw [Ideal.span_le, Set.range_subset_iff]; exact h
    simpa [Ideal.Quotient.eq_zero_iff_mem] using h4 h3
  rw [← h1, this]
  simp

theorem idealHilbertPoly_ne_zero_of_X_notMem {P : Ideal (MvPolynomial ι k)} [hP : P.IsPrime]
    (hI : P.IsHomogeneous (homogeneousSubmodule ι k)) {i : ι}
    (h : (X i : MvPolynomial ι k) ∉ P) : idealHilbertPoly P ≠ 0 := by
  intro h0
  obtain ⟨n, hn⟩ := (eventually_finrank_quotPiece hI).exists
  have := (isHilbertPoly_idealHilbertPoly hI).finite n
  have hbot : quotPiece P n = ⊥ := by simpa [h0] using hn
  have hmem : Ideal.Quotient.mk P (X i ^ n) ∈ quotPiece P n := by
    rw [quotPiece_natCast]
    exact ⟨X i ^ n, isHomogeneous_X_pow i n, rfl⟩
  rw [hbot, Submodule.mem_bot, Ideal.Quotient.eq_zero_iff_mem] at hmem
  exact h (hP.mem_of_pow_mem _ hmem)

omit [Finite ι] in

theorem exists_form_lt_sup_lt_colon {I : Ideal (MvPolynomial ι k)}
    (hI : I.IsHomogeneous (homogeneousSubmodule ι k)) (h : I ≠ ⊤) (hp : ¬ I.IsPrime) :
    ∃ (d : ℕ) (f : MvPolynomial ι k), f.IsHomogeneous d ∧ I < I ⊔ Ideal.span {f} ∧
      I < Submodule.colon I {f} := by
  rw [hI.isPrime_iff] at hp
  push Not at hp
  obtain ⟨g, f, -, ⟨d, hf⟩, hgf, hg, hfI⟩ := hp h
  refine ⟨d, f, hf, lt_of_le_of_ne le_sup_left fun e => hfI ?_, lt_of_le_of_ne
    (fun x hx => Submodule.mem_colon_singleton.2 (I.mul_mem_right _ hx)) fun e => hg ?_⟩
  · rw [e]; exact Ideal.mem_sup_right (Ideal.mem_span_singleton_self f)
  · rw [e]; exact Submodule.mem_colon_singleton.2 hgf

theorem degree_comp_X_sub_C_rat (P : ℚ[X]) (r : ℚ) :
    (P.comp (Polynomial.X - Polynomial.C r)).degree = P.degree := by
  rw [sub_eq_add_neg, ← Polynomial.C_neg, ← taylor_apply, degree_taylor]

theorem coeff_comp_X_sub_C_rat {P : ℚ[X]} {e : ℕ} (h : P.degree ≤ e) (r : ℚ) :
    (P.comp (Polynomial.X - Polynomial.C r)).coeff e = P.coeff e := by
  have := degree_comp_X_add_C_sub_lt P (-r) e h
  rw [Polynomial.C_neg, ← sub_eq_add_neg] at this
  have := coeff_eq_zero_of_degree_lt this
  rwa [Polynomial.coeff_sub, sub_eq_zero] at this

theorem degree_eq_of_degree_sub_comp {P : ℚ[X]} {m : ℕ}
    (h : (P - P.comp (Polynomial.X - Polynomial.C 1)).degree < m) : P.degree ≤ m := by
  by_contra hlt
  push Not at hlt
  have hP0 : P ≠ 0 := by rintro rfl; simp at hlt
  rw [degree_eq_natDegree hP0, Nat.cast_lt] at hlt
  obtain ⟨e, he⟩ : ∃ e, P.natDegree = e + 1 := ⟨P.natDegree - 1, by omega⟩
  have h1 := (coeff_sub_comp_X_sub_C P 1 e (by rw [← he]; exact degree_le_natDegree)).2
  rw [coeff_eq_zero_of_degree_lt (h.trans_le (by exact_mod_cast (by omega : m ≤ e))), ← he,
    one_mul, eq_comm, mul_eq_zero] at h1
  rcases h1 with h1 | h1
  · exact absurd h1 (by positivity)
  · exact hP0 (leadingCoeff_eq_zero.1 h1)

theorem idealHilbertPoly_top : idealHilbertPoly (⊤ : Ideal (MvPolynomial ι k)) = 0 :=
  idealHilbertPoly_eq_zero_of_forall_X_mem (Ideal.IsHomogeneous.top _) fun _ => trivial

theorem degree_idealHilbertPoly_lt {I : Ideal (MvPolynomial ι k)}
    (hI : I.IsHomogeneous (homogeneousSubmodule ι k)) {m : ℕ}
    (hm : ringKrullDim (MvPolynomial ι k ⧸ I) ≤ m) : (idealHilbertPoly I).degree < m := by
  induction I using IsNoetherian.induction generalizing m with
  | _ I ih =>
  have mono : ∀ J, I ≤ J → ringKrullDim (MvPolynomial ι k ⧸ J) ≤ m := fun J hJ =>
    (ringKrullDim_le_of_surjective _ (Ideal.Quotient.factor_surjective hJ)).trans hm
  by_cases htop : I = ⊤
  · rw [htop, idealHilbertPoly_top]; simp
  by_cases hp : Ideal.IsPrime I
  · by_cases hX : ∀ i, (X i : MvPolynomial ι k) ∈ I
    · rw [idealHilbertPoly_eq_zero_of_forall_X_mem hI hX]; simp
    push Not at hX
    obtain ⟨i, hi⟩ := hX
    have hJ := isHomogeneous_sup_span_singleton hI (isHomogeneous_X k i)
    have hlt : I < I ⊔ Ideal.span {X i} := lt_of_le_of_ne le_sup_left fun e => hi (by
      rw [e]; exact Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
    have hne : I ⊔ Ideal.span {X i} ≠ ⊤ := ne_top_of_le_ne_top idealOfVars_ne_top
      (sup_le (le_idealOfVars_of_isHomogeneous hI htop)
        (Ideal.span_mono (Set.singleton_subset_iff.2 ⟨i, rfl⟩)))
    obtain ⟨δ, hδ⟩ := exists_ringKrullDim_quotient_mvPolynomial_eq_nat hne
    have h1 := ringKrullDim_succ_le_of_surjective (Ideal.Quotient.factor hlt.le)
      (Ideal.Quotient.factor_surjective _) (r := Ideal.Quotient.mk I (X i))
      (mem_nonZeroDivisors_of_ne_zero (by rwa [Ne, Ideal.Quotient.eq_zero_iff_mem])) (by
        rw [Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem]
        exact Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
    have h2 : δ + 1 ≤ m := by
      have := h1.trans hm
      rw [hδ] at this
      exact_mod_cast this
    have h3 := ih _ hlt hJ hδ.le
    rw [idealHilbertPoly_sup_of_isPrime hI (isHomogeneous_X k i) hi, Nat.cast_one] at h3
    exact (degree_eq_of_degree_sub_comp h3).trans_lt (by exact_mod_cast h2)
  · obtain ⟨d, f, hf, h1, h2⟩ := exists_form_lt_sup_lt_colon hI htop hp
    rw [idealHilbertPoly_eq_sup_add_colon hI hf]
    refine (degree_add_le _ _).trans_lt (max_lt
      (ih _ h1 (isHomogeneous_sup_span_singleton hI hf) (mono _ h1.le)) ?_)
    rw [degree_comp_X_sub_C_rat]
    exact ih _ h2 (isHomogeneous_colon_singleton hI hf) (mono _ h2.le)

theorem ringKrullDim_quotient_le_zero_of_forall_X_mem {I : Ideal (MvPolynomial ι k)}
    (h : ∀ i, (X i : MvPolynomial ι k) ∈ I) : ringKrullDim (MvPolynomial ι k ⧸ I) ≤ 0 := by
  rw [← ringKrullDim_eq_zero_of_field k]
  refine ringKrullDim_le_of_surjective (algebraMap k _) fun x => ?_
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
  induction p using MvPolynomial.induction_on with
  | C a => exact ⟨a, rfl⟩
  | add p q hp hq =>
    obtain ⟨a, ha⟩ := hp
    obtain ⟨b, hb⟩ := hq
    exact ⟨a + b, by rw [map_add, map_add, ha, hb]⟩
  | mul_X p i _ =>
    exact ⟨0, by rw [map_zero, eq_comm, Ideal.Quotient.eq_zero_iff_mem]; exact I.mul_mem_left _ (h i)⟩

theorem degree_idealHilbertPoly_eq_of_isPrime {P : Ideal (MvPolynomial ι k)} [hP : P.IsPrime]
    (hI : P.IsHomogeneous (homogeneousSubmodule ι k)) {e : ℕ}
    (he : ringKrullDim (MvPolynomial ι k ⧸ P) = (e + 1 : ℕ)) :
    (idealHilbertPoly P).degree = e := by
  refine le_antisymm ((degree_le_iff_coeff_zero _ _).2 fun m hm =>
    (degree_lt_iff_coeff_zero _ _).1 (degree_idealHilbertPoly_lt hI he.le) m
      (by exact_mod_cast hm)) ?_
  induction e generalizing P with
  | zero =>
    have : ¬ ∀ i, (X i : MvPolynomial ι k) ∈ P := fun h => by
      have := ringKrullDim_quotient_le_zero_of_forall_X_mem h
      rw [he] at this
      exact absurd this (by norm_num)
    push Not at this
    obtain ⟨i, hi⟩ := this
    exact zero_le_degree_iff.2 (idealHilbertPoly_ne_zero_of_X_notMem hI hi)
  | succ e ih =>
    have : ¬ ∀ i, (X i : MvPolynomial ι k) ∈ P := fun h => by
      have := ringKrullDim_quotient_le_zero_of_forall_X_mem h
      rw [he] at this
      exact absurd this (by exact_mod_cast (by omega))
    push Not at this
    obtain ⟨i, hi⟩ := this
    have hJ := isHomogeneous_sup_span_singleton hI (isHomogeneous_X k i)
    have hne : P ⊔ Ideal.span {X i} ≠ ⊤ := ne_top_of_le_ne_top idealOfVars_ne_top
      (sup_le (le_idealOfVars_of_isHomogeneous hI hP.ne_top)
        (Ideal.span_mono (Set.singleton_subset_iff.2 ⟨i, rfl⟩)))
    obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hne
    obtain ⟨Q, hQ, -⟩ := Ideal.exists_minimalPrimes_le hle
    have : Q.IsPrime := hQ.1.1
    have hQh := isHomogeneous_of_mem_minimalPrimes _ hJ hQ
    obtain ⟨δ, hδ⟩ := exists_ringKrullDim_quotient_mvPolynomial_eq_nat this.ne_top
    have h1 := ringKrullDim_quotient_add_one_of_mem_minimalPrimes_sup k hi hQ
    rw [he, hδ] at h1
    obtain rfl : δ = e + 1 := by
      have : δ + 1 = e + 1 + 1 := by exact_mod_cast h1
      omega
    have h2 := (ih hQh hδ).trans (degree_idealHilbertPoly_anti hJ hQh hQ.1.2)
    rw [idealHilbertPoly_sup_of_isPrime hI (isHomogeneous_X k i) hi] at h2
    by_contra hlt
    have h3 : (idealHilbertPoly P).degree ≤ e := (degree_le_iff_coeff_zero _ _).2 fun m hm =>
      (degree_lt_iff_coeff_zero _ _).1 (not_le.1 hlt) m (by exact_mod_cast hm)
    have h4 := degree_comp_X_add_C_sub_lt _ (-((1 : ℕ) : ℚ)) e h3
    rw [Polynomial.C_neg, ← sub_eq_add_neg, ← degree_neg, neg_sub] at h4
    exact absurd h2 (not_le.2 h4)

theorem sum_coeff_idealHilbertPoly_minimalPrimes_le {I : Ideal (MvPolynomial ι k)}
    (hI : I.IsHomogeneous (homogeneousSubmodule ι k)) {e : ℕ}
    (he : (idealHilbertPoly I).degree ≤ e) :
    ∑ Q ∈ I.finite_minimalPrimes_of_isNoetherianRing.toFinset, (idealHilbertPoly Q).coeff e ≤
      (idealHilbertPoly I).coeff e := by
  classical
  induction I using IsNoetherian.induction with
  | _ I ih =>
  by_cases htop : I = ⊤
  · subst htop
    simp [idealHilbertPoly_top, Ideal.minimalPrimes_top]
  by_cases hp : Ideal.IsPrime I
  · simp [Ideal.minimalPrimes_eq_subsingleton_self]
  obtain ⟨d, f, hf, h1, h2⟩ := exists_form_lt_sup_lt_colon hI htop hp
  have hJ₁ := isHomogeneous_sup_span_singleton hI hf
  have hJ₂ := isHomogeneous_colon_singleton hI hf
  have e₁ := (degree_idealHilbertPoly_anti hI hJ₁ h1.le).trans he
  have e₂ := (degree_idealHilbertPoly_anti hI hJ₂ h2.le).trans he
  have nn : ∀ J : Ideal (MvPolynomial ι k), J.IsHomogeneous (homogeneousSubmodule ι k) →
      I ≤ J → ∀ Q ∈ J.minimalPrimes, 0 ≤ (idealHilbertPoly Q).coeff e := by
    intro J hJ hIJ Q hQ
    have hQh := isHomogeneous_of_mem_minimalPrimes _ hJ hQ
    exact coeff_nonneg_of_eventually_eval_nat
      ((degree_idealHilbertPoly_anti hI hQh (hIJ.trans hQ.1.2)).trans he)
      (eventually_idealHilbertPoly_nonneg hQh)
  rw [idealHilbertPoly_eq_sup_add_colon hI hf, Polynomial.coeff_add, coeff_comp_X_sub_C_rat e₂]
  refine le_trans ?_ (add_le_add (ih _ h1 hJ₁ e₁) (ih _ h2 hJ₂ e₂))
  rw [← Finset.sum_union_inter]
  refine le_add_of_le_of_nonneg (Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_)
    (Finset.sum_nonneg ?_)
  · intro Q hQ
    simp only [Finset.mem_union, Set.Finite.mem_toFinset] at hQ ⊢
    by_cases hfQ : f ∈ Q
    · exact Or.inl ⟨⟨hQ.1.1, sup_le hQ.1.2 ((Ideal.span_singleton_le_iff_mem _).2 hfQ)⟩,
        fun R hR hRQ => hQ.2 ⟨hR.1, h1.le.trans hR.2⟩ hRQ⟩
    · exact Or.inr ⟨⟨hQ.1.1, fun g hg => (hQ.1.1.mem_or_mem
          (hQ.1.2 (Submodule.mem_colon_singleton.1 hg))).resolve_right hfQ⟩,
        fun R hR hRQ => hQ.2 ⟨hR.1, h2.le.trans hR.2⟩ hRQ⟩
  · intro Q hQ _
    simp only [Finset.mem_union, Set.Finite.mem_toFinset] at hQ
    exact hQ.elim (nn _ hJ₁ h1.le Q) (nn _ hJ₂ h2.le Q)
  · intro Q hQ
    simp only [Finset.mem_inter, Set.Finite.mem_toFinset] at hQ
    exact nn _ hJ₁ h1.le Q hQ.1

end GlobalTheory
