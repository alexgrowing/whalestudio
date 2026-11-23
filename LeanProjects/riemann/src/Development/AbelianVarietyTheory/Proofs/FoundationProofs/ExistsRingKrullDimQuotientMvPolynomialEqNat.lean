import Mathlib
import ReciprocityTheory.CommutativeAlgebra.SaturatedChains.Integral

namespace GlobalTheory

open MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

section Graded

variable {A : Type*} [CommRing A] {τ : Type*} [SetLike τ A] [AddSubgroupClass τ A]
  (𝒜 : ℕ → τ) [GradedRing 𝒜]

theorem isHomogeneous_of_mem_minimalPrimes {J p : Ideal A} (hJ : J.IsHomogeneous 𝒜)
    (hp : p ∈ J.minimalPrimes) : p.IsHomogeneous 𝒜 := by
  have hpp : p.IsPrime := hp.1.1
  rw [Ideal.IsHomogeneous.iff_eq]
  refine le_antisymm (Ideal.toIdeal_homogeneousCore_le _ _) ?_
  refine hp.2 ⟨hpp.homogeneousCore, ?_⟩ (Ideal.toIdeal_homogeneousCore_le _ _)
  exact hJ.toIdeal_homogeneousCore_eq_self.symm.trans_le (Ideal.homogeneousCore_mono _ hp.1.2)

theorem exists_homogeneous_notMem_of_not_le {J p : Ideal A} (hJ : J.IsHomogeneous 𝒜)
    (h : ¬ J ≤ p) : ∃ n, ∃ x ∈ 𝒜 n, x ∈ J ∧ x ∉ p := by
  classical
  by_contra hcon
  push Not at hcon
  refine h fun x hx => ?_
  rw [← DirectSum.sum_support_decompose 𝒜 x]
  exact p.sum_mem fun i _ => hcon i _ (SetLike.coe_mem _) (hJ i hx)

theorem exists_homogeneous_forall_notMem (s : Finset (Ideal A))
    (hprime : ∀ p ∈ s, p.IsPrime) (hhom : ∀ p ∈ s, p.IsHomogeneous 𝒜)
    (hinc : ∀ p ∈ s, ∀ q ∈ s, q ≤ p → q = p)
    (hpos : ∀ p ∈ s, ∃ n, 0 < n ∧ ∃ x ∈ 𝒜 n, x ∉ p) :
    ∃ n, 0 < n ∧ ∃ x ∈ 𝒜 n, ∀ p ∈ s, x ∉ p := by
  classical
  have key : ∀ p : s, ∃ n, 0 < n ∧ ∃ g ∈ 𝒜 n, g ∉ p.1 ∧ ∀ q ∈ s, q ≠ p.1 → g ∈ q := by
    rintro ⟨p, hp⟩
    obtain ⟨n, hn, x, hx, hxp⟩ := hpos p hp
    have hH : ((s.erase p).inf id).IsHomogeneous 𝒜 := by
      rw [Finset.inf_eq_iInf]
      exact Ideal.IsHomogeneous.iInf₂ fun q hq => hhom q (Finset.mem_of_mem_erase hq)
    have hnle : ¬ (s.erase p).inf id ≤ p := by
      rw [(hprime p hp).inf_le']
      rintro ⟨q, hq, hqp⟩
      exact (Finset.ne_of_mem_erase hq) (hinc p hp q (Finset.mem_of_mem_erase hq) hqp)
    obtain ⟨m, y, hy, hyJ, hyp⟩ := exists_homogeneous_notMem_of_not_le 𝒜 hH hnle
    refine ⟨n + m, by omega, x * y, SetLike.mul_mem_graded hx hy, ?_, ?_⟩
    · intro h
      exact ((hprime p hp).mem_or_mem h).elim hxp hyp
    · intro q hq hqp
      exact q.mul_mem_left _
        ((Finset.inf_le (f := id) (Finset.mem_erase.mpr ⟨hqp, hq⟩) : _ ≤ q) hyJ)
  choose n hn g hg hgp hgq using key
  have hD : 0 < ∏ p, n p := Finset.prod_pos fun p _ => hn p
  have hdvd : ∀ p, n p ∣ ∏ p, n p := fun p => Finset.dvd_prod_of_mem _ (Finset.mem_univ p)
  have hq0 : ∀ p, (∏ p, n p) / n p ≠ 0 := fun p =>
    (Nat.div_pos (Nat.le_of_dvd hD (hdvd p)) (hn p)).ne'
  refine ⟨∏ p, n p, hD, ∑ p, g p ^ ((∏ p, n p) / n p), ?_, ?_⟩
  · refine sum_mem fun p _ => ?_
    have := SetLike.pow_mem_graded ((∏ p, n p) / n p) (hg p)
    rwa [smul_eq_mul, Nat.div_mul_cancel (hdvd p)] at this
  · intro p hp hmem
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (⟨p, hp⟩ : s))] at hmem
    have h2 : ∑ q ∈ Finset.univ.erase (⟨p, hp⟩ : s), g q ^ ((∏ p, n p) / n q) ∈ p := by
      refine p.sum_mem fun q hq => Ideal.pow_mem_of_mem _ ?_ _ (Nat.pos_of_ne_zero (hq0 q))
      refine hgq q p hp fun h => Finset.ne_of_mem_erase hq (Subtype.ext h.symm)
    have h3 := (Submodule.add_mem_iff_left p h2).mp hmem
    exact hgp ⟨p, hp⟩ ((hprime p hp).mem_of_pow_mem _ h3)

end Graded

theorem ringKrullDim_quotient_radical_sup_succ_le {A : Type*} [CommRing A] (J : Ideal A) {f : A}
    (hf : ∀ p ∈ J.minimalPrimes, f ∉ p) :
    ringKrullDim (A ⧸ (J.radical ⊔ Ideal.span {f})) + 1 ≤ ringKrullDim (A ⧸ J) := by
  refine le_trans ?_ (ringKrullDim_le_of_surjective (Ideal.Quotient.factor J.le_radical)
    (Ideal.Quotient.factor_surjective _))
  refine ringKrullDim_succ_le_of_surjective (Ideal.Quotient.factor le_sup_left)
    (Ideal.Quotient.factor_surjective _) (r := Ideal.Quotient.mk _ f) ?_ ?_
  · rw [mem_nonZeroDivisors_iff_right]
    intro x hx
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem, ← Ideal.sInf_minimalPrimes,
      Ideal.mem_sInf] at hx
    rw [Ideal.Quotient.eq_zero_iff_mem, ← Ideal.sInf_minimalPrimes, Ideal.mem_sInf]
    intro p hp
    exact (hp.1.1.mem_or_mem (hx hp)).resolve_right (hf p hp)
  · rw [Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_sup_right (Ideal.mem_span_singleton_self f)

section Poly

variable {σ : Type*}

theorem mem_idealOfVars_pow_of_isHomogeneous {R : Type*} [CommRing R] {p : MvPolynomial σ R}
    {d n : ℕ} (hp : p.IsHomogeneous d) (h : n ≤ d) : p ∈ idealOfVars σ R ^ n := by
  rw [mem_pow_idealOfVars_iff']
  intro x hx
  exact hp.coeff_eq_zero (by omega)

theorem le_idealOfVars_of_isHomogeneous {k : Type*} [Field k] {J : Ideal (MvPolynomial σ k)}
    (hJ : J.IsHomogeneous (homogeneousSubmodule σ k)) (hJ' : J ≠ ⊤) : J ≤ idealOfVars σ k := by
  intro x hx
  rw [← pow_one (idealOfVars σ k), mem_pow_idealOfVars_iff']
  intro m hm
  have hm0 : m = 0 := by
    rw [← Finsupp.degree_eq_zero_iff]; omega
  subst hm0
  by_contra hne
  have h0 := homogeneousComponent_mem_of_mem hJ hx 0
  rw [homogeneousComponent_zero] at h0
  exact hJ' (J.eq_top_of_isUnit_mem h0 ((Ne.isUnit hne).map C))

theorem idealOfVars_ne_top {k : Type*} [Field k] : idealOfVars σ k ≠ ⊤ := fun h => by
  have := (mem_pow_idealOfVars_iff' 1 (1 : MvPolynomial σ k)).mp (by simp [h]) 0 (by simp)
  simp at this

variable [Finite σ] {k : Type*} [Field k]

theorem exists_form_forall_notMem_minimalPrimes {J : Ideal (MvPolynomial σ k)}
    (hJ : J.IsHomogeneous (homogeneousSubmodule σ k)) (h : ¬ idealOfVars σ k ≤ J.radical) :
    ∃ n, 0 < n ∧ ∃ f : MvPolynomial σ k, f.IsHomogeneous n ∧ ∀ p ∈ J.minimalPrimes, f ∉ p := by
  have hfin := J.finite_minimalPrimes_of_isNoetherianRing
  have hhom : ∀ p ∈ J.minimalPrimes, p.IsHomogeneous (homogeneousSubmodule σ k) :=
    fun p hp => isHomogeneous_of_mem_minimalPrimes _ hJ hp
  obtain ⟨q, hq, hqm⟩ : ∃ q ∈ J.minimalPrimes, ¬ idealOfVars σ k ≤ q := by
    by_contra hcon
    push Not at hcon
    exact h (by rw [← Ideal.sInf_minimalPrimes]; exact le_sInf hcon)
  have hnle : ∀ p ∈ J.minimalPrimes, ¬ idealOfVars σ k ≤ p := by
    intro p hp hle
    have hqp : q ≤ p := (le_idealOfVars_of_isHomogeneous (hhom q hq) hq.1.1.ne_top).trans hle
    exact hqm (hle.trans (hp.2 hq.1 hqp))
  obtain ⟨n, hn, f, hf, hfp⟩ := exists_homogeneous_forall_notMem (homogeneousSubmodule σ k)
    hfin.toFinset (fun p hp => (hfin.mem_toFinset.mp hp).1.1)
    (fun p hp => hhom p (hfin.mem_toFinset.mp hp))
    (fun p hp q hq hqp => le_antisymm hqp
      ((hfin.mem_toFinset.mp hp).2 (hfin.mem_toFinset.mp hq).1 hqp))
    (fun p hp => by
      have h1 := hnle p (hfin.mem_toFinset.mp hp)
      rw [Ideal.span_le, Set.range_subset_iff] at h1
      push Not at h1
      obtain ⟨i, hi⟩ := h1
      exact ⟨1, one_pos, X i, isHomogeneous_X k i, hi⟩)
  exact ⟨n, hn, f, hf, fun p hp => hfp p (hfin.mem_toFinset.mpr hp)⟩

theorem exists_forms_idealOfVars_le_radical (n : ℕ) :
    ∀ (J : Ideal (MvPolynomial σ k)), J.IsHomogeneous (homogeneousSubmodule σ k) → J ≠ ⊤ →
      ringKrullDim (MvPolynomial σ k ⧸ J) ≤ n →
      ∃ e, 0 < e ∧ ∃ F : Fin n → MvPolynomial σ k, (∀ i, (F i).IsHomogeneous e) ∧
        idealOfVars σ k ≤ (J ⊔ Ideal.span (Set.range F)).radical := by
  have step : ∀ (J : Ideal (MvPolynomial σ k)), J.IsHomogeneous (homogeneousSubmodule σ k) →
      J ≠ ⊤ → ¬ idealOfVars σ k ≤ J.radical →
      ∃ m, 0 < m ∧ ∃ f : MvPolynomial σ k, f.IsHomogeneous m ∧
        (J.radical ⊔ Ideal.span {f}).IsHomogeneous (homogeneousSubmodule σ k) ∧
        J.radical ⊔ Ideal.span {f} ≠ ⊤ ∧
        ringKrullDim (MvPolynomial σ k ⧸ (J.radical ⊔ Ideal.span {f})) + 1 ≤
          ringKrullDim (MvPolynomial σ k ⧸ J) := by
    intro J hJ hJ' h
    obtain ⟨m, hm, f, hf, hfp⟩ := exists_form_forall_notMem_minimalPrimes hJ h
    refine ⟨m, hm, f, hf, ?_, ?_, ringKrullDim_quotient_radical_sup_succ_le J hfp⟩
    · refine hJ.radical.sup (Ideal.homogeneous_span _ _ ?_)
      rintro x rfl
      exact ⟨m, hf⟩
    · refine ne_top_of_le_ne_top idealOfVars_ne_top (sup_le ?_ ?_)
      · exact le_idealOfVars_of_isHomogeneous hJ.radical (by rwa [Ne, Ideal.radical_eq_top])
      · rw [Ideal.span_singleton_le_iff_mem, ← pow_one (idealOfVars σ k)]
        exact mem_idealOfVars_pow_of_isHomogeneous hf hm
  induction n with
  | zero =>
    intro J hJ hJ' hdim
    by_cases h : idealOfVars σ k ≤ J.radical
    · exact ⟨1, one_pos, 0, fun i => isHomogeneous_zero _ _ _,
        h.trans (Ideal.radical_mono le_sup_left)⟩
    · exfalso
      obtain ⟨m, hm, f, hf, h1, h2, h3⟩ := step J hJ hJ' h
      haveI := Ideal.Quotient.nontrivial_iff.mpr h2
      have h4 := (add_le_add_left (ringKrullDim_nonneg_of_nontrivial
        (R := MvPolynomial σ k ⧸ (J.radical ⊔ Ideal.span {f}))) 1).trans (h3.trans hdim)
      rw [zero_add, Nat.cast_zero] at h4
      exact absurd h4 (not_le.mpr zero_lt_one)
  | succ n ih =>
    intro J hJ hJ' hdim
    by_cases h : idealOfVars σ k ≤ J.radical
    · exact ⟨1, one_pos, 0, fun i => isHomogeneous_zero _ _ _,
        h.trans (Ideal.radical_mono le_sup_left)⟩
    · obtain ⟨m, hm, f, hf, h1, h2, h3⟩ := step J hJ hJ' h
      have h4 : ringKrullDim (MvPolynomial σ k ⧸ (J.radical ⊔ Ideal.span {f})) ≤ n := by
        have h5 := h3.trans hdim
        rw [Nat.cast_add, Nat.cast_one] at h5
        exact (ENat.WithBot.add_le_add_one_right_iff).mp h5
      obtain ⟨e, he, F, hF, hle⟩ := ih _ h1 h2 h4
      refine ⟨e * m, Nat.mul_pos he hm, Fin.cons (f ^ e) (fun i => F i ^ m), ?_, ?_⟩
      · intro i
        refine Fin.cases ?_ (fun i => ?_) i
        · simpa [mul_comm] using hf.pow e
        · simpa using (hF i).pow m
      · refine hle.trans ?_
        rw [Ideal.radical_le_radical_iff]
        refine sup_le (sup_le (Ideal.radical_mono le_sup_left) ?_) ?_
        · rw [Ideal.span_singleton_le_iff_mem]
          exact ⟨e, Ideal.mem_sup_right (Ideal.subset_span ⟨0, rfl⟩)⟩
        · rw [Ideal.span_le, Set.range_subset_iff]
          intro i
          exact ⟨m, Ideal.mem_sup_right (Ideal.subset_span ⟨i.succ, rfl⟩)⟩

end Poly

section AnyBase

variable {σ ι R S : Type*} [CommRing R] [Fintype ι] [CommRing S] [Algebra R S]

theorem exists_forms_sub_sum_mem {I : Ideal (MvPolynomial σ R)}
    (hI : I.IsHomogeneous (homogeneousSubmodule σ R)) {F : ι → MvPolynomial σ R} {e N d : ℕ}
    (hF : ∀ i, (F i).IsHomogeneous e)
    (hN : idealOfVars σ R ^ N ≤ I ⊔ Ideal.span (Set.range F)) (hNd : N ≤ d) (hed : e ≤ d)
    {p : MvPolynomial σ R} (hp : p.IsHomogeneous d) :
    ∃ G : ι → MvPolynomial σ R, (∀ i, (G i).IsHomogeneous (d - e)) ∧ p - ∑ i, F i * G i ∈ I := by
  obtain ⟨a, ha, b, hb, hab⟩ :=
    Submodule.mem_sup.mp (hN (mem_idealOfVars_pow_of_isHomogeneous hp hNd))
  obtain ⟨c, rfl⟩ := Ideal.mem_span_range_iff_exists_fun.mp hb
  refine ⟨fun i => homogeneousComponent (d - e) (c i),
    fun i => homogeneousComponent_isHomogeneous _ _, ?_⟩
  have h1 : ∀ i, homogeneousComponent d (c i * F i) =
      F i * homogeneousComponent (d - e) (c i) := by
    intro i
    have := DirectSum.coe_decompose_mul_of_left_mem_of_le (homogeneousSubmodule σ R)
      (b := c i) (hF i) hed
    rw [mul_comm]
    exact (decomposition.decompose'_apply _ _).symm.trans
      (this.trans (congrArg _ (decomposition.decompose'_apply _ _)))
  have h2 := congrArg (homogeneousComponent d) hab
  rw [map_add, map_sum, homogeneousComponent_eq_self hp] at h2
  simp only [h1] at h2
  rw [← h2, add_sub_cancel_right]
  exact homogeneousComponent_mem_of_mem hI ha d

theorem finite_aeval_of_forms_eq_sum [Finite σ] (π : MvPolynomial σ R →ₐ[R] S)
    (hπ : Function.Surjective π) (f : ι → S) {e d₀ : ℕ} (he : 0 < e) (hed : e ≤ d₀)
    (h : ∀ d, d₀ ≤ d → ∀ p : MvPolynomial σ R, p.IsHomogeneous d →
      ∃ G : ι → MvPolynomial σ R,
        (∀ i, (G i).IsHomogeneous (d - e)) ∧ π p = ∑ i, f i * π (G i)) :
    (aeval f : MvPolynomial ι R →ₐ[R] S).Finite := by
  classical
  letI : Algebra (MvPolynomial ι R) S := (aeval f : MvPolynomial ι R →ₐ[R] S).toRingHom.toAlgebra
  haveI : IsScalarTower R (MvPolynomial ι R) S :=
    IsScalarTower.of_algebraMap_eq fun r => ((aeval f : MvPolynomial ι R →ₐ[R] S).commutes r).symm
  obtain ⟨t, ht⟩ : (restrictTotalDegree σ R d₀).FG := Module.Finite.iff_fg.mp inferInstance
  let M : Submodule (MvPolynomial ι R) S := Submodule.span _ (π '' t)
  have hlow : ∀ p ∈ restrictTotalDegree σ R d₀, π p ∈ M := by
    intro p hp
    rw [← ht] at hp
    have h1 : π p ∈ Submodule.span R (π '' t) := by
      have := Submodule.mem_map_of_mem (f := π.toLinearMap) hp
      rwa [Submodule.map_span] at this
    exact Submodule.span_le_restrictScalars R (MvPolynomial ι R) _ h1
  have hall : ∀ d, ∀ p : MvPolynomial σ R, p.IsHomogeneous d → π p ∈ M := by
    intro d
    induction d using Nat.strong_induction_on with
    | _ d ih =>
      intro p hp
      by_cases hd : d₀ ≤ d
      · obtain ⟨G, hG, hs⟩ := h d hd p hp
        rw [hs]
        refine M.sum_mem fun i _ => ?_
        have h2 := M.smul_mem (X i) (ih (d - e) (by omega) _ (hG i))
        have h3 : algebraMap (MvPolynomial ι R) S (X i) = f i := aeval_X f i
        rwa [Algebra.smul_def, h3] at h2
      · exact hlow p ((mem_restrictTotalDegree _ _ _).mpr (hp.totalDegree_le.trans (by omega)))
  change Module.Finite (MvPolynomial ι R) S
  refine ⟨⟨t.image π, ?_⟩⟩
  rw [Finset.coe_image, eq_top_iff]
  intro y _
  obtain ⟨p, rfl⟩ := hπ y
  rw [← sum_homogeneousComponent p, map_sum]
  exact M.sum_mem fun i _ => hall i _ (homogeneousComponent_isHomogeneous _ _)

end AnyBase

theorem injective_of_finite_of_ringKrullDim_eq {k S : Type*} [Field k] [CommRing S] {δ : ℕ}
    (φ : MvPolynomial (Fin δ) k →+* S) (hφ : φ.Finite) (hdim : ringKrullDim S = δ) :
    Function.Injective φ := by
  rw [injective_iff_map_eq_zero]
  intro r hr
  by_contra hne
  letI := φ.toAlgebra
  haveI : Module.Finite (MvPolynomial (Fin δ) k) S := hφ
  have h1 := ReciprocityTheory.CA.ringKrullDim_quotient_eq_quotient_comap_of_isIntegral
    (A := MvPolynomial (Fin δ) k) (⊥ : Ideal S)
  rw [ringKrullDim_eq_of_ringEquiv (RingEquiv.quotientBot S), hdim] at h1
  have h2 := ringKrullDim_succ_le_of_surjective
    (Ideal.Quotient.mk ((⊥ : Ideal S).comap (algebraMap (MvPolynomial (Fin δ) k) S)))
    Ideal.Quotient.mk_surjective (mem_nonZeroDivisors_of_ne_zero hne)
    (Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_comap.mpr (Ideal.mem_bot.mpr hr)))
  rw [← h1, MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field,
    zero_add, Nat.card_eq_fintype_card, Fintype.card_fin] at h2
  have h3 : δ + 1 ≤ δ := by exact_mod_cast h2
  omega

section Main

variable {σ : Type*} [Finite σ] {k : Type*} [Field k]

theorem exists_ringKrullDim_quotient_mvPolynomial_eq_nat {I : Ideal (MvPolynomial σ k)}
    (hI : I ≠ ⊤) : ∃ δ : ℕ, ringKrullDim (MvPolynomial σ k ⧸ I) = δ := by
  haveI := Ideal.Quotient.nontrivial_iff.mpr hI
  have h0 := ringKrullDim_nonneg_of_nontrivial (R := MvPolynomial σ k ⧸ I)
  have h1 := ringKrullDim_quotient_le I
  rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field,
    zero_add] at h1
  generalize ringKrullDim (MvPolynomial σ k ⧸ I) = x at h0 h1
  induction x with
  | bot => simp at h0
  | coe x =>
    induction x with
    | top => exact absurd h1 (not_le.mpr (by exact_mod_cast ENat.coe_lt_top _))
    | coe n => exact ⟨n, rfl⟩

theorem exists_forms_algebraicIndependent_finite {I : Ideal (MvPolynomial σ k)}
    (hI : I.IsHomogeneous (homogeneousSubmodule σ k)) {δ : ℕ}
    (hdim : ringKrullDim (MvPolynomial σ k ⧸ I) = δ) :
    ∃ (e d₀ : ℕ) (F : Fin δ → MvPolynomial σ k), 1 ≤ e ∧ e ≤ d₀ ∧
      (∀ i, (F i).IsHomogeneous e) ∧
      AlgebraicIndependent k (fun i => Ideal.Quotient.mk I (F i)) ∧
      (∀ d, d₀ ≤ d → ∀ p : MvPolynomial σ k, p.IsHomogeneous d →
        ∃ G : Fin δ → MvPolynomial σ k,
          (∀ i, (G i).IsHomogeneous (d - e)) ∧ p - ∑ i, F i * G i ∈ I) ∧
      (aeval (fun i => Ideal.Quotient.mk I (F i)) :
        MvPolynomial (Fin δ) k →ₐ[k] MvPolynomial σ k ⧸ I).Finite := by
  have hI' : I ≠ ⊤ := by
    rintro rfl
    rw [ringKrullDim_eq_bot_of_subsingleton] at hdim
    exact absurd hdim (WithBot.bot_ne_coe (a := (δ : ℕ∞)))
  obtain ⟨e, he, F, hF, hle⟩ := exists_forms_idealOfVars_le_radical δ I hI hI' hdim.le
  obtain ⟨N, hN⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hle (idealOfVars_fg σ k)
  have hgen : ∀ d, max N e ≤ d → ∀ p : MvPolynomial σ k, p.IsHomogeneous d →
      ∃ G : Fin δ → MvPolynomial σ k,
        (∀ i, (G i).IsHomogeneous (d - e)) ∧ p - ∑ i, F i * G i ∈ I := fun d hd p hp =>
    exists_forms_sub_sum_mem hI hF hN (le_of_max_le_left hd) (le_of_max_le_right hd) hp
  have hfin : (aeval (fun i => Ideal.Quotient.mk I (F i)) :
      MvPolynomial (Fin δ) k →ₐ[k] MvPolynomial σ k ⧸ I).Finite := by
    refine finite_aeval_of_forms_eq_sum (Ideal.Quotient.mkₐ k I) (Ideal.Quotient.mkₐ_surjective k I)
      _ he (le_max_right N e) fun d hd p hp => ?_
    obtain ⟨G, hG, hs⟩ := hgen d hd p hp
    refine ⟨G, hG, ?_⟩
    have := Ideal.Quotient.eq.mpr hs
    simpa using this
  exact ⟨e, max N e, F, he, le_max_right N e, hF,
    injective_of_finite_of_ringKrullDim_eq _ hfin hdim, hgen, hfin⟩

example : (Ideal.span {(X 0 * X 1 : MvPolynomial (Fin 2) (ZMod 2))}).IsHomogeneous
      (homogeneousSubmodule (Fin 2) (ZMod 2)) ∧
    Ideal.span {(X 0 * X 1 : MvPolynomial (Fin 2) (ZMod 2))} ≠ ⊤ := by
  have h : (X 0 * X 1 : MvPolynomial (Fin 2) (ZMod 2)).IsHomogeneous (1 + 1) :=
    (isHomogeneous_X _ 0).mul (isHomogeneous_X _ 1)
  refine ⟨Ideal.homogeneous_span _ _ (by rintro x rfl; exact ⟨_, h⟩),
    ne_top_of_le_ne_top idealOfVars_ne_top ?_⟩
  rw [Ideal.span_singleton_le_iff_mem, ← pow_one (idealOfVars _ _)]
  exact mem_idealOfVars_pow_of_isHomogeneous h (by norm_num)

end Main

end GlobalTheory
