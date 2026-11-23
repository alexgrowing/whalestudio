import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsMultiHomogeneousFixFirstBlock

set_option autoImplicit false

open MvPolynomial GlobalTheory.ChowHt

attribute [local instance] MvPolynomial.gradedAlgebra

namespace GlobalTheory.ChowHt.Associativity

section Length

variable {A : Type} [CommRing A]

theorem length_quotient_eq_sup_add_colon (K : Ideal A) (f : A) :
    Module.length A (A ⧸ K) =
      Module.length A (A ⧸ Submodule.colon K {f}) +
        Module.length A (A ⧸ (K ⊔ Ideal.span {f})) := by
  have hmap : Submodule.colon K {f} ≤ Submodule.comap (LinearMap.lsmul A A f) K := by
    intro x hx
    have := Submodule.mem_colon_singleton.1 hx
    rw [smul_eq_mul, mul_comm] at this
    exact this
  let g : (A ⧸ Submodule.colon K {f}) →ₗ[A] (A ⧸ K) :=
    Submodule.mapQ _ _ (LinearMap.lsmul A A f) hmap
  have hle : K ≤ K ⊔ Ideal.span {f} := le_sup_left
  let h : (A ⧸ K) →ₗ[A] (A ⧸ (K ⊔ Ideal.span {f})) := Submodule.factor hle
  have hg : Function.Injective g := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro x hx
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    have hx' : (Submodule.Quotient.mk (f • x) : A ⧸ K) = 0 := hx
    rw [Submodule.Quotient.mk_eq_zero] at hx'
    rw [Submodule.mem_bot, Submodule.Quotient.mk_eq_zero]
    refine Submodule.mem_colon_singleton.2 ?_
    rw [smul_eq_mul, mul_comm]
    exact hx'
  have hex : Function.Exact g h := by
    intro y
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    constructor
    · intro hy
      have hy' : (Submodule.Quotient.mk y : A ⧸ (K ⊔ Ideal.span {f})) = 0 := hy
      rw [Submodule.Quotient.mk_eq_zero] at hy'
      obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hy'
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hb
      refine ⟨Submodule.Quotient.mk c, ?_⟩
      change (Submodule.Quotient.mk (f • c) : A ⧸ K) = Submodule.Quotient.mk (a + c * f)
      rw [Submodule.Quotient.eq]
      have : f • c - (a + c * f) = -a := by rw [smul_eq_mul]; ring
      rw [this]
      exact K.neg_mem ha
    · rintro ⟨z, hz⟩
      obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ z
      rw [← hz]
      change (Submodule.Quotient.mk (f • z) : A ⧸ (K ⊔ Ideal.span {f})) = 0
      rw [Submodule.Quotient.mk_eq_zero, smul_eq_mul]
      exact Ideal.mem_sup_right (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self f))
  exact Module.length_eq_add_of_exact g h hg (Submodule.factor_surjective hle) hex

theorem map_colon_singleton {B : Type} [CommRing B] [Algebra A B] (M : Submonoid A)
    [IsLocalization M B] (I : Ideal A) (f : A) :
    (Submodule.colon I {f}).map (algebraMap A B) =
      Submodule.colon (I.map (algebraMap A B)) {algebraMap A B f} := by
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    intro x hx
    rw [Ideal.mem_comap, Submodule.mem_colon_singleton, smul_eq_mul, ← map_mul]
    have := Submodule.mem_colon_singleton.1 hx
    rw [smul_eq_mul] at this
    exact Ideal.mem_map_of_mem _ this
  · intro x hx
    rw [Submodule.mem_colon_singleton, smul_eq_mul] at hx
    obtain ⟨⟨r, s⟩, hrs⟩ := IsLocalization.surj M x
    simp only at hrs
    have h1 : algebraMap A B (f * r) ∈ I.map (algebraMap A B) := by
      rw [map_mul, ← hrs, mul_comm, mul_assoc, mul_comm (algebraMap A B s), ← mul_assoc]
      exact Ideal.mul_mem_right _ _ hx
    obtain ⟨⟨i, t⟩, hit⟩ := (IsLocalization.mem_map_algebraMap_iff M B).1 h1
    simp only at hit
    rw [← map_mul] at hit
    obtain ⟨c, hc⟩ := (IsLocalization.eq_iff_exists M B).1 hit
    have h2 : (c : A) * t * r ∈ Submodule.colon I {f} := by
      rw [Submodule.mem_colon_singleton, smul_eq_mul]
      have : (c : A) * t * r * f = c * (f * r * t) := by ring
      rw [this, hc]
      exact I.mul_mem_left _ i.2
    have h3 := Ideal.mem_map_of_mem (algebraMap A B) h2
    have h4 : algebraMap A B ((c : A) * t * r) = algebraMap A B ((c * t * s : M) : A) * x := by
      rw [map_mul _ _ r, ← hrs]
      simp only [Submonoid.coe_mul, map_mul]
      ring
    rw [h4] at h3
    exact (Ideal.unit_mul_mem_iff_mem _ (IsLocalization.map_units B (c * t * s))).1 h3

end Length

section LocalLength

variable {R : Type} [CommRing R]

theorem localLength_eq_colon_add_sup (I Q : Ideal R) [Q.IsPrime] (f : R) :
    localLength I Q = localLength (Submodule.colon I {f}) Q +
      localLength (I ⊔ Ideal.span {f}) Q := by
  have h := length_quotient_eq_sup_add_colon
    (I.map (algebraMap R (Localization.AtPrime Q))) (algebraMap R (Localization.AtPrime Q) f)
  rw [← map_colon_singleton Q.primeCompl] at h
  have e : (I ⊔ Ideal.span {f}).map (algebraMap R (Localization.AtPrime Q)) =
      I.map (algebraMap R (Localization.AtPrime Q)) ⊔
        Ideal.span {algebraMap R (Localization.AtPrime Q) f} := by
    rw [Ideal.map_sup, Ideal.map_span, Set.image_singleton]
  rw [← e] at h
  exact h

theorem localLength_eq_zero {I Q : Ideal R} [Q.IsPrime] (h : ¬ I ≤ Q) : localLength I Q = 0 := by
  obtain ⟨a, ha, haQ⟩ := SetLike.not_le_iff_exists.1 h
  rw [localLength, Module.length_eq_zero_iff, Ideal.Quotient.subsingleton_iff]
  have hu : IsUnit (algebraMap R (Localization.AtPrime Q) a) :=
    IsLocalization.map_units _ (⟨a, haQ⟩ : Q.primeCompl)
  exact Ideal.eq_top_of_isUnit_mem _ (Ideal.mem_map_of_mem _ ha) hu

open Classical in

noncomputable def lenAt (I Q : Ideal R) : ℕ :=
  if h : Q.IsPrime then (haveI := h; localLength I Q).toNat else 0

theorem lenAt_of_isPrime (I Q : Ideal R) [h : Q.IsPrime] : lenAt I Q = (localLength I Q).toNat := by
  rw [lenAt, dif_pos h]

theorem localLength_ne_top_of_le [IsNoetherianRing R] {J I Q : Ideal R} [Q.IsPrime]
    (hQ : Q ∈ J.minimalPrimes) (hJ : J ≤ I) : localLength I Q ≠ ⊤ := by
  by_cases h : I ≤ Q
  · exact localLength_ne_top ⟨⟨inferInstance, h⟩, fun R' hR hle => hQ.2 ⟨hR.1, hJ.trans hR.2⟩ hle⟩
  · rw [localLength_eq_zero h]
    simp

theorem lenAt_eq_colon_add_sup [IsNoetherianRing R] {J I Q : Ideal R}
    (hQ : Q ∈ J.minimalPrimes) (hJ : J ≤ I) (f : R) :
    lenAt I Q = lenAt (Submodule.colon I {f}) Q + lenAt (I ⊔ Ideal.span {f}) Q := by
  haveI : Q.IsPrime := hQ.1.1
  have hc : J ≤ Submodule.colon I {f} := fun x hx => Submodule.mem_colon_singleton.2 (by
    rw [smul_eq_mul]; exact I.mul_mem_right _ (hJ hx))
  rw [lenAt_of_isPrime, lenAt_of_isPrime, lenAt_of_isPrime, localLength_eq_colon_add_sup I Q f,
    ENat.toNat_add (localLength_ne_top_of_le hQ hc)
      (localLength_ne_top_of_le hQ (hJ.trans le_sup_left))]

end LocalLength

section Hilbert

variable {k : Type} [Field k] {N : ℕ}

local notation "S" => MvPolynomial (Fin N) k

theorem ringKrullDim_quotient_mono {I J : Ideal S} (h : I ≤ J) :
    ringKrullDim (S ⧸ J) ≤ ringKrullDim (S ⧸ I) :=
  ringKrullDim_le_of_surjective _ (Ideal.Quotient.factor_surjective h)

theorem ringKrullDim_quotient_add_one_le {P I : Ideal S} [P.IsPrime] (h : P < I) :
    ringKrullDim (S ⧸ I) + 1 ≤ ringKrullDim (S ⧸ P) := by
  obtain ⟨a, ha, haP⟩ := SetLike.exists_of_lt h
  exact ringKrullDim_succ_le_of_surjective (Ideal.Quotient.factor h.le)
    (Ideal.Quotient.factor_surjective _) (r := Ideal.Quotient.mk P a)
    (mem_nonZeroDivisors_of_ne_zero (by rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]))
    (by rw [Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem]; exact ha)

theorem coeff_idealHilbertPoly_eq_sum {J : Ideal S} {e : ℕ}
    (hd : ringKrullDim (S ⧸ J) ≤ (e + 1 : ℕ)) (T : Finset (Ideal S))
    (hT : ∀ Q ∈ T, Q ∈ J.minimalPrimes ∧ ringKrullDim (S ⧸ Q) = (e + 1 : ℕ))
    (hT' : ∀ Q ∈ J.minimalPrimes, ringKrullDim (S ⧸ Q) = (e + 1 : ℕ) → Q ∈ T)
    (I : Ideal S) (hI : I.IsHomogeneous (homogeneousSubmodule (Fin N) k)) (hJI : J ≤ I) :
    (idealHilbertPoly I).coeff e = ∑ Q ∈ T, (lenAt I Q : ℚ) * (idealHilbertPoly Q).coeff e := by
  induction I using IsNoetherian.induction with
  | _ I ih =>
  have hdI : ringKrullDim (S ⧸ I) ≤ (e + 1 : ℕ) := (ringKrullDim_quotient_mono hJI).trans hd
  by_cases htop : I = ⊤
  · subst htop
    rw [idealHilbertPoly_top, Polynomial.coeff_zero]
    symm
    refine Finset.sum_eq_zero fun Q hQ => ?_
    haveI : Ideal.IsPrime Q := (hT Q hQ).1.1.1
    rw [lenAt_of_isPrime, localLength_eq_zero (fun h => Ideal.IsPrime.ne_top ‹_› (top_le_iff.1 h))]
    simp
  by_cases hp : Ideal.IsPrime I
  · haveI := hp
    by_cases hdim : ringKrullDim (S ⧸ I) = (e + 1 : ℕ)
    ·
      have hIT : I ∈ T := by
        refine hT' I ?_ hdim
        obtain ⟨Q', hQ', hle⟩ := Ideal.exists_minimalPrimes_le hJI
        haveI : Q'.IsPrime := hQ'.1.1
        rcases hle.eq_or_lt with rfl | hlt
        · exact hQ'
        · have h1 := ringKrullDim_quotient_add_one_le hlt
          have h2 := ringKrullDim_quotient_mono hQ'.1.2
          have h3 := (h1.trans h2).trans hd
          rw [hdim] at h3
          exact absurd h3 (by exact_mod_cast (by omega : ¬ (e + 1 + 1 ≤ e + 1)))
      rw [Finset.sum_eq_single_of_mem I hIT]
      · rw [lenAt_of_isPrime, localLength_self]
        simp
      · intro Q hQ hne
        haveI : Ideal.IsPrime Q := (hT Q hQ).1.1.1
        have hnle : ¬ I ≤ Q := fun hle =>
          hne (le_antisymm ((hT Q hQ).1.2 ⟨hp, hJI⟩ hle) hle)
        rw [lenAt_of_isPrime, localLength_eq_zero hnle]
        simp
    ·
      obtain ⟨δ, hδ⟩ := exists_ringKrullDim_quotient_mvPolynomial_eq_nat htop
      have hδe : δ ≤ e := by
        have h1 : δ ≤ e + 1 := by rw [hδ] at hdI; exact_mod_cast hdI
        have h2 : δ ≠ e + 1 := fun h => hdim (by rw [hδ, h])
        omega
      have hco : (idealHilbertPoly I).coeff e = 0 :=
        Polynomial.coeff_eq_zero_of_degree_lt
          (degree_idealHilbertPoly_lt hI (m := e) (by rw [hδ]; exact_mod_cast hδe))
      rw [hco]
      symm
      refine Finset.sum_eq_zero fun Q hQ => ?_
      haveI : Ideal.IsPrime Q := (hT Q hQ).1.1.1
      have hnle : ¬ I ≤ Q := fun hle => by
        have := ringKrullDim_quotient_mono hle
        rw [(hT Q hQ).2, hδ] at this
        have h3 : e + 1 ≤ δ := by exact_mod_cast this
        omega
      rw [lenAt_of_isPrime, localLength_eq_zero hnle]
      simp
  · obtain ⟨d, f, hf, h1, h2⟩ := exists_form_lt_sup_lt_colon hI htop hp
    have hJ₁ := isHomogeneous_sup_span_singleton hI hf
    have hJ₂ := isHomogeneous_colon_singleton hI hf
    have hdeg : (idealHilbertPoly (Submodule.colon I {f})).degree ≤ (e : ℕ) := by
      have := degree_idealHilbertPoly_lt hJ₂
        ((ringKrullDim_quotient_mono h2.le).trans hdI)
      exact (Polynomial.degree_le_iff_coeff_zero _ _).2 fun m hm =>
        (Polynomial.degree_lt_iff_coeff_zero _ _).1 this m (by
          have : e < m := by exact_mod_cast hm
          omega)
    rw [idealHilbertPoly_eq_sup_add_colon hI hf, Polynomial.coeff_add,
      coeff_comp_X_sub_C_rat hdeg, ih _ h1 hJ₁ (hJI.trans h1.le), ih _ h2 hJ₂ (hJI.trans h2.le),
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun Q hQ => ?_
    rw [lenAt_eq_colon_add_sup (hT Q hQ).1 hJI f]
    push_cast
    ring

end Hilbert

theorem hilbertDegree_sup_eq_sum :
    ∀ {k : Type} [Field k] {N e : ℕ} {P : Ideal (MvPolynomial (Fin N) k)},
    P.IsHomogeneous (homogeneousSubmodule (Fin N) k) → P.IsPrime →
    ringKrullDim (MvPolynomial (Fin N) k ⧸ P) = (e + 1 + 1 : ℕ) →
    ∀ {u : Fin N → k}, hyperplaneForm u ∉ P →
    GlobalTheory.hilbertDegree (P ⊔ Ideal.span {hyperplaneForm u}) =
      (hyperplaneSection P u).sum (fun Q m => m * GlobalTheory.hilbertDegree Q) := by
  intro k _ N e P hP hp he u hu
  haveI := hp
  set J := P ⊔ Ideal.span {hyperplaneForm u} with hJdef
  have hℓ := isHomogeneous_hyperplaneForm u
  have hJ : J.IsHomogeneous (homogeneousSubmodule (Fin N) k) :=
    isHomogeneous_sup_span_singleton hP hℓ
  have hPJ : P < J := lt_of_le_of_ne le_sup_left fun h => hu (by
    rw [h]; exact Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))

  have hd : ringKrullDim (MvPolynomial (Fin N) k ⧸ J) ≤ (e + 1 : ℕ) := by
    by_cases htop : J = ⊤
    · rw [htop, ringKrullDim_eq_bot_of_subsingleton]
      exact bot_le
    · obtain ⟨δ, hδ⟩ := exists_ringKrullDim_quotient_mvPolynomial_eq_nat htop
      have h1 := ringKrullDim_quotient_add_one_le hPJ
      rw [he, hδ] at h1
      have h2 : δ + 1 ≤ e + 1 + 1 := by exact_mod_cast h1
      rw [hδ]
      exact_mod_cast (by omega : δ ≤ e + 1)

  have hmin : ∀ Q ∈ J.minimalPrimes, ringKrullDim (MvPolynomial (Fin N) k ⧸ Q) = (e + 1 : ℕ) := by
    intro Q hQ
    haveI : Q.IsPrime := hQ.1.1
    have h1 := ringKrullDim_quotient_add_one_of_mem_minimalPrimes_sup k hu hQ
    rw [he] at h1
    obtain ⟨δ, hδ⟩ := exists_ringKrullDim_quotient_mvPolynomial_eq_nat (Ideal.IsPrime.ne_top ‹Q.IsPrime›)
    rw [hδ] at h1 ⊢
    have h2 : δ + 1 = e + 1 + 1 := by exact_mod_cast h1
    obtain rfl : δ = e + 1 := by omega
    rfl
  have hsupp : ∀ Q, Q ∈ (hyperplaneSection P u).support ↔ Q ∈ J.minimalPrimes := by
    intro Q
    rw [hyperplaneSection, mem_support_projCycle]
    refine ⟨fun h => h.1, fun h => ⟨h, ?_⟩⟩
    by_contra hX
    push Not at hX
    have h1 := ringKrullDim_quotient_le_zero_of_forall_X_mem hX
    rw [hmin Q h] at h1
    exact absurd h1 (by exact_mod_cast (by omega : ¬ (e + 1 ≤ 0)))
  have key := coeff_idealHilbertPoly_eq_sum hd (hyperplaneSection P u).support
    (fun Q hQ => ⟨(hsupp Q).1 hQ, hmin Q ((hsupp Q).1 hQ)⟩)
    (fun Q hQ _ => (hsupp Q).2 hQ) J hJ le_rfl

  have hPdeg : (idealHilbertPoly P).degree = ((e + 1 : ℕ) : WithBot ℕ) :=
    degree_idealHilbertPoly_eq_of_isPrime hP he
  have hH := idealHilbertPoly_sup_of_isPrime hP hℓ hu
  have hc := coeff_sub_comp_X_sub_C (idealHilbertPoly P) (((1 : ℕ) : ℚ)) e hPdeg.le
  rw [← hH] at hc
  have hJdeg : (idealHilbertPoly J).degree = (e : ℕ) := by
    have hne : (idealHilbertPoly J).coeff e ≠ 0 := by
      rw [hc.2]
      have : (idealHilbertPoly P).coeff (e + 1) ≠ 0 := by
        have h0 : idealHilbertPoly P ≠ 0 := fun h => by
          rw [h, Polynomial.degree_zero] at hPdeg
          exact WithBot.bot_ne_natCast _ hPdeg
        rw [← Polynomial.natDegree_eq_of_degree_eq_some hPdeg]
        exact Polynomial.leadingCoeff_ne_zero.2 h0
      have h1 : ((e : ℚ) + 1) ≠ 0 := by positivity
      simpa using ⟨h1, this⟩
    refine le_antisymm ?_ (Polynomial.le_degree_of_ne_zero hne)
    exact (Polynomial.degree_le_iff_coeff_zero _ _).2 fun m hm =>
      (Polynomial.degree_lt_iff_coeff_zero _ _).1 hc.1 m (by
        have : e < m := by exact_mod_cast hm
        omega)
  have hcast := cast_hilbertDegree_of_degree_eq hJ hJdeg
  have : (GlobalTheory.hilbertDegree J : ℚ) =
      (((hyperplaneSection P u).sum (fun Q m => m * GlobalTheory.hilbertDegree Q) : ℕ) : ℚ) := by
    rw [hcast, key, Finsupp.sum, Nat.cast_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun Q hQ => ?_
    have hQm := (hsupp Q).1 hQ
    haveI : Q.IsPrime := hQm.1.1
    have hQh := isHomogeneous_of_mem_minimalPrimes _ hJ hQm
    have hQd := degree_idealHilbertPoly_eq_of_isPrime hQh (hmin Q hQm)
    have hm : lenAt J Q = hyperplaneSection P u Q := by
      have hcomp := mem_support_projCycle.1 hQ
      have h1 := cast_projCycle_apply hcomp
      rw [lenAt_of_isPrime, ← h1, ENat.toNat_coe]
      rfl
    rw [hm]
    push_cast
    rw [cast_hilbertDegree_of_degree_eq hQh hQd]
    ring
  exact_mod_cast this

end GlobalTheory.ChowHt.Associativity
