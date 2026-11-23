import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RingKrullDimQuotientAddOneOfMemMinimalPrimesSup

open Polynomial Filter Module DirectSum

namespace GlobalTheory

variable {K T : Type*} [Field K] [CommRing T] [Algebra K T] (𝒜 : ℕ → Submodule K T)

def extendGradingByZero : ℤ → Submodule K T
  | (n : ℕ) => 𝒜 n
  | Int.negSucc _ => ⊥

@[simp] theorem extendGradingByZero_natCast (n : ℕ) : extendGradingByZero 𝒜 n = 𝒜 n := rfl

@[simp] theorem extendGradingByZero_negSucc (n : ℕ) :
    extendGradingByZero 𝒜 (Int.negSucc n) = ⊥ := rfl

def gradedQuotPiece (J : Ideal T) (n : ℤ) : Submodule K (T ⧸ J) :=
  (extendGradingByZero 𝒜 n).map (Ideal.Quotient.mkₐ K J).toLinearMap

theorem gradedQuotPiece_natCast (J : Ideal T) (n : ℕ) :
    gradedQuotPiece 𝒜 J n = (𝒜 n).map (Ideal.Quotient.mkₐ K J).toLinearMap := rfl

open Classical in

noncomputable def gradedQuotHilbertPoly (J : Ideal T) : ℚ[X] :=
  if h : ∃ P, IsHilbertPoly (gradedQuotPiece 𝒜 J) P then h.choose else 0

noncomputable def gradedQuotDeg (r : ℕ) (J : Ideal T) : ℚ :=
  (r.factorial : ℚ) * (gradedQuotHilbertPoly 𝒜 J).coeff r

def relevantMinimalPrimes {ι : Type*} (x : ι → T) (J : Ideal T) : Set (Ideal T) :=
  {Q | Q ∈ J.minimalPrimes ∧ ∃ i, x i ∉ Q}

variable {𝒜} in
theorem IsHilbertPoly.gradedQuotHilbertPoly_eq {J : Ideal T} {P : ℚ[X]}
    (hP : IsHilbertPoly (gradedQuotPiece 𝒜 J) P) : gradedQuotHilbertPoly 𝒜 J = P := by
  have h : ∃ P, IsHilbertPoly (gradedQuotPiece 𝒜 J) P := ⟨P, hP⟩
  rw [gradedQuotHilbertPoly, dif_pos h]
  exact h.choose_spec.unique hP

namespace GradedBezout

section Finite

variable {ι : Type*} {x : ι → T} (hfin : Module.Finite (Algebra.adjoin K (Set.range x)) T)
include hfin

theorem finite_aeval : (MvPolynomial.aeval x : MvPolynomial ι K →ₐ[K] T).Finite := by
  rw [Algebra.adjoin_range_eq_range_aeval] at hfin
  exact RingHom.Finite.comp (g := algebraMap _ T)
    (f := (MvPolynomial.aeval x : MvPolynomial ι K →ₐ[K] T).rangeRestrict.toRingHom) hfin
    (RingHom.Finite.of_surjective _ (AlgHom.rangeRestrict_surjective _))

theorem ringKrullDim_quotient_eq_comap (I : Ideal T) : ringKrullDim (T ⧸ I) =
    ringKrullDim (MvPolynomial ι K ⧸
      I.comap (MvPolynomial.aeval x : MvPolynomial ι K →ₐ[K] T).toRingHom) := by
  letI : Algebra (MvPolynomial ι K) T :=
    (MvPolynomial.aeval x : MvPolynomial ι K →ₐ[K] T).toRingHom.toAlgebra
  haveI : Module.Finite (MvPolynomial ι K) T := finite_aeval hfin
  exact ReciprocityTheory.CA.ringKrullDim_quotient_eq_quotient_comap_of_isIntegral
    (A := MvPolynomial ι K) I

variable [Finite ι]

theorem finiteType : Algebra.FiniteType K T := by
  letI : Algebra (MvPolynomial ι K) T :=
    (MvPolynomial.aeval x : MvPolynomial ι K →ₐ[K] T).toRingHom.toAlgebra
  haveI : IsScalarTower K (MvPolynomial ι K) T := IsScalarTower.of_algebraMap_eq fun r =>
    ((MvPolynomial.aeval x : MvPolynomial ι K →ₐ[K] T).commutes r).symm
  haveI : Module.Finite (MvPolynomial ι K) T := finite_aeval hfin
  exact Algebra.FiniteType.trans (S := MvPolynomial ι K) inferInstance inferInstance

theorem isNoetherianRing : IsNoetherianRing T :=
  haveI := finiteType hfin
  Algebra.FiniteType.isNoetherianRing K T

theorem exists_ringKrullDim_quotient_eq_nat {I : Ideal T} (hI : I ≠ ⊤) :
    ∃ δ : ℕ, ringKrullDim (T ⧸ I) = δ := by
  rw [ringKrullDim_quotient_eq_comap hfin]
  exact exists_ringKrullDim_quotient_mvPolynomial_eq_nat (Ideal.comap_ne_top _ hI)

theorem ringKrullDim_quotient_le_zero {I : Ideal T} (h : ∀ i, x i ∈ I) :
    ringKrullDim (T ⧸ I) ≤ 0 := by
  rw [ringKrullDim_quotient_eq_comap hfin]
  exact ringKrullDim_quotient_le_zero_of_forall_X_mem fun i => by simpa using h i

end Finite

variable [GradedAlgebra 𝒜]

noncomputable def decomposeExtend : T →ₗ[K] ⨁ i, extendGradingByZero 𝒜 i :=
  (toModule K ℕ _ (M := fun n => 𝒜 n) fun n =>
    (lof K ℤ (fun i => extendGradingByZero 𝒜 i) (n : ℤ) : 𝒜 n →ₗ[K] _)) ∘ₗ
      (decomposeLinearEquiv 𝒜).toLinearMap

theorem decomposeExtend_coe (n : ℕ) (m : 𝒜 n) :
    decomposeExtend 𝒜 m = lof K ℤ (fun i => extendGradingByZero 𝒜 i) (n : ℤ) m := by
  change toModule K ℕ _ (M := fun n => 𝒜 n) _ (decompose 𝒜 (m : T)) = _
  rw [decompose_coe, ← lof_eq_of K]
  exact toModule_lof K (M := fun n => 𝒜 n) n m

@[reducible] noncomputable def decompositionExtend : Decomposition (extendGradingByZero 𝒜) :=
  Decomposition.ofLinearMap (extendGradingByZero 𝒜) (decomposeExtend 𝒜)
    (by
      ext t
      induction t using Decomposition.inductionOn 𝒜 with
      | zero => rw [map_zero, map_zero]
      | @homogeneous n m =>
        rw [LinearMap.comp_apply, decomposeExtend_coe]
        exact coeLinearMap_of (extendGradingByZero 𝒜) (n : ℤ) m
      | add a b ha hb => rw [map_add, map_add, ha, hb])
    (by
      ext1 i
      ext1 m
      cases i with
      | ofNat n =>
        exact (congrArg (decomposeExtend 𝒜) (coeLinearMap_of (extendGradingByZero 𝒜) _ m)).trans
          (decomposeExtend_coe 𝒜 n m)
      | negSucc n =>
        obtain rfl : m = 0 := Subtype.ext m.2
        rw [map_zero, map_zero])

variable {𝒜}

theorem isHomogeneous_sup_span {I : Ideal T} (hI : I.IsHomogeneous 𝒜) {f : T} {d : ℕ}
    (hf : f ∈ 𝒜 d) : (I ⊔ Ideal.span {f}).IsHomogeneous 𝒜 :=
  hI.sup (Ideal.homogeneous_span _ _ (by rintro x rfl; exact ⟨d, hf⟩))

theorem isHomogeneous_colon {I : Ideal T} (hI : I.IsHomogeneous 𝒜) {f : T} {d : ℕ}
    (hf : f ∈ 𝒜 d) : (Submodule.colon I {f}).IsHomogeneous 𝒜 := by
  intro n g hg
  rw [Submodule.mem_colon_singleton, smul_eq_mul] at hg ⊢
  rw [← coe_decompose_mul_add_of_right_mem 𝒜 (j := d) hf]
  exact hI _ hg

theorem sup_span_ne_top {I : Ideal T} (hI : I.IsHomogeneous 𝒜) (h : I ≠ ⊤) {f : T} {d : ℕ}
    (hf : f ∈ 𝒜 d) (hd : 0 < d) : I ⊔ Ideal.span {f} ≠ ⊤ := by
  intro htop
  obtain ⟨a, ha, _, hb, hab⟩ := Submodule.mem_sup.1 ((Ideal.eq_top_iff_one _).1 htop)
  obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.1 hb
  have h1 := congrArg (fun t => (decompose 𝒜 t 0 : T)) hab
  simp only [decompose_add, DirectSum.add_apply, Submodule.coe_add] at h1
  rw [coe_decompose_mul_of_right_mem_of_not_le 𝒜 hf (by omega), add_zero,
    decompose_of_mem_same 𝒜 (SetLike.one_mem_graded 𝒜)] at h1
  exact h ((Ideal.eq_top_iff_one _).2 (h1 ▸ hI 0 ha))

theorem exists_lt_sup_lt_colon {I : Ideal T} (hI : I.IsHomogeneous 𝒜) (h : I ≠ ⊤)
    (hp : ¬ I.IsPrime) : ∃ (d : ℕ) (f : T), f ∈ 𝒜 d ∧ I < I ⊔ Ideal.span {f} ∧
      I < Submodule.colon I {f} := by
  rw [hI.isPrime_iff] at hp
  push Not at hp
  obtain ⟨g, f, -, ⟨d, hf⟩, hgf, hg, hfI⟩ := hp h
  refine ⟨d, f, hf, lt_of_le_of_ne le_sup_left fun e => hfI ?_, lt_of_le_of_ne
    (fun x hx => Submodule.mem_colon_singleton.2 (I.mul_mem_right _ hx)) fun e => hg ?_⟩
  · rw [e]; exact Ideal.mem_sup_right (Ideal.mem_span_singleton_self f)
  · rw [e]; exact Submodule.mem_colon_singleton.2 hgf

variable {ι : Type*} [Finite ι] {x : ι → T} (hx : ∀ i, x i ∈ 𝒜 1)
  (hfin : Module.Finite (Algebra.adjoin K (Set.range x)) T)
include hx hfin

theorem exists_isHilbertPoly_gradedQuotPiece {I : Ideal T} (hI : I.IsHomogeneous 𝒜)
    (s : Finset ι) (hs : ∀ i ∉ s, x i ∈ I) :
    (∀ n, Module.Finite K (𝒜 n)) ∧
      ∃ P : ℚ[X], IsHilbertPoly (gradedQuotPiece 𝒜 I) P ∧ P.degree < (s.card : ℕ) := by
  classical
  letI : Algebra (MvPolynomial ι K) T :=
    (MvPolynomial.aeval x : MvPolynomial ι K →ₐ[K] T).toRingHom.toAlgebra
  haveI : IsScalarTower K (MvPolynomial ι K) T := IsScalarTower.of_algebraMap_eq fun r =>
    ((MvPolynomial.aeval x : MvPolynomial ι K →ₐ[K] T).commutes r).symm
  haveI : Module.Finite (MvPolynomial ι K) T := finite_aeval hfin
  letI := decompositionExtend 𝒜
  have hsm : ∀ i (m : T), (MvPolynomial.X i : MvPolynomial ι K) • m = x i * m := fun i m => by
    rw [Algebra.smul_def]
    exact congrArg (· * m) (MvPolynomial.aeval_X x i)
  have hX : ∀ (i : ι) (n : ℤ), ∀ m ∈ extendGradingByZero 𝒜 n,
      (MvPolynomial.X i : MvPolynomial ι K) • m ∈ extendGradingByZero 𝒜 (n + 1) := by
    intro i n m hm
    cases n with
    | ofNat n =>
      rw [hsm, mul_comm]
      exact SetLike.mul_mem_graded (i := n) hm (hx i)
    | negSucc n =>
      obtain rfl : m = 0 := hm
      simp
  have hpiece := GradedHilbert.finite_piece _ hX
  obtain ⟨P, hP, h⟩ := GradedHilbert.exists_polynomial_subquotient _ hX s
    (I.restrictScalars (MvPolynomial ι K)) ⊤ le_top
    (by
      intro n m hm
      rw [← sum_support_decompose 𝒜 m, map_sum]
      refine Submodule.sum_mem _ fun i _ => ?_
      have h1 : (decompose 𝒜 m i : T) ∈ extendGradingByZero 𝒜 i := SetLike.coe_mem _
      by_cases hi : (i : ℤ) = n
      · rw [← hi, GradedHilbert.proj_of_mem _ h1]
        exact hI i hm
      · rw [GradedHilbert.proj_of_mem_ne _ h1 hi]
        exact Submodule.zero_mem _) (by simp)
    (by
      intro i hi m _
      rw [hsm]
      exact I.mul_mem_right _ (hs i hi))
  refine ⟨fun n => hpiece n, P, ⟨fun n => ?_, ?_⟩, hP⟩
  · haveI := hpiece n
    unfold gradedQuotPiece
    infer_instance
  · filter_upwards [h] with n hn
    haveI := hpiece n
    have e := GradedHilbert.finrank_map_add_finrank_inf_ker (Ideal.Quotient.mkₐ K I).toLinearMap
      (extendGradingByZero 𝒜 n)
    have e2 : LinearMap.ker (Ideal.Quotient.mkₐ K I).toLinearMap =
        (I.restrictScalars (MvPolynomial ι K)).restrictScalars K := by
      ext x; simp [Ideal.Quotient.eq_zero_iff_mem]
    rw [e2, inf_comm] at e
    rw [Submodule.restrictScalars_top, top_inf_eq, ← e] at hn
    rw [← hn, gradedQuotPiece]
    push_cast
    ring

theorem finite_piece (n : ℕ) : Module.Finite K (𝒜 n) := by
  cases nonempty_fintype ι
  exact (exists_isHilbertPoly_gradedQuotPiece hx hfin (Ideal.IsHomogeneous.bot 𝒜) Finset.univ
    (by simp)).1 n

theorem isHilbertPoly {I : Ideal T} (hI : I.IsHomogeneous 𝒜) :
    IsHilbertPoly (gradedQuotPiece 𝒜 I) (gradedQuotHilbertPoly 𝒜 I) := by
  cases nonempty_fintype ι
  obtain ⟨P, hP, -⟩ :=
    (exists_isHilbertPoly_gradedQuotPiece hx hfin hI Finset.univ (by simp)).2
  rwa [hP.gradedQuotHilbertPoly_eq]

theorem hilbertPoly_eq_zero {I : Ideal T} (hI : I.IsHomogeneous 𝒜) (h : ∀ i, x i ∈ I) :
    gradedQuotHilbertPoly 𝒜 I = 0 := by
  obtain ⟨P, hP, hd⟩ :=
    (exists_isHilbertPoly_gradedQuotPiece hx hfin hI ∅ fun i _ => h i).2
  rw [hP.gradedQuotHilbertPoly_eq]
  ext m
  exact (degree_lt_iff_coeff_zero P _).1 hd m (by simp)

theorem eventually_finrank {I : Ideal T} (hI : I.IsHomogeneous 𝒜) :
    ∀ᶠ n : ℕ in atTop, (finrank K (gradedQuotPiece 𝒜 I n) : ℚ) =
      (gradedQuotHilbertPoly 𝒜 I).eval (n : ℚ) := by
  have := (tendsto_natCast_atTop_atTop (R := ℤ)).eventually
    (isHilbertPoly hx hfin hI).eventually_eq
  simpa using this

theorem eventually_nonneg {I : Ideal T} (hI : I.IsHomogeneous 𝒜) :
    ∀ᶠ n : ℕ in atTop, 0 ≤ (gradedQuotHilbertPoly 𝒜 I).eval (n : ℚ) := by
  filter_upwards [eventually_finrank hx hfin hI] with n hn
  rw [← hn]
  positivity

theorem finrank_piece_add (I : Ideal T) (n : ℕ) :
    finrank K (gradedQuotPiece 𝒜 I n) +
      finrank K (I.restrictScalars K ⊓ 𝒜 n : Submodule K _) = finrank K (𝒜 n) := by
  haveI := finite_piece hx hfin n
  have e := GradedHilbert.finrank_map_add_finrank_inf_ker (Ideal.Quotient.mkₐ K I).toLinearMap
    (𝒜 n)
  have e2 : LinearMap.ker (Ideal.Quotient.mkₐ K I).toLinearMap = I.restrictScalars K := by
    ext x; simp [Ideal.Quotient.eq_zero_iff_mem]
  rw [e2, inf_comm] at e
  rw [gradedQuotPiece_natCast, e]

theorem finrank_sup_add_colon {I : Ideal T} (hI : I.IsHomogeneous 𝒜) {f : T} {d : ℕ}
    (hf : f ∈ 𝒜 d) (n : ℕ) :
    finrank K (gradedQuotPiece 𝒜 (I ⊔ Ideal.span {f}) (n + d : ℕ)) +
      finrank K (gradedQuotPiece 𝒜 (Submodule.colon I {f}) n) =
      finrank K (gradedQuotPiece 𝒜 I (n + d : ℕ)) := by
  have h1 := finrank_piece_add hx hfin (I ⊔ Ideal.span {f}) (n + d)
  have h2 := finrank_piece_add hx hfin (Submodule.colon I {f}) n
  have h3 := finrank_piece_add hx hfin I (n + d)
  haveI := finite_piece hx hfin n
  haveI := finite_piece hx hfin (n + d)
  have e := GradedHilbert.finrank_sup_map_add_finrank_inf_comap (LinearMap.mulRight K f)
    (𝒜 n) (I.restrictScalars K ⊓ 𝒜 (n + d))
  have a₁ : (I ⊔ Ideal.span {f}).restrictScalars K ⊓ 𝒜 (n + d) =
      (I.restrictScalars K ⊓ 𝒜 (n + d)) ⊔ (𝒜 n).map (LinearMap.mulRight K f) := by
    apply le_antisymm
    · rintro m ⟨hm, hmn⟩
      obtain ⟨a, ha, _, hb, rfl⟩ := Submodule.mem_sup.1 hm
      obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.1 hb
      rw [← decompose_of_mem_same 𝒜 hmn, decompose_add, DirectSum.add_apply,
        Submodule.coe_add, coe_decompose_mul_add_of_right_mem _ (j := d) hf]
      exact Submodule.add_mem_sup ⟨hI _ ha, SetLike.coe_mem _⟩ ⟨_, SetLike.coe_mem _, rfl⟩
    · refine sup_le (inf_le_inf_right _ fun m hm => Submodule.mem_sup_left hm) ?_
      rintro _ ⟨m, hm, rfl⟩
      exact ⟨Ideal.mem_sup_right (Ideal.mem_span_singleton'.2 ⟨m, rfl⟩),
        SetLike.mul_mem_graded hm hf⟩
  have a₂ : (Submodule.colon I {f}).restrictScalars K ⊓ 𝒜 n =
      𝒜 n ⊓ (I.restrictScalars K ⊓ 𝒜 (n + d)).comap (LinearMap.mulRight K f) := by
    apply le_antisymm
    · rintro m ⟨hm, hmn⟩
      exact ⟨hmn, Submodule.mem_colon_singleton.1 hm, SetLike.mul_mem_graded hmn hf⟩
    · rintro m ⟨hm, hm', -⟩
      exact ⟨Submodule.mem_colon_singleton.2 hm', hm⟩
  rw [a₁] at h1
  rw [a₂] at h2
  omega

theorem hilbertPoly_eq_sup_add_colon {I : Ideal T} (hI : I.IsHomogeneous 𝒜) {f : T} {d : ℕ}
    (hf : f ∈ 𝒜 d) :
    gradedQuotHilbertPoly 𝒜 I = gradedQuotHilbertPoly 𝒜 (I ⊔ Ideal.span {f}) +
      (gradedQuotHilbertPoly 𝒜 (Submodule.colon I {f})).comp (X - C (d : ℚ)) := by
  apply polynomial_eq_of_eventually_eval_nat
  obtain ⟨N, hN⟩ := eventually_atTop.1 (eventually_finrank hx hfin (isHomogeneous_colon hI hf))
  filter_upwards [eventually_finrank hx hfin hI,
    eventually_finrank hx hfin (isHomogeneous_sup_span hI hf),
    eventually_ge_atTop (N + d)] with n h1 h2 h3
  obtain ⟨n, rfl⟩ : ∃ m, n = m + d := ⟨n - d, by omega⟩
  rw [eval_add, ← h1, ← h2, ← finrank_sup_add_colon hx hfin hI hf n, Nat.cast_add,
    hN n (by omega)]
  simp

theorem hilbertPoly_sup_of_isPrime {P : Ideal T} [hP : P.IsPrime] (hI : P.IsHomogeneous 𝒜)
    {f : T} {d : ℕ} (hf : f ∈ 𝒜 d) (hfP : f ∉ P) :
    gradedQuotHilbertPoly 𝒜 (P ⊔ Ideal.span {f}) = gradedQuotHilbertPoly 𝒜 P -
      (gradedQuotHilbertPoly 𝒜 P).comp (X - C (d : ℚ)) := by
  have h := hilbertPoly_eq_sup_add_colon hx hfin hI hf
  have e : Submodule.colon P {f} = P := by
    ext g
    rw [Submodule.mem_colon_singleton, smul_eq_mul, hP.mul_mem_iff_mem_or_mem]
    simp [hfP]
  rw [e] at h
  linear_combination -h

theorem degree_hilbertPoly_anti {I J : Ideal T} (hI : I.IsHomogeneous 𝒜)
    (hJ : J.IsHomogeneous 𝒜) (h : I ≤ J) :
    (gradedQuotHilbertPoly 𝒜 J).degree ≤ (gradedQuotHilbertPoly 𝒜 I).degree := by
  refine degree_le_of_eventually_eval_nat (eventually_nonneg hx hfin hJ) ?_
  filter_upwards [eventually_finrank hx hfin hI, eventually_finrank hx hfin hJ] with n h1 h2
  have h3 := finrank_piece_add hx hfin I n
  have h4 := finrank_piece_add hx hfin J n
  haveI := finite_piece hx hfin n
  have h5 : finrank K (I.restrictScalars K ⊓ 𝒜 n : Submodule K _) ≤
      finrank K (J.restrictScalars K ⊓ 𝒜 n : Submodule K _) :=
    Submodule.finrank_mono (inf_le_inf_right _ fun x hx => h hx)
  rw [← h1, ← h2]
  exact_mod_cast (by omega)

theorem hilbertPoly_ne_zero {P : Ideal T} [hP : P.IsPrime] (hI : P.IsHomogeneous 𝒜) {i : ι}
    (h : x i ∉ P) : gradedQuotHilbertPoly 𝒜 P ≠ 0 := by
  intro h0
  obtain ⟨n, hn⟩ := (eventually_finrank hx hfin hI).exists
  have := (isHilbertPoly hx hfin hI).finite n
  have hbot : gradedQuotPiece 𝒜 P n = ⊥ := by simpa [h0] using hn
  have hmem : Ideal.Quotient.mk P (x i ^ n) ∈ gradedQuotPiece 𝒜 P n :=
    ⟨x i ^ n, by simpa using SetLike.pow_mem_graded n (hx i), rfl⟩
  rw [hbot, Submodule.mem_bot, Ideal.Quotient.eq_zero_iff_mem] at hmem
  exact h (hP.mem_of_pow_mem _ hmem)

theorem hilbertPoly_top : gradedQuotHilbertPoly 𝒜 (⊤ : Ideal T) = 0 :=
  hilbertPoly_eq_zero hx hfin (Ideal.IsHomogeneous.top _) fun _ => trivial

theorem degree_hilbertPoly_lt {I : Ideal T} (hI : I.IsHomogeneous 𝒜) {m : ℕ}
    (hm : ringKrullDim (T ⧸ I) ≤ m) : (gradedQuotHilbertPoly 𝒜 I).degree < m := by
  haveI := isNoetherianRing hfin
  induction I using IsNoetherian.induction generalizing m with
  | _ I ih =>
  have mono : ∀ J, I ≤ J → ringKrullDim (T ⧸ J) ≤ m := fun J hJ =>
    (ringKrullDim_le_of_surjective _ (Ideal.Quotient.factor_surjective hJ)).trans hm
  by_cases htop : I = ⊤
  · rw [htop, hilbertPoly_top hx hfin]; simp
  by_cases hp : Ideal.IsPrime I
  · by_cases hX : ∀ i, x i ∈ I
    · rw [hilbertPoly_eq_zero hx hfin hI hX]; simp
    push Not at hX
    obtain ⟨i, hi⟩ := hX
    have hJ := isHomogeneous_sup_span hI (hx i)
    have hlt : I < I ⊔ Ideal.span {x i} := lt_of_le_of_ne le_sup_left fun e => hi (by
      rw [e]; exact Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
    obtain ⟨δ, hδ⟩ := exists_ringKrullDim_quotient_eq_nat hfin
      (sup_span_ne_top hI htop (hx i) one_pos)
    have h1 := ringKrullDim_succ_le_of_surjective (Ideal.Quotient.factor hlt.le)
      (Ideal.Quotient.factor_surjective _) (r := Ideal.Quotient.mk I (x i))
      (mem_nonZeroDivisors_of_ne_zero (by rwa [Ne, Ideal.Quotient.eq_zero_iff_mem])) (by
        rw [Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem]
        exact Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
    have h2 : δ + 1 ≤ m := by
      have := h1.trans hm
      rw [hδ] at this
      exact_mod_cast this
    have h3 := ih _ hlt hJ hδ.le
    rw [hilbertPoly_sup_of_isPrime hx hfin hI (hx i) hi, Nat.cast_one] at h3
    exact (degree_eq_of_degree_sub_comp h3).trans_lt (by exact_mod_cast h2)
  · obtain ⟨d, f, hf, h1, h2⟩ := exists_lt_sup_lt_colon hI htop hp
    rw [hilbertPoly_eq_sup_add_colon hx hfin hI hf]
    refine (degree_add_le _ _).trans_lt (max_lt
      (ih _ h1 (isHomogeneous_sup_span hI hf) (mono _ h1.le)) ?_)
    rw [degree_comp_X_sub_C_rat]
    exact ih _ h2 (isHomogeneous_colon hI hf) (mono _ h2.le)

theorem degree_hilbertPoly_eq_of_isPrime {P : Ideal T} [hP : P.IsPrime]
    (hI : P.IsHomogeneous 𝒜) {e : ℕ} (he : ringKrullDim (T ⧸ P) = (e + 1 : ℕ)) :
    (gradedQuotHilbertPoly 𝒜 P).degree = e := by
  haveI := finiteType hfin
  refine le_antisymm ((degree_le_iff_coeff_zero _ _).2 fun m hm =>
    (degree_lt_iff_coeff_zero _ _).1 (degree_hilbertPoly_lt hx hfin hI he.le) m
      (by exact_mod_cast hm)) ?_
  induction e generalizing P with
  | zero =>
    have : ¬ ∀ i, x i ∈ P := fun h => by
      have := ringKrullDim_quotient_le_zero hfin h
      rw [he] at this
      exact absurd this (by norm_num)
    push Not at this
    obtain ⟨i, hi⟩ := this
    exact zero_le_degree_iff.2 (hilbertPoly_ne_zero hx hfin hI hi)
  | succ e ih =>
    have : ¬ ∀ i, x i ∈ P := fun h => by
      have := ringKrullDim_quotient_le_zero hfin h
      rw [he] at this
      exact absurd this (by exact_mod_cast (by omega))
    push Not at this
    obtain ⟨i, hi⟩ := this
    have hJ := isHomogeneous_sup_span hI (hx i)
    obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ (sup_span_ne_top hI hP.ne_top (hx i) one_pos)
    obtain ⟨Q, hQ, -⟩ := Ideal.exists_minimalPrimes_le hle
    have : Q.IsPrime := hQ.1.1
    have hQh := isHomogeneous_of_mem_minimalPrimes _ hJ hQ
    obtain ⟨δ, hδ⟩ := exists_ringKrullDim_quotient_eq_nat hfin this.ne_top
    have h1 := ringKrullDim_quotient_add_one_of_mem_minimalPrimes_sup K hi hQ
    rw [he, hδ] at h1
    obtain rfl : δ = e + 1 := by
      have : δ + 1 = e + 1 + 1 := by exact_mod_cast h1
      omega
    have h2 := (ih hQh hδ).trans (degree_hilbertPoly_anti hx hfin hJ hQh hQ.1.2)
    rw [hilbertPoly_sup_of_isPrime hx hfin hI (hx i) hi] at h2
    by_contra hlt
    have h3 : (gradedQuotHilbertPoly 𝒜 P).degree ≤ e :=
      (degree_le_iff_coeff_zero _ _).2 fun m hm =>
        (degree_lt_iff_coeff_zero _ _).1 (not_le.1 hlt) m (by exact_mod_cast hm)
    have h4 := degree_comp_X_add_C_sub_lt _ (-((1 : ℕ) : ℚ)) e h3
    rw [C_neg, ← sub_eq_add_neg, ← degree_neg, neg_sub] at h4
    exact absurd h2 (not_le.2 h4)

theorem sum_coeff_hilbertPoly_le {I : Ideal T} (hI : I.IsHomogeneous 𝒜) {e : ℕ}
    (he : (gradedQuotHilbertPoly 𝒜 I).degree ≤ e) (s : Finset (Ideal T))
    (hs : ∀ Q ∈ s, Q ∈ I.minimalPrimes) :
    ∑ Q ∈ s, (gradedQuotHilbertPoly 𝒜 Q).coeff e ≤ (gradedQuotHilbertPoly 𝒜 I).coeff e := by
  classical
  haveI := isNoetherianRing hfin
  induction I using IsNoetherian.induction generalizing s with
  | _ I ih =>
  have h0 := coeff_nonneg_of_eventually_eval_nat he (eventually_nonneg hx hfin hI)
  by_cases htop : I = ⊤
  · subst htop
    obtain rfl : s = ∅ := Finset.eq_empty_of_forall_notMem fun Q hQ => by
      simpa [Ideal.minimalPrimes_top] using hs Q hQ
    simpa using h0
  by_cases hp : Ideal.IsPrime I
  · have : s ⊆ {I} := fun Q hQ => by
      simpa [Ideal.minimalPrimes_eq_subsingleton_self] using hs Q hQ
    rcases Finset.subset_singleton_iff.1 this with rfl | rfl
    · simpa using h0
    · simp
  obtain ⟨d, f, hf, h1, h2⟩ := exists_lt_sup_lt_colon hI htop hp
  have hJ₁ := isHomogeneous_sup_span hI hf
  have hJ₂ := isHomogeneous_colon hI hf
  have e₁ := (degree_hilbertPoly_anti hx hfin hI hJ₁ h1.le).trans he
  have e₂ := (degree_hilbertPoly_anti hx hfin hI hJ₂ h2.le).trans he
  rw [hilbertPoly_eq_sup_add_colon hx hfin hI hf, coeff_add, coeff_comp_X_sub_C_rat e₂,
    ← Finset.sum_filter_add_sum_filter_not s (f ∈ ·)]
  refine add_le_add (ih _ h1 hJ₁ e₁ _ fun Q hQ => ?_) (ih _ h2 hJ₂ e₂ _ fun Q hQ => ?_)
  · obtain ⟨hQ, hfQ⟩ := Finset.mem_filter.1 hQ
    replace hQ := hs Q hQ
    exact ⟨⟨hQ.1.1, sup_le hQ.1.2 ((Ideal.span_singleton_le_iff_mem _).2 hfQ)⟩,
      fun R hR hRQ => hQ.2 ⟨hR.1, h1.le.trans hR.2⟩ hRQ⟩
  · obtain ⟨hQ, hfQ⟩ := Finset.mem_filter.1 hQ
    replace hQ := hs Q hQ
    exact ⟨⟨hQ.1.1, fun g hg => (hQ.1.1.mem_or_mem
        (hQ.1.2 (Submodule.mem_colon_singleton.1 hg))).resolve_right hfQ⟩,
      fun R hR hRQ => hQ.2 ⟨hR.1, h2.le.trans hR.2⟩ hRQ⟩

theorem exists_ringKrullDim_quotient_eq_succ {P : Ideal T} [hP : P.IsPrime]
    (hI : P.IsHomogeneous 𝒜) {i : ι} (h : x i ∉ P) :
    ∃ e : ℕ, ringKrullDim (T ⧸ P) = (e + 1 : ℕ) := by
  obtain ⟨δ, hδ⟩ := exists_ringKrullDim_quotient_eq_nat hfin hP.ne_top
  have h1 := (zero_le_degree_iff.2 (hilbertPoly_ne_zero hx hfin hI h)).trans_lt
    (degree_hilbertPoly_lt hx hfin hI hδ.le)
  have h2 : 0 < δ := by exact_mod_cast h1
  exact ⟨δ - 1, by rw [hδ, Nat.sub_add_cancel h2]⟩

theorem ringKrullDim_quotient_eq_natDegree_add_one {P : Ideal T} [P.IsPrime]
    (hI : P.IsHomogeneous 𝒜) (h : ∃ i, x i ∉ P) :
    ringKrullDim (T ⧸ P) = ((gradedQuotHilbertPoly 𝒜 P).natDegree + 1 : ℕ) := by
  obtain ⟨i, hi⟩ := h
  obtain ⟨e, he⟩ := exists_ringKrullDim_quotient_eq_succ hx hfin hI hi
  rw [natDegree_eq_of_degree_eq_some (degree_hilbertPoly_eq_of_isPrime hx hfin hI he), he]

theorem exists_nat_gradedQuotDeg_eq {I : Ideal T} (hI : I.IsHomogeneous 𝒜) {r : ℕ}
    (hr : (gradedQuotHilbertPoly 𝒜 I).degree ≤ r) : ∃ D : ℕ, gradedQuotDeg 𝒜 r I = D := by
  obtain ⟨z, hz⟩ := exists_int_factorial_mul_coeff hr (by
    filter_upwards [eventually_finrank hx hfin hI] with n hn
    exact ⟨finrank K (gradedQuotPiece 𝒜 I n), by rw [← hn]; simp⟩)
  have h0 : 0 ≤ (r.factorial : ℚ) * (gradedQuotHilbertPoly 𝒜 I).coeff r :=
    mul_nonneg (by positivity)
      (coeff_nonneg_of_eventually_eval_nat hr (eventually_nonneg hx hfin hI))
  rw [hz] at h0
  lift z to ℕ using (by exact_mod_cast h0)
  exact ⟨z, by simpa [gradedQuotDeg] using hz⟩

theorem exists_pos_nat_gradedQuotDeg_eq {P : Ideal T} [P.IsPrime] (hI : P.IsHomogeneous 𝒜)
    {r : ℕ} (hr : ringKrullDim (T ⧸ P) = (r + 1 : ℕ)) :
    ∃ D : ℕ, 1 ≤ D ∧ gradedQuotDeg 𝒜 r P = D := by
  have hd := degree_hilbertPoly_eq_of_isPrime hx hfin hI hr
  obtain ⟨D, hD⟩ := exists_nat_gradedQuotDeg_eq hx hfin hI hd.le
  refine ⟨D, Nat.one_le_iff_ne_zero.2 ?_, hD⟩
  rintro rfl
  rw [gradedQuotDeg, Nat.cast_zero, mul_eq_zero] at hD
  exact hD.elim (by positivity) (coeff_ne_zero_of_eq_degree hd)

theorem one_le_gradedQuotDeg {P : Ideal T} [P.IsPrime] (hI : P.IsHomogeneous 𝒜)
    {r : ℕ} (hr : ringKrullDim (T ⧸ P) = (r + 1 : ℕ)) : 1 ≤ gradedQuotDeg 𝒜 r P := by
  obtain ⟨D, h1, hD⟩ := exists_pos_nat_gradedQuotDeg_eq hx hfin hI hr
  rw [hD]
  exact_mod_cast h1

omit hx [GradedAlgebra 𝒜] in

theorem ringKrullDim_quotient_of_mem_minimalPrimes_sup {P Q : Ideal T} [P.IsPrime] {r : ℕ}
    (hr : ringKrullDim (T ⧸ P) = (r + 1 : ℕ)) {f : T} (hfP : f ∉ P)
    (hQ : Q ∈ (P ⊔ Ideal.span {f}).minimalPrimes) : ringKrullDim (T ⧸ Q) = r := by
  haveI := finiteType hfin
  obtain ⟨δ, hδ⟩ := exists_ringKrullDim_quotient_eq_nat hfin hQ.1.1.ne_top
  have h1 := ringKrullDim_quotient_add_one_of_mem_minimalPrimes_sup K hfP hQ
  rw [hr, hδ] at h1
  have : δ + 1 = r + 1 := by exact_mod_cast h1
  rw [hδ, show δ = r by omega]

theorem sum_gradedQuotDeg_le {P : Ideal T} [P.IsPrime] (hI : P.IsHomogeneous 𝒜) {e : ℕ}
    (he : ringKrullDim (T ⧸ P) = (e + 2 : ℕ)) {f : T} {a : ℕ} (hf : f ∈ 𝒜 a) (hfP : f ∉ P)
    (s : Finset (Ideal T)) (hs : ∀ Q ∈ s, Q ∈ (P ⊔ Ideal.span {f}).minimalPrimes) :
    ∑ Q ∈ s, gradedQuotDeg 𝒜 e Q ≤ a * gradedQuotDeg 𝒜 (e + 1) P := by
  have hd := degree_hilbertPoly_eq_of_isPrime hx hfin hI (e := e + 1) he
  obtain ⟨h1, h2⟩ := coeff_sub_comp_X_sub_C (gradedQuotHilbertPoly 𝒜 P) (a : ℚ) e hd.le
  rw [← hilbertPoly_sup_of_isPrime hx hfin hI hf hfP] at h1 h2
  have h3 := sum_coeff_hilbertPoly_le hx hfin (isHomogeneous_sup_span hI hf) (e := e)
    ((degree_le_iff_coeff_zero _ _).2 fun m hm =>
      (degree_lt_iff_coeff_zero _ _).1 h1 m (by exact_mod_cast hm)) s hs
  simp only [gradedQuotDeg, ← Finset.mul_sum]
  refine (mul_le_mul_of_nonneg_left h3 (by positivity)).trans_eq ?_
  rw [h2, Nat.factorial_succ]
  push_cast
  ring

theorem gradedQuotDeg_bot_le {r : ℕ} {c : ℚ}
    (h : ∀ᶠ n : ℕ in atTop, (finrank K (𝒜 n) : ℚ) ≤ (c * n) ^ r) :
    gradedQuotDeg 𝒜 r ⊥ ≤ r.factorial * c ^ r := by
  have hb := Ideal.IsHomogeneous.bot 𝒜
  have h1 : ∀ᶠ n : ℕ in atTop, (gradedQuotHilbertPoly 𝒜 ⊥).eval (n : ℚ) ≤
      (monomial r (c ^ r) : ℚ[X]).eval (n : ℚ) := by
    filter_upwards [h, eventually_finrank hx hfin hb] with n hn hn'
    have := finrank_piece_add hx hfin ⊥ n
    rw [← hn', eval_monomial, ← mul_pow]
    exact le_trans (by exact_mod_cast (by omega)) hn
  have h2 := (degree_le_of_eventually_eval_nat (eventually_nonneg hx hfin hb) h1).trans
    (degree_monomial_le r _)
  have h3 := coeff_nonneg_of_eventually_eval_nat
    ((degree_sub_le _ _).trans (max_le (degree_monomial_le r (c ^ r)) h2)) (by
      filter_upwards [h1] with n hn
      rwa [eval_sub, sub_nonneg])
  rw [coeff_sub, coeff_monomial_same, sub_nonneg] at h3
  exact mul_le_mul_of_nonneg_left h3 (by positivity)

end GradedBezout

open GradedBezout in

theorem graded_bezout_step [GradedAlgebra 𝒜] {ι : Type*} [Finite ι] (x : ι → T)
    (hx : ∀ i, x i ∈ 𝒜 1) (hfin : Module.Finite (Algebra.adjoin K (Set.range x)) T) :
    (∀ J : Ideal T, J.IsHomogeneous 𝒜 →
      IsHilbertPoly (gradedQuotPiece 𝒜 J) (gradedQuotHilbertPoly 𝒜 J)) ∧
    ∀ (P : Ideal T) (r : ℕ), P.IsPrime → P.IsHomogeneous 𝒜 → (∃ i, x i ∉ P) →
      (gradedQuotHilbertPoly 𝒜 P).natDegree = r →
      (ringKrullDim (T ⧸ P) = (r + 1 : ℕ) ∧ ∃ D : ℕ, 1 ≤ D ∧ gradedQuotDeg 𝒜 r P = D) ∧
      ∀ (a : ℕ) (f : T), f ∈ 𝒜 a → f ∉ P →
        (P ⊔ Ideal.span {f}).minimalPrimes.Finite ∧
        (∀ Q ∈ (P ⊔ Ideal.span {f}).minimalPrimes,
          Q.IsHomogeneous 𝒜 ∧ ringKrullDim (T ⧸ Q) = r) ∧
        (1 ≤ r →
          (∀ Q ∈ relevantMinimalPrimes x (P ⊔ Ideal.span {f}),
            (gradedQuotHilbertPoly 𝒜 Q).natDegree = r - 1) ∧
          ∑ᶠ Q ∈ relevantMinimalPrimes x (P ⊔ Ideal.span {f}), gradedQuotDeg 𝒜 (r - 1) Q ≤
            a * gradedQuotDeg 𝒜 r P) := by
  refine ⟨fun J hJ => isHilbertPoly hx hfin hJ, fun P r hp hP hi hr => ?_⟩
  have hdim := ringKrullDim_quotient_eq_natDegree_add_one hx hfin hP hi
  rw [hr] at hdim
  refine ⟨⟨hdim, exists_pos_nat_gradedQuotDeg_eq hx hfin hP hdim⟩, fun a f hf hfP => ?_⟩
  haveI := isNoetherianRing hfin
  have hfinite := (P ⊔ Ideal.span {f}).finite_minimalPrimes_of_isNoetherianRing
  have hQ : ∀ Q ∈ (P ⊔ Ideal.span {f}).minimalPrimes,
      Q.IsHomogeneous 𝒜 ∧ ringKrullDim (T ⧸ Q) = r := fun Q hQ =>
    ⟨isHomogeneous_of_mem_minimalPrimes _ (isHomogeneous_sup_span hP hf) hQ,
      ringKrullDim_quotient_of_mem_minimalPrimes_sup hfin hdim hfP hQ⟩
  refine ⟨hfinite, hQ, fun h1 => ?_⟩
  obtain ⟨e, rfl⟩ : ∃ e, r = e + 1 := ⟨r - 1, by omega⟩
  rw [Nat.add_sub_cancel]
  refine ⟨fun Q h => ?_, ?_⟩
  · haveI := h.1.1.1
    exact natDegree_eq_of_degree_eq_some
      (degree_hilbertPoly_eq_of_isPrime hx hfin (hQ Q h.1).1 (hQ Q h.1).2)
  · have h2 : (relevantMinimalPrimes x (P ⊔ Ideal.span {f})).Finite :=
      hfinite.subset fun _ h => h.1
    rw [finsum_mem_eq_finite_toFinset_sum _ h2]
    exact sum_gradedQuotDeg_le hx hfin hP hdim hf hfP _ fun Q h => (h2.mem_toFinset.1 h).1

section PolynomialRing

attribute [local instance] MvPolynomial.gradedAlgebra

open MvPolynomial

theorem finite_adjoin_range_X (ι : Type*) :
    Module.Finite (Algebra.adjoin K (Set.range (MvPolynomial.X : ι → MvPolynomial ι K)))
      (MvPolynomial ι K) :=
  Module.Finite.of_surjective (Algebra.linearMap _ _) fun p =>
    ⟨⟨p, by rw [adjoin_range_X]; trivial⟩, rfl⟩

theorem gradedQuotHilbertPoly_mvPolynomial {ι : Type*} [Finite ι] {I : Ideal (MvPolynomial ι K)}
    (hI : I.IsHomogeneous (homogeneousSubmodule ι K)) :
    gradedQuotHilbertPoly (homogeneousSubmodule ι K) I = idealHilbertPoly I := by
  apply polynomial_eq_of_eventually_eval_nat
  filter_upwards [eventually_finrank_quotPiece hI, GradedBezout.eventually_finrank
    (fun i => isHomogeneous_X K i) (finite_adjoin_range_X ι) hI] with n h1 h2
  rw [← h1, ← h2, quotPiece_natCast, gradedQuotPiece_natCast]

example : (⊥ : Ideal (MvPolynomial (Fin 2) K)).IsPrime ∧
    (⊥ : Ideal (MvPolynomial (Fin 2) K)).IsHomogeneous (homogeneousSubmodule (Fin 2) K) ∧
    (MvPolynomial.X 0 : MvPolynomial (Fin 2) K) ∉ (⊥ : Ideal (MvPolynomial (Fin 2) K)) ∧
    (gradedQuotHilbertPoly (homogeneousSubmodule (Fin 2) K) ⊥).natDegree = 1 := by
  refine ⟨inferInstance, Ideal.IsHomogeneous.bot _, MvPolynomial.X_ne_zero 0, ?_⟩
  refine natDegree_eq_of_degree_eq_some (GradedBezout.degree_hilbertPoly_eq_of_isPrime
    (fun i => isHomogeneous_X K i) (finite_adjoin_range_X _) (Ideal.IsHomogeneous.bot _) ?_)
  rw [ringKrullDim_eq_of_ringEquiv (RingEquiv.quotientBot _),
    MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field]
  simp

end PolynomialRing

end GlobalTheory
