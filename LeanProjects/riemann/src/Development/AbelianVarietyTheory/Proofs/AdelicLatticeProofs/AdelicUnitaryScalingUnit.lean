import Mathlib
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.IsHermForm
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.NormOneInfinite

open NumberField IsDedekindDomain GlobalTheory.AdLat GlobalTheory.UnRep
open scoped TensorProduct Matrix

namespace GlobalTheory.UnRep

theorem finite_det_one_add_smul_eq_zero {E K : Type} [Field E] [Field K] (φ : E →+* K) {n : ℕ}
    (G : Matrix (Fin n) (Fin n) K) : {l : E | (1 + φ l • G).det = 0}.Finite := by
  let p : Polynomial K := (1 + (Polynomial.X : Polynomial K) • G.map Polynomial.C).det
  have hp : ∀ x : K, p.eval x = (1 + x • G).det := by
    intro x
    have := (Polynomial.evalRingHom x).map_det (1 + (Polynomial.X : Polynomial K) • G.map Polynomial.C)
    rw [Polynomial.coe_evalRingHom] at this
    rw [this]
    congr 1
    ext i j
    by_cases h : i = j <;> simp [h, Matrix.one_apply] <;> ring
  have hp0 : p ≠ 0 := by
    intro h
    have := hp 0
    rw [h] at this
    simp at this
  have hfin : (p.rootSet K).Finite := p.rootSet_finite K
  refine (hfin.preimage φ.injective.injOn).subset fun l hl => ?_
  simp only [Set.mem_preimage, Polynomial.mem_rootSet]
  refine ⟨hp0, ?_⟩
  rw [Polynomial.coe_aeval_eq_eval, hp]
  exact hl

theorem finite_not_isUnit_det {E R : Type} [Field E] [CommRing R] (φ : E →+* R) {n : ℕ}
    (g : Matrix (Fin n) (Fin n) R) (ε : R) (hε : ε * ε = ε)
    (hfin : {M : Ideal R | M.IsMaximal ∧ 1 - ε ∈ M}.Finite) :
    {l : E | ¬ IsUnit (1 + φ l • (ε • g + (1 - ε) • (1 : Matrix (Fin n) (Fin n) R))).det}.Finite := by
  set G := ε • g + (1 - ε) • (1 : Matrix (Fin n) (Fin n) R) with hG
  have key : ∀ (M : Ideal R) (l : E), Ideal.Quotient.mk M (1 + φ l • G).det =
      (1 + ((Ideal.Quotient.mk M).comp φ) l • G.map (Ideal.Quotient.mk M)).det := by
    intro M l
    rw [RingHom.map_det]
    congr 1
    ext i j
    by_cases h : i = j <;> simp [h, Matrix.one_apply]
  have h1 : ∀ M ∈ {M : Ideal R | M.IsMaximal ∧ 1 - ε ∈ M}, {l : E | (1 + φ l • G).det ∈ M}.Finite := by
    rintro M ⟨hM, -⟩
    letI := Ideal.Quotient.field M
    refine (finite_det_one_add_smul_eq_zero ((Ideal.Quotient.mk M).comp φ)
      (G.map (Ideal.Quotient.mk M))).subset fun l hl => ?_
    rw [Set.mem_setOf_eq, ← key, Ideal.Quotient.eq_zero_iff_mem]
    exact hl
  refine ((hfin.biUnion h1).union (Set.finite_singleton (-1))).subset fun l hl => ?_
  obtain ⟨M, hM, hl⟩ := exists_max_ideal_of_mem_nonunits (mem_nonunits_iff.2 hl)
  have h0 : ε * (1 - ε) ∈ M := by
    rw [mul_sub, mul_one, hε, sub_self]; exact M.zero_mem
  rcases hM.isPrime.mem_or_mem h0 with h | h
  · right
    letI := Ideal.Quotient.field M
    have h2 := Ideal.Quotient.eq_zero_iff_mem.2 hl
    have h3 := Ideal.Quotient.eq_zero_iff_mem.2 h
    have h4 : G.map (Ideal.Quotient.mk M) = 1 := by
      ext i j
      by_cases hij : i = j <;> simp [hG, hij, Matrix.one_apply, h3]
    rw [key, h4] at h2
    have h5 : (1 + ((Ideal.Quotient.mk M).comp φ) l • (1 : Matrix (Fin n) (Fin n) (R ⧸ M))) =
        ((Ideal.Quotient.mk M).comp φ) (1 + l) • 1 := by
      rw [map_add, map_one, add_smul, one_smul]
    rw [h5, Matrix.det_smul, Matrix.det_one, mul_one] at h2
    have h6 := (map_eq_zero _).1 (pow_eq_zero_iff (by
      intro h; rw [h] at h2; simp at h2) |>.1 h2)
    exact eq_neg_of_add_eq_zero_right h6
  · left
    exact Set.mem_biUnion (s := {M : Ideal R | M.IsMaximal ∧ 1 - ε ∈ M}) ⟨hM, h⟩ hl

noncomputable def adEval (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
    FiniteAdeleRing (𝓞 F) F →+* v.adicCompletion F :=
  RestrictedProduct.evalRingHom (fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletion F) v

theorem adEval_surjective (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
    Function.Surjective (adEval F v) := by
  classical
  intro x
  refine ⟨⟨Pi.single v x, ?_⟩, ?_⟩
  · filter_upwards [(Set.finite_singleton v).compl_mem_cofinite] with w hw
    rw [Pi.single_eq_of_ne hw]
    exact zero_mem _
  · exact Pi.single_eq_same v x

theorem finite_primes_one_sub (F : Type) [Field F] [NumberField F] (e : FiniteAdeleRing (𝓞 F) F)
    (he : {v | e v ≠ 0}.Finite) :
    {P : Ideal (FiniteAdeleRing (𝓞 F) F) | P.IsPrime ∧ 1 - e ∈ P}.Finite := by
  refine (he.image fun v => RingHom.ker (adEval F v)).subset ?_
  rintro P ⟨hP, h⟩
  have hle : he.toFinset.inf (fun v => RingHom.ker (adEval F v)) ≤ P := by
    intro a ha
    have h0 : a * e = 0 := by
      refine FiniteAdeleRing.ext F fun v => ?_
      change a v * e v = 0
      by_cases hv : e v = 0
      · rw [hv, mul_zero]
      · have h1 : a ∈ RingHom.ker (adEval F v) :=
          (Finset.inf_le (f := fun v => RingHom.ker (adEval F v)) (he.mem_toFinset.2 hv)) ha
        have h2 : a v = 0 := h1
        rw [h2, zero_mul]
    have : a = a * (1 - e) := by rw [mul_sub, h0, mul_one, sub_zero]
    rw [this]
    exact P.mul_mem_left _ h
  obtain ⟨v, hv, hvP⟩ := (Ideal.IsPrime.inf_le' hP).1 hle
  exact ⟨v, he.mem_toFinset.1 hv,
    (RingHom.ker_isMaximal_of_surjective _ (adEval_surjective F v)).eq_of_le hP.ne_top hvP⟩

theorem infinite_norm_one {F E : Type} [Field F] [Field E] [CharZero E] [Algebra F E] (c : E ≃ₐ[F] E)
    (hc : ∀ x, c (c x) = x) (hc1 : c ≠ 1) : {l : E | l * c l = 1}.Infinite := by
  first
  | exact @_root_.GlobalTheory.NormOneInfinite.normOne_infinite
  | exact _root_.GlobalTheory.NormOneInfinite.normOne_infinite
  | (apply _root_.GlobalTheory.NormOneInfinite.normOne_infinite <;> assumption)
  | (intros; apply _root_.GlobalTheory.NormOneInfinite.normOne_infinite <;> assumption)
  | (intros; apply @_root_.GlobalTheory.NormOneInfinite.normOne_infinite <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.NormOneInfinite.normOne_infinite ..)

theorem exists_norm_one_isUnit_det : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (c : E ≃ₐ[F] E), Module.finrank F E = 2 → (∀ x, c (c x) = x) → c ≠ 1 → ∀ (n : ℕ) (g : Matrix (Fin n) (Fin n) (RA F E)) (e : FiniteAdeleRing (𝓞 F) F), e * e = e → {v | e v ≠ 0}.Finite → ∃ lam : E, lam * c lam = 1 ∧ IsUnit (1 + ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] lam) • ((e ⊗ₜ[F] (1 : E)) • g + ((1 - e) ⊗ₜ[F] (1 : E)) • (1 : Matrix (Fin n) (Fin n) (RA F E)))).det := by
  intro F E _ _ _ _ _ c hrk hc hc1 n g e he hfin
  haveI : Module.Finite F E := Module.finite_of_finrank_pos (by omega)
  have hsub : ((1 - e) ⊗ₜ[F] (1 : E) : RA F E) = 1 - e ⊗ₜ[F] (1 : E) := by
    rw [TensorProduct.sub_tmul, Algebra.TensorProduct.one_def]
  have hM : {M : Ideal (RA F E) | M.IsMaximal ∧ 1 - e ⊗ₜ[F] (1 : E) ∈ M}.Finite := by
    refine ((finite_primes_one_sub F e hfin).biUnion fun P _ =>
      Algebra.QuasiFinite.finite_primesOver (S := RA F E) P).subset ?_
    rintro M ⟨hM, h⟩
    haveI := hM.isPrime
    refine Set.mem_biUnion (x := M.under (FiniteAdeleRing (𝓞 F) F)) ⟨inferInstance, ?_⟩
      ⟨inferInstance, inferInstance⟩
    rw [← hsub] at h
    exact h
  have hbad := finite_not_isUnit_det
    (Algebra.TensorProduct.includeRight : E →ₐ[F] RA F E).toRingHom g (e ⊗ₜ[F] (1 : E))
    (by rw [Algebra.TensorProduct.tmul_mul_tmul, he, mul_one]) hM
  obtain ⟨l, hl, hl'⟩ := (infinite_norm_one c hc hc1).exists_notMem_finite hbad
  refine ⟨l, hl, ?_⟩
  rw [hsub]
  exact not_not.1 hl'

end GlobalTheory.UnRep
