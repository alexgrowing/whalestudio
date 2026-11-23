import Formalism.CharacterColumnKernels.Statement
import Lemmata.SecondBlockLemmaA.Imports
import Lemmata.AddValuationProducts.AddValProd

open Module IsDiscreteValuationRing Matrix

noncomputable section

namespace Formalism.NG

namespace IdempotentNormalFormsLenFacts

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

lemma length_quot_span (a : O) :
    Module.length O (O ⧸ Ideal.span ({a} : Set O)) = addVal O a :=
  Ring.ord_eq_addVal a

lemma addVal_prod {ι : Type*} (s : Finset ι) (a : ι → O) :
    addVal O (∏ i ∈ s, a i) = ∑ i ∈ s, addVal O (a i) := by
  first | exact Bl.SecondBlockLemmaA.goal1 .. | (apply Bl.SecondBlockLemmaA.goal1 <;> assumption) | (intros; apply Bl.SecondBlockLemmaA.goal1 <;> assumption) | (apply @Bl.SecondBlockLemmaA.goal1 <;> assumption) | (intros; apply @Bl.SecondBlockLemmaA.goal1 <;> assumption) | (apply @Bl.SecondBlockLemmaA.goal1 <;> first | assumption | infer_instance) | exact @Bl.SecondBlockLemmaA.goal1 O ‹_› ‹_› ‹_› ι s a | exact @Bl.SecondBlockLemmaA.goal1 O ‹_› ‹_› ‹_› ι s | exact @Bl.SecondBlockLemmaA.goal1 O ‹_› ‹_› ‹_› ι | exact @Bl.SecondBlockLemmaA.goal1 O ‹_› ‹_› ‹_› | exact @Bl.SecondBlockLemmaA.goal1 O ‹_› ‹_› | exact @Bl.SecondBlockLemmaA.goal1 O ‹_› | exact @Bl.SecondBlockLemmaA.goal1 O

lemma length_quot_eq_addVal_det {ι : Type} [Fintype ι] [DecidableEq ι]
    (N : Submodule O (ι → O)) (e : (ι → O) ≃ₗ[O] N) :
    Module.length O ((ι → O) ⧸ N) =
      addVal O (LinearMap.det (N.subtype ∘ₗ (e : (ι → O) →ₗ[O] N))) := by
  first | exact Bl.AddValuationProducts.goal1 .. | (apply Bl.AddValuationProducts.goal1 <;> assumption) | (intros; apply Bl.AddValuationProducts.goal1 <;> assumption) | (apply @Bl.AddValuationProducts.goal1 <;> assumption) | (intros; apply @Bl.AddValuationProducts.goal1 <;> assumption) | (apply @Bl.AddValuationProducts.goal1 <;> first | assumption | infer_instance) | exact @Bl.AddValuationProducts.goal1 O ‹_› ‹_› ‹_› ι ‹_› ‹_› N e | exact @Bl.AddValuationProducts.goal1 O ‹_› ‹_› ‹_› ι ‹_› ‹_› N | exact @Bl.AddValuationProducts.goal1 O ‹_› ‹_› ‹_› ι ‹_› ‹_› | exact @Bl.AddValuationProducts.goal1 O ‹_› ‹_› ‹_› ι ‹_› | exact @Bl.AddValuationProducts.goal1 O ‹_› ‹_› ‹_› ι | exact @Bl.AddValuationProducts.goal1 O ‹_› ‹_› ‹_› | exact @Bl.AddValuationProducts.goal1 O ‹_› ‹_› | exact @Bl.AddValuationProducts.goal1 O ‹_› | exact @Bl.AddValuationProducts.goal1 O

lemma mk_eq_zero_iff (y : FractionRing O) :
    (Submodule.Quotient.mk y : KO O) = 0 ↔ ∃ x : O, algebraMap O (FractionRing O) x = y := by
  rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_one]

lemma matQ_mk {ι : Type*} [Fintype ι] (A : Matrix ι ι O) (y : ι → FractionRing O) :
    matQ O A (fun i => (Submodule.Quotient.mk (y i) : KO O)) =
      fun i => (Submodule.Quotient.mk ((A.map (algebraMap O (FractionRing O)) *ᵥ y) i) : KO O) := by
  ext i
  show ∑ j, A i j • (Submodule.mkQ (1 : Submodule O (FractionRing O)) (y j)) =
    Submodule.mkQ (1 : Submodule O (FractionRing O))
      ((A.map (algebraMap O (FractionRing O)) *ᵥ y) i)
  rw [Matrix.mulVec, dotProduct, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← map_smul, Matrix.map_apply, Algebra.smul_def]

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

abbrev AK (A : Matrix ι ι O) : Matrix ι ι (FractionRing O) := A.map (algebraMap O (FractionRing O))

lemma isUnit_det_AK (A : Matrix ι ι O) (hd : A.det ≠ 0) : IsUnit (AK A).det := by
  rw [isUnit_iff_ne_zero, AK, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
  exact fun h => hd (IsFractionRing.injective O (FractionRing O) (by rw [h, map_zero]))

def phi (A : Matrix ι ι O) : (ι → O) →ₗ[O] (ι → KO O) where
  toFun x i := Submodule.Quotient.mk (((AK A)⁻¹ *ᵥ (fun j => algebraMap O (FractionRing O) (x j))) i)
  map_add' x y := by
    ext i
    have : (fun j => algebraMap O (FractionRing O) (x j + y j)) =
        (fun j => algebraMap O (FractionRing O) (x j)) +
          (fun j => algebraMap O (FractionRing O) (y j)) := by
      ext j; simp
    simp only [Pi.add_apply]
    rw [this, Matrix.mulVec_add, Pi.add_apply, Submodule.Quotient.mk_add]
  map_smul' r x := by
    ext i
    have : (fun j => algebraMap O (FractionRing O) (r • x j)) =
        algebraMap O (FractionRing O) r • (fun j => algebraMap O (FractionRing O) (x j)) := by
      ext j; simp
    simp only [Pi.smul_apply, RingHom.id_apply]
    rw [this, Matrix.mulVec_smul, ← Submodule.Quotient.mk_smul]
    congr 1
    simp [Algebra.smul_def]

lemma phi_apply (A : Matrix ι ι O) (x : ι → O) :
    phi A x = fun i => (Submodule.Quotient.mk
      (((AK A)⁻¹ *ᵥ (fun j => algebraMap O (FractionRing O) (x j))) i) : KO O) := rfl

lemma map_mulVec_fun (A : Matrix ι ι O) (z : ι → O) :
    (fun i => algebraMap O (FractionRing O) ((A *ᵥ z) i)) =
      AK A *ᵥ (fun j => algebraMap O (FractionRing O) (z j)) := by
  ext i
  exact RingHom.map_mulVec _ A z i

lemma range_phi (A : Matrix ι ι O) (hd : A.det ≠ 0) :
    LinearMap.range (phi A) = LinearMap.ker (matQ O A) := by
  have hu := isUnit_det_AK A hd
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    rw [LinearMap.mem_ker, phi_apply, matQ_mk, Matrix.mulVec_mulVec,
      Matrix.mul_nonsing_inv _ hu, Matrix.one_mulVec]
    ext i
    exact (mk_eq_zero_iff _).mpr ⟨x i, rfl⟩
  · intro v hv
    rw [LinearMap.mem_ker] at hv
    choose y hy using fun i => Submodule.Quotient.mk_surjective (1 : Submodule O (FractionRing O)) (v i)
    have hv' : v = fun i => (Submodule.Quotient.mk (y i) : KO O) := funext fun i => (hy i).symm
    rw [hv', matQ_mk] at hv
    choose x hx using fun i => (mk_eq_zero_iff _).mp (congrFun hv i)
    refine ⟨x, ?_⟩
    have hx' : (fun j => algebraMap O (FractionRing O) (x j)) = AK A *ᵥ y := funext hx
    rw [phi_apply, hx', Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hu, Matrix.one_mulVec, hv']

lemma ker_phi (A : Matrix ι ι O) (hd : A.det ≠ 0) :
    LinearMap.ker (phi A) = LinearMap.range (Matrix.mulVecLin A) := by
  have hu := isUnit_det_AK A hd
  ext x
  rw [LinearMap.mem_ker, LinearMap.mem_range, phi_apply]
  constructor
  · intro h
    choose z hz using fun i => (mk_eq_zero_iff _).mp (congrFun h i)
    refine ⟨z, ?_⟩
    have hz' : (fun j => algebraMap O (FractionRing O) (z j)) =
        (AK A)⁻¹ *ᵥ (fun j => algebraMap O (FractionRing O) (x j)) := funext hz
    funext i
    apply IsFractionRing.injective O (FractionRing O)
    rw [Matrix.mulVecLin_apply]
    have := congrFun (map_mulVec_fun A z) i
    rw [this, hz', Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hu, Matrix.one_mulVec]
  · rintro ⟨z, rfl⟩
    rw [Matrix.mulVecLin_apply, map_mulVec_fun, Matrix.mulVec_mulVec,
      Matrix.nonsing_inv_mul _ hu, Matrix.one_mulVec]
    ext i
    exact (mk_eq_zero_iff _).mpr ⟨z i, rfl⟩

lemma length_ker_of_det_ne_zero {ι : Type} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι O)
    (hd : A.det ≠ 0) :
    Module.length O (LinearMap.ker (matQ O A)) = addVal O A.det := by
  have hinj : Function.Injective (Matrix.mulVecLin A) :=
    Matrix.mulVec_injective_of_det_mem_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero hd)
  let N := LinearMap.range (Matrix.mulVecLin A)
  let e : (ι → O) ≃ₗ[O] N := LinearEquiv.ofInjective _ hinj
  have h1 := length_quot_eq_addVal_det N e
  have h2 : N.subtype ∘ₗ (e : (ι → O) →ₗ[O] N) = Matrix.mulVecLin A := LinearMap.ext fun x => rfl
  have h3 : LinearMap.det (Matrix.mulVecLin A) = A.det := by
    rw [← Matrix.toLin'_apply', LinearMap.det_toLin']
  rw [← (LinearEquiv.ofEq _ _ (range_phi A hd)).length_eq,
    ← (LinearMap.quotKerEquivRange (phi A)).length_eq,
    (Submodule.quotEquivOfEq _ _ (ker_phi A hd)).length_eq, h1, h2, h3]

lemma length_ker_of_det_eq_zero (A : Matrix ι ι O) (hd : A.det = 0) :
    Module.length O (LinearMap.ker (matQ O A)) = ⊤ := by
  obtain ⟨w, hw0, hw⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hd
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hw0
  obtain ⟨i0, -, hi0⟩ := Finset.exists_min_image Finset.univ (fun i => addVal O (w i))
    ⟨j, Finset.mem_univ _⟩
  have hwi0 : w i0 ≠ 0 := by
    intro h
    have := hi0 j (Finset.mem_univ _)
    rw [h, addVal_zero, top_le_iff, addVal_eq_top_iff] at this
    exact hj this
  choose w' hw' using fun i => (addVal_le_iff_dvd (a := w i0) (b := w i)).mp
    (hi0 i (Finset.mem_univ _))
  have hw'i0 : w' i0 = 1 := by
    have := hw' i0
    exact (mul_left_cancel₀ hwi0 (this.symm.trans (mul_one _).symm))
  have hAw' : A *ᵥ w' = 0 := by
    have : w = w i0 • w' := funext fun i => by simp [hw' i]
    rw [this, Matrix.mulVec_smul] at hw
    exact (smul_eq_zero.mp hw).resolve_left hwi0
  obtain ⟨ϖ, hϖ⟩ := exists_irreducible O
  have hϖ0 : ϖ ≠ 0 := hϖ.ne_zero
  rw [ENat.eq_top_iff_forall_ge]
  intro k
  let c : FractionRing O := (algebraMap O (FractionRing O) (ϖ ^ k))⁻¹
  have hc : algebraMap O (FractionRing O) (ϖ ^ k) ≠ 0 := by
    rw [Ne, ← map_zero (algebraMap O (FractionRing O))]
    exact fun h => pow_ne_zero k hϖ0 (IsFractionRing.injective O (FractionRing O) h)
  have hc1 : algebraMap O (FractionRing O) (ϖ ^ k) * c = 1 := mul_inv_cancel₀ hc
  let v : ι → KO O := fun i => Submodule.Quotient.mk (c * algebraMap O (FractionRing O) (w' i))
  have hv : v ∈ LinearMap.ker (matQ O A) := by
    rw [LinearMap.mem_ker]
    have : (fun i => c * algebraMap O (FractionRing O) (w' i)) =
        c • (fun i => algebraMap O (FractionRing O) (w' i)) := by
      ext i; simp
    show matQ O A (fun i => (Submodule.Quotient.mk (c * algebraMap O (FractionRing O) (w' i)) : KO O)) = 0
    rw [matQ_mk, this, Matrix.mulVec_smul, ← map_mulVec_fun, hAw']
    ext i
    exact (mk_eq_zero_iff _).mpr ⟨0, by simp⟩
  let χ : O →ₗ[O] (ι → KO O) := LinearMap.toSpanSingleton O _ v
  have hker : LinearMap.ker χ = Ideal.span ({ϖ ^ k} : Set O) := by
    ext x
    rw [LinearMap.mem_ker, LinearMap.toSpanSingleton_apply, Ideal.mem_span_singleton]
    constructor
    · intro h
      have h0 := congrFun h i0
      simp only [v, Pi.smul_apply, Pi.zero_apply, hw'i0, map_one, mul_one,
        ← Submodule.Quotient.mk_smul] at h0
      obtain ⟨z, hz⟩ := (mk_eq_zero_iff _).mp h0
      refine ⟨z, ?_⟩
      apply IsFractionRing.injective O (FractionRing O)
      rw [Algebra.smul_def] at hz
      rw [map_mul, hz, mul_left_comm, hc1, mul_one]
    · rintro ⟨z, rfl⟩
      ext i
      simp only [v, Pi.smul_apply, Pi.zero_apply, ← Submodule.Quotient.mk_smul]
      refine (mk_eq_zero_iff _).mpr ⟨z * w' i, ?_⟩
      rw [Algebra.smul_def, map_mul, map_mul,
        show algebraMap O (FractionRing O) (ϖ ^ k) * algebraMap O (FractionRing O) z *
          (c * algebraMap O (FractionRing O) (w' i)) =
          (algebraMap O (FractionRing O) (ϖ ^ k) * c) *
          (algebraMap O (FractionRing O) z * algebraMap O (FractionRing O) (w' i)) by ring,
        hc1, one_mul]
  have hrange : LinearMap.range χ ≤ LinearMap.ker (matQ O A) := by
    rintro _ ⟨x, rfl⟩
    exact Submodule.smul_mem _ x hv
  have hle := Module.length_le_of_injective (Submodule.inclusion hrange)
    (Submodule.inclusion_injective hrange)
  rw [← (LinearMap.quotKerEquivRange χ).length_eq,
    (Submodule.quotEquivOfEq _ _ hker).length_eq, length_quot_span, hϖ.addVal_pow] at hle
  simpa using hle

end IdempotentNormalFormsLenFacts

open IdempotentNormalFormsLenFacts

theorem lenKer : StatLenKer := by
  intro O _ _ _ ι _ _ A
  by_cases hd : A.det = 0
  · rw [length_ker_of_det_eq_zero A hd, hd, addVal_zero]
  · exact length_ker_of_det_ne_zero A hd

end Formalism.NG
