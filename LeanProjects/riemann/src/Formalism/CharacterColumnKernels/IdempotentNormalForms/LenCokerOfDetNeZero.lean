import Formalism.CharacterColumnKernels.StatementX
import Formalism.CharacterColumnKernels.IdempotentNormalForms.SingleEqSmul
import Formalism.CharacterColumnKernels.IdempotentNormalForms.LengthKerOfDetEqZero

open Finset Module IsDiscreteValuationRing Matrix

noncomputable section

namespace Formalism.NG

section HomQuotAux

variable {R O M NN : Type*} [Ring R] [CommRing O] [AddCommGroup M] [Module R M] [Module O M]
  [SMulCommClass R O M] [AddCommGroup NN] [Module R NN] {g : Type} [Fintype g]

def evalGens (n : g → NN) : (NN →ₗ[R] M) →ₗ[O] (g → M) where
  toFun φ j := φ (n j)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem evalGens_mem (Θ : Matrix g g R) (n : g → NN) (hrel : ∀ i, ∑ j, Θ i j • n j = 0)
    (φ : NN →ₗ[R] M) : (fun j => φ (n j)) ∈ LinearMap.ker (relMap O M Θ) := by
  classical
  rw [LinearMap.mem_ker]
  funext i
  rw [relMap_apply', Pi.zero_apply]
  simp_rw [← LinearMap.map_smul]
  rw [← map_sum, hrel i, map_zero]

theorem evalGens_inj (n : g → NN) (hspan : Submodule.span R (Set.range n) = ⊤) :
    Function.Injective (fun (φ : NN →ₗ[R] M) (j : g) => φ (n j)) := by
  intro φ ψ h
  exact LinearMap.ext_on_range hspan fun j => congrFun h j

end HomQuotAux

theorem homQuot : StatHomQuot := by
  intro R O M NN _ _ _ _ _ _ _ _ g _ _ Θ n hspan hrel
  refine ⟨evalGens_mem Θ n hrel, evalGens_inj n hspan, ?_⟩
  exact Module.length_le_of_injective
    (LinearMap.codRestrict (LinearMap.ker (relMap O M Θ)) (evalGens (O := O) (M := M) n)
      (evalGens_mem Θ n hrel))
    fun φ ψ h => evalGens_inj n hspan (congrArg Subtype.val h)

section KerHomAux

variable {R : Type*} [Ring R] {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  {g d : Type} [Fintype g] [DecidableEq g] [Fintype d] [DecidableEq d]
  (ρ : R →+* Matrix d d O)

def uncurryEquiv : (g → LatQ O d ρ) ≃ₗ[O] (g × d → KO O) where
  toFun v p := v p.1 p.2
  invFun w j b := w (j, b)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

variable [SMulCommClass R O (LatQ O d ρ)]

theorem uncurry_relMap (Θ : Matrix g g R) (v : g → LatQ O d ρ) :
    uncurryEquiv ρ (relMap O (LatQ O d ρ) Θ v) = matQ O (bigMat ρ Θ) (uncurryEquiv ρ v) := by
  funext p
  obtain ⟨i, a⟩ := p
  show (∑ j, Θ i j • v j : LatQ O d ρ) a = ∑ q : g × d, ρ (Θ i q.1) a q.2 • v q.1 q.2
  rw [Fintype.sum_prod_type]
  have hsum : (∑ j, Θ i j • v j : LatQ O d ρ) a = ∑ j, ((Θ i j • v j : LatQ O d ρ) : d → KO O) a :=
    Finset.sum_apply (M := fun _ : d => KO O) a univ (fun j => (Θ i j • v j : LatQ O d ρ))
  rw [hsum]
  rfl

theorem ker_map_uncurry (Θ : Matrix g g R) :
    (LinearMap.ker (relMap O (LatQ O d ρ) Θ)).map (uncurryEquiv (g := g) ρ).toLinearMap =
      LinearMap.ker (matQ O (bigMat ρ Θ)) := by
  ext w
  rw [Submodule.mem_map_equiv, LinearMap.mem_ker, LinearMap.mem_ker,
    ← (uncurryEquiv (g := g) ρ).map_eq_zero_iff, uncurry_relMap, LinearEquiv.apply_symm_apply]

end KerHomAux

theorem kerHomBlock : StatKerHomBlock := by
  intro R O _ _ _ _ g d _ _ _ _ ρ _ Θ
  obtain ⟨e⟩ := homCoker R O (LatQ O d ρ) g g Θ
  rw [e.length_eq, ← ker_map_uncurry ρ Θ]
  exact (Submodule.equivMapOfInjective _ (uncurryEquiv (g := g) ρ).injective _).length_eq.symm

section LenCokerAux

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  {ι : Type} [Fintype ι] [DecidableEq ι]

theorem lenCoker_of_det_ne_zero (A : Matrix ι ι O) (hd : A.det ≠ 0) :
    Module.length O ((ι → O) ⧸ LinearMap.range (Matrix.mulVecLin A)) = addVal O A.det := by
  have hinj : Function.Injective (Matrix.mulVecLin A) :=
    Matrix.mulVec_injective_of_det_mem_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero hd)
  let N := LinearMap.range (Matrix.mulVecLin A)
  let e : (ι → O) ≃ₗ[O] N := LinearEquiv.ofInjective _ hinj
  have h1 := IdempotentNormalFormsLenFacts.length_quot_eq_addVal_det N e
  have h2 : N.subtype ∘ₗ (e : (ι → O) →ₗ[O] N) = Matrix.mulVecLin A := LinearMap.ext fun x => rfl
  have h3 : LinearMap.det (Matrix.mulVecLin A) = A.det := by
    rw [← Matrix.toLin'_apply', LinearMap.det_toLin']
  rw [h1, h2, h3]

def dotLin (u : ι → O) : (ι → O) →ₗ[O] O where
  toFun x := u ⬝ᵥ x
  map_add' x y := dotProduct_add u x y
  map_smul' c x := by simp [dotProduct_smul]

theorem lenCoker_of_det_eq_zero (A : Matrix ι ι O) (hd : A.det = 0) :
    Module.length O ((ι → O) ⧸ LinearMap.range (Matrix.mulVecLin A)) = ⊤ := by
  obtain ⟨w, hw0, hw⟩ := Matrix.exists_vecMul_eq_zero_iff.mpr hd
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
  have hw'A : w' ᵥ* A = 0 := by
    have : w = w i0 • w' := funext fun i => by simp [hw' i]
    rw [this, Matrix.smul_vecMul] at hw
    exact (smul_eq_zero.mp hw).resolve_left hwi0
  obtain ⟨ϖ, hϖ⟩ := exists_irreducible O
  rw [ENat.eq_top_iff_forall_ge]
  intro k
  let I : Ideal O := Ideal.span ({ϖ ^ k} : Set O)
  let f : (ι → O) →ₗ[O] (O ⧸ I) := I.mkQ ∘ₗ dotLin w'
  have hle : LinearMap.range (Matrix.mulVecLin A) ≤ LinearMap.ker f := by
    rintro _ ⟨z, rfl⟩
    rw [LinearMap.mem_ker]
    show I.mkQ (w' ⬝ᵥ (A *ᵥ z)) = 0
    rw [Matrix.dotProduct_mulVec, hw'A, zero_dotProduct, map_zero]
  let F := (LinearMap.range (Matrix.mulVecLin A)).liftQ f hle
  have hF : Function.Surjective F := by
    intro y
    obtain ⟨c, rfl⟩ := I.mkQ_surjective y
    refine ⟨Submodule.Quotient.mk (Pi.single i0 c), ?_⟩
    show I.mkQ (w' ⬝ᵥ Pi.single i0 c) = I.mkQ c
    rw [dotProduct_single, hw'i0, one_mul]
  have h := Module.length_le_of_surjective F hF
  rw [IdempotentNormalFormsLenFacts.length_quot_span, hϖ.addVal_pow] at h
  simpa using h

end LenCokerAux

theorem lenCoker : StatLenCoker := by
  intro O _ _ _ ι _ _ A
  by_cases hd : A.det = 0
  · rw [lenCoker_of_det_eq_zero A hd, hd, addVal_zero]
  · exact lenCoker_of_det_ne_zero A hd

end Formalism.NG
