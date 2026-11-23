import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Graded
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.MapRepApply
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GrNoeth

open IsLocalRing UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement

private theorem pt_of_ft {K C : Type} [Field K] [IsAlgClosed K] [CommRing C] [Algebra K C] [Nontrivial C]
    [Algebra.FiniteType K C] : Nonempty (C →ₐ[K] K) := by
  obtain ⟨m, hm⟩ := Ideal.exists_maximal C
  letI := Ideal.Quotient.field m
  haveI : Module.Finite K (C ⧸ m) := finite_of_finite_type_of_isJacobsonRing K (C ⧸ m)
  exact ⟨(IsAlgClosed.lift : (C ⧸ m) →ₐ[K] K).comp (Ideal.Quotient.mkₐ K m)⟩

private theorem pt_of_lin {A B K : Type} [CommRing A] [CommRing B] [Field K] [IsAlgClosed K] [Algebra A B]
    [Algebra A K] [Algebra.FiniteType A B] (ρ : B →ₗ[A] K) (h : ρ 1 = 1) : Nonempty (B →ₐ[A] K) := by
  haveI : Nontrivial (TensorProduct A K B) := by
    refine ⟨1, 0, fun e => ?_⟩
    have := congrArg (TensorProduct.lift ((LinearMap.mul A K).compl₂ ρ)) e
    rw [Algebra.TensorProduct.one_def, TensorProduct.lift.tmul, map_zero] at this
    simp [h] at this
  obtain ⟨y⟩ := pt_of_ft (K := K) (C := TensorProduct A K B)
  exact ⟨(y.restrictScalars A).comp Algebra.TensorProduct.includeRight⟩

private theorem ext_graded {O A X K : Type} [CommRing O] [CommRing A] [Algebra O A] [AddCommGroup X]
    [DecidableEq X] (𝒜 : X → Submodule O A) [GradedAlgebra 𝒜] [Algebra.FiniteType (𝒜 0) A]
    [Field K] [IsAlgClosed K] [Algebra O K] (y : 𝒜 0 →ₐ[O] K) :
    ∃ ξ : A →ₐ[O] K, ∀ b : 𝒜 0, ξ b = y b := by
  letI : Algebra (𝒜 0) K := (y : 𝒜 0 →+* K).toAlgebra
  have key : ∀ (r : 𝒜 0) (a : A),
      DirectSum.decompose 𝒜 ((r : A) * a) 0 = r * DirectSum.decompose 𝒜 a 0 := by
    intro r a
    apply Subtype.ext
    have := DirectSum.coe_decompose_mul_add_of_left_mem 𝒜 (i := 0) (j := 0) (b := a) r.2
    rw [add_zero] at this
    exact this
  let ρ : A →ₗ[𝒜 0] K :=
    { toFun := fun a => y (DirectSum.decompose 𝒜 a 0)
      map_add' := fun a b => by rw [DirectSum.decompose_add, DirectSum.add_apply, map_add]
      map_smul' := fun r a => by
        show y (DirectSum.decompose 𝒜 ((r : A) * a) 0) = y r * y (DirectSum.decompose 𝒜 a 0)
        rw [key, map_mul] }
  have hρ : ρ 1 = 1 := by
    show y (DirectSum.decompose 𝒜 ((1 : 𝒜 0) : A) 0) = 1
    rw [DirectSum.decompose_coe, DirectSum.of_eq_same, map_one]
  obtain ⟨η⟩ := pt_of_lin ρ hρ
  have hη : ∀ b : 𝒜 0, η b = y b := fun b => η.commutes b
  refine ⟨{ (η : A →+* K) with commutes' := fun r => ?_ }, hη⟩
  exact (hη (algebraMap O (𝒜 0) r)).trans (y.commutes r)

theorem UpperTheory.V.Ws.Po.extA :
    ∀ (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O] (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] [DecidableEq X] (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (W : WPres O X R), (∀ s, W.z s ∈ maximalIdeal R) → ∀ (K : Type) [Field K] [IsAlgClosed K] [Algebra O K] (y : W.gr 0 →ₐ[O] K),
      ∃ ξ : W.A →ₐ[O] K, ∀ b : W.gr 0, ξ b = y b := by
  intro O _ _ _ _ X _ _ _ _ R _ _ _ W hz K _ _ _ y
  haveI := (gr_noeth O X R W hz).2.1
  exact ext_graded W.gr y
