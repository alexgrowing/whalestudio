import Mathlib

open scoped TensorProduct nonZeroDivisors

namespace GlobalTheory.IndefiniteRowSideFullHecke.TensorProductAction

section Defs

variable (Λ : Type) [CommRing Λ] (O : Type) [CommRing O] [Algebra Λ O]

noncomputable def tensorAction (R : Type) [CommRing R] [Algebra Λ R]
    (T : Type) [AddCommGroup T] [Module Λ T] [Module O T] [IsScalarTower Λ O T] :
    R ⊗[Λ] O →ₐ[R] Module.End R (R ⊗[Λ] T) :=
  Algebra.TensorProduct.lift (Algebra.ofId R _)
    ((Module.End.baseChangeHom Λ R T).comp (Algebra.lsmul Λ Λ T))
    (fun r _ => Algebra.commute_algebraMap_left r _)

@[reducible] noncomputable def tensorModule (R : Type) [CommRing R] [Algebra Λ R]
    (T : Type) [AddCommGroup T] [Module Λ T] [Module O T] [IsScalarTower Λ O T] :
    Module (R ⊗[Λ] O) (R ⊗[Λ] T) :=
  Module.compHom (R ⊗[Λ] T) (tensorAction Λ O R T).toRingHom

noncomputable def act (R : Type) [CommRing R] [Algebra Λ R]
    (X : Type) [AddCommGroup X] [Module R X] [Module (R ⊗[Λ] O) X]
    [IsScalarTower R (R ⊗[Λ] O) X] (a : O) : X →ₗ[R] X :=
  Algebra.lsmul R R X ((1 : R) ⊗ₜ[Λ] a : R ⊗[Λ] O)

variable {Λ O}
variable {R : Type} [CommRing R] [Algebra Λ R] (C : Type) [Field C] [Algebra R C]
  (τ : O →ₐ[Λ] R)
  (X : Type) [AddCommGroup X] [Module R X] [Module (R ⊗[Λ] O) X] [IsScalarTower R (R ⊗[Λ] O) X]

noncomputable def coeigen : Submodule C (C ⊗[R] X) :=
  Submodule.span C
    {z | ∃ (a : O) (y : C ⊗[R] X),
      z = (act Λ O R X a).baseChange C y - algebraMap R C (τ a) • y}

noncomputable def toEigen : X →ₗ[R] (C ⊗[R] X) ⧸ coeigen C τ X :=
  ((coeigen C τ X).mkQ.restrictScalars R).comp (TensorProduct.mk R C X 1)

noncomputable def eigenQuot : Submodule R ((C ⊗[R] X) ⧸ coeigen C τ X) :=
  LinearMap.range (toEigen C τ X)

noncomputable def eigenProj : X →ₗ[R] eigenQuot C τ X :=
  (toEigen C τ X).rangeRestrict

noncomputable def evalAt : R ⊗[Λ] O →+* R :=
  (Algebra.TensorProduct.lift (AlgHom.id R R) τ (fun _ _ => Commute.all _ _)).toRingHom

noncomputable def reduceRing (O : Type) [CommRing O] [Algebra Λ O] {A : Type} [CommRing A]
    [Algebra Λ A] (θ : A →ₐ[Λ] R) : A ⊗[Λ] O →+* R ⊗[Λ] O :=
  (Algebra.TensorProduct.map θ (AlgHom.id Λ O)).toRingHom

end Defs

def FreenessLemma : Prop :=
  ∀ (l : ℕ) [Fact l.Prime]
    (E : Type) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    [Algebra ℤ_[l] E] [IsScalarTower ℤ_[l] ℚ_[l] E]
    (O : Type) [CommRing O] [Algebra ℤ_[l] O] [Algebra O E] [IsScalarTower ℤ_[l] O E]
    [IsIntegralClosure O ℤ_[l] E]
    (k : Type) [Field k] [IsAlgClosed k] [CharP k l]
    (A : Type) [CommRing A] [IsLocalRing A] [Algebra ℤ_[l] A]
    (ρ : A →+* WittVector l k)
    (_ : Function.Surjective (WittVector.constantCoeff.comp ρ : A →+* k))
    (μ : A) (_ : μ ∈ A⁰)
    (N : ℕ)
    (T : Type) [AddCommGroup T] [Module ℤ_[l] T] [Module O T] [IsScalarTower ℤ_[l] O T]
    [Module.Finite ℤ_[l] T] [Module.Free ℤ_[l] T]
    (_ : Module.finrank ℤ_[l] T = Module.finrank ℚ_[l] E * N)
    (M : Type) [AddCommGroup M] [Module A M] [Module (A ⊗[ℤ_[l]] O) M]
    [IsScalarTower A (A ⊗[ℤ_[l]] O) M] [Module.Finite A M] [Module.Free A M]
    (j : Localization.Away μ ⊗[A] M ≃ₗ[Localization.Away μ] Localization.Away μ ⊗[ℤ_[l]] T)
    (_ : ∀ (a : O) (y : Localization.Away μ ⊗[A] M),
      j ((act ℤ_[l] O A M a).baseChange (Localization.Away μ) y) =
        tensorAction ℤ_[l] O (Localization.Away μ) T (1 ⊗ₜ a) (j y)),
    Nonempty (Module.Basis (Fin N) O T) ∧
    Nonempty (Module.Basis (Fin N) (A ⊗[ℤ_[l]] O) M) ∧
    ∀ (R : Type) [CommRing R] [IsDomain R] [Algebra ℤ_[l] R]
      (C : Type) [Field C] [Algebra R C] [IsFractionRing R C]
      (θ : A →ₐ[ℤ_[l]] R) (_ : Function.Surjective θ)
      (ξ : A) (_ : RingHom.ker θ = Ideal.span {ξ})
      (H : Type) [AddCommGroup H] [Module R H] [Module (R ⊗[ℤ_[l]] O) H]
      [IsScalarTower R (R ⊗[ℤ_[l]] O) H]
      (q : M →ₛₗ[reduceRing O θ] H) (_ : Function.Surjective q)
      (_ : ∀ m : M, q m = 0 ↔ ∃ m' : M, m = ξ • m'),
      Nonempty (Module.Basis (Fin N) (R ⊗[ℤ_[l]] O) H) ∧
      (letI := tensorModule ℤ_[l] O R T
       Nonempty (Module.Basis (Fin N) (R ⊗[ℤ_[l]] O) (R ⊗[ℤ_[l]] T))) ∧
      ∀ τ : O →ₐ[ℤ_[l]] R,
        Nonempty (Module.Basis (Fin N) R (eigenQuot C τ H)) ∧
        (∃ (f : ⋀[A ⊗[ℤ_[l]] O]^N M →ₛₗ[reduceRing O θ] ⋀[R ⊗[ℤ_[l]] O]^N H)
           (g : ⋀[R ⊗[ℤ_[l]] O]^N H →ₛₗ[evalAt τ] ⋀[R]^N (eigenQuot C τ H)),
          (∀ x : Fin N → M, f (exteriorPower.ιMulti _ N x) =
            exteriorPower.ιMulti _ N (fun i => q (x i))) ∧
          (∀ h : Fin N → H, g (exteriorPower.ιMulti _ N h) =
            exteriorPower.ιMulti _ N (fun i => eigenProj C τ H (h i))) ∧
          Function.Surjective f ∧ Function.Surjective g) ∧
        ∃ d : eigenQuot C τ (⋀[R ⊗[ℤ_[l]] O]^N H) ≃ₗ[R] ⋀[R]^N (eigenQuot C τ H),
          ∀ h : Fin N → H,
            d (eigenProj C τ _ (exteriorPower.ιMulti _ N h)) =
              exteriorPower.ιMulti _ N (fun i => eigenProj C τ H (h i))

example (l : ℕ) [Fact l.Prime] (k : Type) [Field k] [IsAlgClosed k] [CharP k l] :
    IsLocalRing (WittVector l k) ∧
    Function.Surjective
      (WittVector.constantCoeff.comp (RingHom.id (WittVector l k)) : WittVector l k →+* k) ∧
    (l : WittVector l k) ∈ (WittVector l k)⁰ := by
  refine ⟨inferInstance, fun x => ⟨WittVector.teichmuller l x, by simp⟩, ?_⟩
  exact mem_nonZeroDivisors_of_ne_zero (WittVector.p_nonzero l k)

end GlobalTheory.IndefiniteRowSideFullHecke.TensorProductAction
