import Mathlib

theorem UpperTheory.Reformulated.B.IntegralExtensionAlgClosed.exists_ringHom_extension_of_integral :
    ∀ (R S K : Type) [inst : CommRing R] [inst_1 : CommRing S]
    [inst_2 : Algebra R S] [Algebra.IsIntegral R S] [inst_4 : Field K] [IsAlgClosed K],
    Function.Injective (⇑(Algebra.algebraMap R S) : R → S) →
      ∀ (b : R →+* K), ∃ (Φ : S →+* K), Φ.comp (Algebra.algebraMap R S) = b := by
  intro R S K _ _ _ _ _ _ hinj b
  haveI hp : (RingHom.ker b).IsPrime := RingHom.ker_isPrime b
  obtain ⟨Q, -, hQ, hQp⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (S := S)
    (RingHom.ker b) ⊥ (by
      intro x hx
      have hx0 : algebraMap R S x = 0 := by simpa using hx
      have : x = 0 := hinj (by simpa using hx0)
      simp [this])
  haveI : Q.LiesOver (RingHom.ker b) := ⟨hQp.symm⟩
  letI : Algebra (R ⧸ RingHom.ker b) K := (RingHom.kerLift b).toAlgebra
  haveI : FaithfulSMul (R ⧸ RingHom.ker b) K :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (RingHom.kerLift_injective b)
  haveI : Algebra.IsIntegral (R ⧸ RingHom.ker b) (S ⧸ Q) := inferInstance
  haveI : FaithfulSMul (R ⧸ RingHom.ker b) (S ⧸ Q) := inferInstance
  haveI : Module.IsTorsionFree (R ⧸ RingHom.ker b) (S ⧸ Q) :=
    Module.isTorsionFree_iff_faithfulSMul.2 inferInstance
  haveI : Module.IsTorsionFree (R ⧸ RingHom.ker b) K :=
    Module.isTorsionFree_iff_faithfulSMul.2 inferInstance
  haveI : Algebra.IsAlgebraic (R ⧸ RingHom.ker b) (S ⧸ Q) := Algebra.IsIntegral.isAlgebraic
  let ψ : (S ⧸ Q) →ₐ[R ⧸ RingHom.ker b] K := IsAlgClosed.lift
  refine ⟨ψ.toRingHom.comp (Ideal.Quotient.mk Q), ?_⟩
  ext x
  exact ψ.commutes (Ideal.Quotient.mk (RingHom.ker b) x)
