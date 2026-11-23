import Mathlib

theorem UpperTheory.Reformulated.B.Qi28.exists_extend.{u_1, u_2} :
    ∀ {R : Type u_1} {A : Type u_2} [inst : CommRing R] [inst_1 : CommRing A] [inst_2 : Algebra R A]
    [Algebra.IsIntegral R A] (ev : R →+* ℂ),
    RingHom.ker (Algebra.algebraMap R A) ≤ RingHom.ker ev → ∃ (χ : A →+* ℂ), χ.comp (Algebra.algebraMap R A) = ev := by
  intro R A _ _ _ _ ev h
  haveI hP : (RingHom.ker ev).IsPrime := RingHom.ker_isPrime ev
  obtain ⟨Q, -, hQ, hQP⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (S := A) (RingHom.ker ev) ⊥
    (by rw [← RingHom.ker_eq_comap_bot]; exact h)
  haveI : Q.LiesOver (RingHom.ker ev) := ⟨hQP.symm⟩
  letI : Algebra (R ⧸ RingHom.ker ev) ℂ := (RingHom.kerLift ev).toAlgebra
  haveI : FaithfulSMul (R ⧸ RingHom.ker ev) ℂ :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (RingHom.kerLift_injective ev)
  haveI : Algebra.IsAlgebraic (R ⧸ RingHom.ker ev) (A ⧸ Q) := Algebra.IsIntegral.isAlgebraic
  haveI : FaithfulSMul (R ⧸ RingHom.ker ev) (A ⧸ Q) := inferInstance
  haveI : IsDomain (R ⧸ RingHom.ker ev) := Ideal.Quotient.isDomain _
  haveI : IsDomain (A ⧸ Q) := Ideal.Quotient.isDomain _
  haveI : Module.IsTorsionFree (R ⧸ RingHom.ker ev) (A ⧸ Q) :=
    Module.isTorsionFree_iff_faithfulSMul.2 ‹_›
  haveI : Module.IsTorsionFree (R ⧸ RingHom.ker ev) ℂ :=
    Module.isTorsionFree_iff_faithfulSMul.2 ‹_›
  let φ : (A ⧸ Q) →ₐ[R ⧸ RingHom.ker ev] ℂ := IsAlgClosed.lift
  refine ⟨(φ : (A ⧸ Q) →+* ℂ).comp (Ideal.Quotient.mk Q), ?_⟩
  ext r
  exact φ.commutes (Ideal.Quotient.mk (RingHom.ker ev) r)
