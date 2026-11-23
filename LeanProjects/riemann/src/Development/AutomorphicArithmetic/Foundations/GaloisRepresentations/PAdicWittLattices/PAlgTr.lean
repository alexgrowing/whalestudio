import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.SplitsBasic

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.GalV GlobalTheory.HodgeCoh TensorProduct UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (FEt Cover gen piece IsHEig)
universe u v

private theorem trace_pi_eq_sum {C J : Type} [CommRing C] [Fintype J] (a : J → C) :
    Algebra.trace C (J → C) a = ∑ j, a j := by
  classical
  rw [Algebra.trace_apply, LinearMap.trace_eq_matrix_trace C (Pi.basisFun C J), Matrix.trace]
  apply Finset.sum_congr rfl
  intro j _
  simp [LinearMap.toMatrix_apply, Pi.single_apply]

theorem UpperTheory.Gal.G3.pAlgTr :
    AlgTr := by
  intro A A' C _ _ _ _ _ _ _ J _ τ e he b
  letI : Algebra A' (C ⊗[A] A') := Algebra.TensorProduct.rightAlgebra
  haveI : Module.Projective A A' := projective_of_etale A A'
  haveI : Module.Free C (C ⊗[A] A') := Module.Free.of_equiv e.symm.toLinearEquiv
  haveI : Module.Finite C (C ⊗[A] A') := Module.Finite.equiv e.symm.toLinearEquiv
  have h1 := algTrace_of_isPushout (B := A) (B' := A') (C := C) (C' := C ⊗[A] A') b
  have h2 : (etTrace A A') b = (algTrace A A') b := rfl
  rw [h2, ← h1, algTrace_eq_trace]
  have h3 : algebraMap A' (C ⊗[A] A') b = e.symm (e (1 ⊗ₜ[A] b)) := by
    rw [AlgEquiv.symm_apply_apply]
    rfl
  rw [h3, Algebra.trace_eq_of_algEquiv e.symm, trace_pi_eq_sum]
  exact Finset.sum_congr rfl fun j _ => he b j
