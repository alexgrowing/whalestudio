import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LinearDescent
import Development.AbelianVarietyTheory.Definitions.Divisors.GaloisRepOfPolarizedCuspidal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulMat
open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT
open scoped Classical

namespace GlobalTheory

theorem charpoly_mulLeft_eq_of_adjoin_eq_top {F A : Type*} [Field F] [CommRing A] [Algebra F A]
    [Module.Finite F A] (u : A) (P : F[X]) (hP : P.Monic) (hadj : Algebra.adjoin F {u} = ⊤)
    (hu : aeval u P = 0) (hdim : Module.finrank F A = P.natDegree) :
    (LinearMap.mulLeft F u).charpoly = P := by
  have hint : IsIntegral F u := ⟨P, hP, hu⟩
  let pb := PowerBasis.ofAdjoinEqTop hint hadj
  have hgen : pb.gen = u := PowerBasis.ofAdjoinEqTop_gen hint hadj
  have hmin : minpoly F u = P := by
    refine (Polynomial.eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hint) hP (minpoly.dvd F u hu) ?_).symm
    rw [← hdim, pb.finrank, PowerBasis.ofAdjoinEqTop_dim]
  have h1 := charpoly_leftMulMatrix pb
  rw [Algebra.leftMulMatrix_apply, LinearMap.charpoly_toMatrix, hgen, hmin] at h1
  exact h1

theorem charpoly_mulLeft_eq_map_symm : ∀ (K : GlobalTheory.UnitLemma.UQ) (B : GlobalTheory.UnitLemma.InvAlg K) (R : Type) [Field R] (e : K.E ≃+* R) (u : B.A) (Q : R[X]), Q.Monic → Algebra.adjoin K.E {u} = ⊤ → aeval u (Q.map e.symm.toRingHom) = 0 → Module.finrank K.E B.A = Q.natDegree → (LinearMap.mulLeft K.E u).charpoly = Q.map e.symm.toRingHom := by
  intro K B R _ e u Q hQ hadj hu hdim
  exact charpoly_mulLeft_eq_of_adjoin_eq_top u _ (hQ.map _) hadj hu (by rw [hdim, hQ.natDegree_map])

end GlobalTheory
