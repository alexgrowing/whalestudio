import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AlgebraMapNormCoeff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CharpolyDvdPowFinrankOfAevalEqZeroStatement
open CategoryTheory Polynomial GlobalTheory.NormalDescent TensorProduct

namespace GlobalTheory.NormalDescent

theorem exists_map_eq_charK : ∀ {A B K : Type} [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [CommRing B] [Field K]
    [Algebra A K] [IsFractionRing A K] (φ : A →+* B) (hφ : φ.Finite) (b : B),
    ∃ P : A[X], P.map (algebraMap A K) = charK φ hφ K b := by
  intro A B K _ _ _ _ _ _ _ φ hφ b
  letI := φ.toAlgebra
  haveI : Module.Finite A B := hφ
  obtain ⟨g, hgm, hg⟩ := (Algebra.IsIntegral.isIntegral (R := A) b)
  have hT : aeval (Algebra.lmul K (K ⊗[A] B) (1 ⊗ₜ b)) (g.map (algebraMap A K)) = 0 := by
    rw [Polynomial.aeval_algHom_apply, Polynomial.aeval_map_algebraMap]
    have : (1 : K) ⊗ₜ[A] b = Algebra.TensorProduct.includeRight b := rfl
    rw [this, Polynomial.aeval_algHom_apply, show aeval b g = 0 from hg, map_zero, map_zero]
  have hd := GlobalTheory.T.charpoly_dvd_pow_finrank_of_aeval_eq_zero _ _ hT
  rw [← Polynomial.map_pow] at hd
  obtain ⟨P, hP⟩ := IsIntegrallyClosed.eq_map_mul_C_of_dvd K (hgm.pow _) hd
  refine ⟨P, ?_⟩
  have hm : (charK φ hφ K b).Monic := charK_monic φ hφ K b
  have : (Algebra.lmul K (K ⊗[A] B) (1 ⊗ₜ b)).charpoly = charK φ hφ K b := rfl
  rw [this, hm.leadingCoeff, C_1, mul_one] at hP
  exact hP

end GlobalTheory.NormalDescent
