import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SimilitudePairGramInvCongruent
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BijectiveRealTensorToProdMatrixAlgebrasInfPlacesStatement
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.LKMid

theorem trivR_of_gram_psi_inv_congr : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (β : G.Cˣ),
    (∀ v : InfinitePlace G.F, ∃ W : GL (Fin G.n) ℂ, G.gram v * G.psi v ((β⁻¹ : G.Cˣ) : G.C) =
      (W : Matrix (Fin G.n) (Fin G.n) ℂ)ᴴ * G.gram v * (W : Matrix (Fin G.n) (Fin G.n) ℂ)) →
    ∃ z : (ℝ ⊗[ℚ] G.C)ˣ, Triv G ℝ β z 1 := by
  intro p _ G β hW
  choose W hW using hW
  obtain ⟨hinj, hsurj⟩ := GlobalTheory.T.bijective_realTensor_to_prod_matrixAlgebras_infPlaces p G
  obtain ⟨z, hz⟩ := hsurj (fun v => (W v : Matrix (Fin G.n) (Fin G.n) ℂ))
  obtain ⟨z', hz'⟩ := hsurj (fun v => (((W v)⁻¹ : GL (Fin G.n) ℂ) : Matrix (Fin G.n) (Fin G.n) ℂ))
  have hz1 : ∀ v, G.psiR v z = (W v : Matrix (Fin G.n) (Fin G.n) ℂ) := fun v => congrFun hz v
  have hz2 : ∀ v, G.psiR v z' = (((W v)⁻¹ : GL (Fin G.n) ℂ) : Matrix (Fin G.n) (Fin G.n) ℂ) :=
    fun v => congrFun hz' v
  have e1 : z * z' = 1 := hinj (funext fun v => show G.psiR v (z * z') = G.psiR v 1 by
    rw [map_mul, map_one, hz1, hz2, Units.mul_inv])
  have e2 : z' * z = 1 := hinj (funext fun v => show G.psiR v (z' * z) = G.psiR v 1 by
    rw [map_mul, map_one, hz1, hz2, Units.inv_mul])
  refine ⟨⟨z, z', e1, e2⟩, ?_⟩
  unfold Triv
  rw [Units.val_one, map_one]
  apply hinj
  funext v
  show G.psiR v (z * inC G ℝ (β : G.C) * (starT G.star ℝ z).unop) = G.psiR v 1
  have hb : G.psiR v (inC G ℝ (β : G.C)) = G.psi v (β : G.C) := by
    change G.psiR v ((1 : ℝ) ⊗ₜ (β : G.C)) = _
    rw [psiR_tmul, one_smul]
  rw [map_mul, map_mul, psiR_starT, hb, hz1, map_one]
  set Wm : Matrix (Fin G.n) (Fin G.n) ℂ := (W v : Matrix (Fin G.n) (Fin G.n) ℂ)
  have hg : IsUnit (G.gram v).det := isUnit_iff_ne_zero.2 (G.gram_det v)
  have hM : (G.gram v)⁻¹ * Wmᴴ * G.gram v * Wm = G.psi v ((β⁻¹ : G.Cˣ) : G.C) := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc Wmᴴ, ← hW v, ← Matrix.mul_assoc,
      Matrix.nonsing_inv_mul _ hg, Matrix.one_mul]
  have hBA : ((G.gram v)⁻¹ * Wmᴴ * G.gram v) * (Wm * G.psi v (β : G.C)) = 1 := by
    rw [← Matrix.mul_assoc, hM, ← map_mul, Units.inv_mul, map_one]
  have hAB := mul_eq_one_comm.1 hBA
  simpa [Matrix.mul_assoc] using hAB

end GlobalTheory.LKMid
