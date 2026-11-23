import Mathlib
import Formalism.SharpRestriction.GlobalSchurBounds.StandardLattice
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.DualExponentDensity
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.ActionCoordinates
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.LocalDensityEuler
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.LatticeTensorUnfolding
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsArchAdeleTensorEquivComplexCmType
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions.StandardLattice Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke
open scoped ENNReal TensorProduct

namespace GlobalTheory.RealSpaceCoord

theorem herm_eq_dot {P Q : ℕ} (x y : ActionCoordinates.Wsp P Q) :
    ActionCoordinates.herm y x = star x ⬝ᵥ (Formalism.UG.Jpq P Q *ᵥ y) := by
  simp [ActionCoordinates.herm, ActionCoordinates.sgn, Formalism.UG.Jpq, Fintype.sum_sum_type, dotProduct, fromBlocks_mulVec, neg_mulVec,
    mul_comm]

theorem form_eq {M P Q : ℕ} (A : Matrix (Fin P ⊕ Fin Q) (Fin M) ℂ) (x y : Fin M → ℂ) :
    ∑ i, ∑ j, star (x i) * (Aᴴ * Formalism.UG.Jpq P Q * A) i j * y j = ActionCoordinates.herm (A *ᵥ y) (A *ᵥ x) := by
  rw [herm_eq_dot, star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec]
  simp only [dotProduct, mulVec, Finset.mul_sum, mul_assoc, Pi.star_apply]

theorem exists_coord : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (T : Type) [Fintype T] (τ : T → (E →+* ℂ)) (θ : T → (Ainf F ⊗[F] E →+* ℂ)), (Function.Bijective fun ρ => InfinitePlace.mk (τ ρ)) → (∀ ρ, IsInfEmb (τ ρ) (θ ρ)) → ∀ (M P Q : ℕ), P + Q = M → ∀ J : Matrix (Fin M) (Fin M) E, IsHermND σ J → ∀ A : T → Matrix (Fin P ⊕ Fin Q) (Fin M) ℂ, (∀ ρ, (A ρ)ᴴ * Formalism.UG.Jpq P Q * A ρ = J.map (τ ρ)) → ∃ e : (Fin 1 → Fin M → Ainf F ⊗[F] E) ≃ₜ+ (T → ActionCoordinates.Wsp P Q), (∀ X ρ, e X ρ = A ρ *ᵥ fun i => θ ρ (X 0 i)) ∧ ∀ X Y ρ, θ ρ (hR (Ainf F) σ J (X 0) (Y 0)) = ActionCoordinates.herm (e Y ρ) (e X ρ) := by
  intro F E _ _ _ _ _ σ h T _ τ θ hτ hθ M P Q hM J hJ A hA
  obtain ⟨e0, he, hc, hc', hs⟩ := GlobalTheory.Mem.VolInfIso.exists_infAdele_equiv F E σ T τ θ h hτ hθ
  let B : T → Matrix (Fin M) (Fin P ⊕ Fin Q) ℂ := fun ρ => (J.map (τ ρ))⁻¹ * ((A ρ)ᴴ * Formalism.UG.Jpq P Q)
  have hBA : ∀ ρ, B ρ * A ρ = 1 := fun ρ => by
    have hd : (J.map (τ ρ)).det = τ ρ J.det := ((τ ρ).map_det J).symm
    simp only [B]
    rw [Matrix.mul_assoc, hA, Matrix.nonsing_inv_mul]
    rw [hd]
    exact ((map_ne_zero (τ ρ)).2 hJ.2).isUnit
  have hAB : ∀ ρ, A ρ * B ρ = 1 := fun ρ =>
    (Matrix.mul_eq_one_comm_of_card_eq _ _ _ (by simp [hM])).2 (hBA ρ)
  have he' : ∀ z ρ, θ ρ (e0.symm z) = z ρ := fun z ρ => by rw [← he, e0.apply_symm_apply]
  refine ⟨{ toFun := fun X ρ => A ρ *ᵥ fun i => θ ρ (X 0 i)
            invFun := fun z _ i => e0.symm fun ρ => (B ρ *ᵥ z ρ) i
            left_inv := fun X => ?_
            right_inv := fun z => ?_
            map_add' := fun X Y => ?_
            continuous_toFun := ?_
            continuous_invFun := ?_ }, fun _ _ => rfl, fun X Y ρ => ?_⟩
  · funext k i
    obtain rfl : k = 0 := Subsingleton.elim _ _
    simp only [mulVec_mulVec, hBA, one_mulVec]
    rw [RingEquiv.symm_apply_eq]
    funext ρ
    rw [he]
  · funext ρ
    simp only [he']
    rw [mulVec_mulVec, hAB, one_mulVec]
  · funext ρ
    refine Eq.trans ?_ (mulVec_add (A ρ) (fun i => θ ρ (X 0 i)) (fun i => θ ρ (Y 0 i)))
    congr 1
    funext i
    simp
  · refine continuous_pi fun ρ => continuous_const.matrix_mulVec (continuous_pi fun i => ?_)
    simp only [← he]
    exact (continuous_apply ρ).comp (hc.comp ((continuous_apply i).comp (continuous_apply 0)))
  · exact continuous_pi fun _ => continuous_pi fun i => hc'.comp (continuous_pi fun ρ =>
      (continuous_apply i).comp (continuous_const.matrix_mulVec (continuous_apply ρ)))
  · refine Eq.trans ?_ (form_eq (A ρ) (fun i => θ ρ (X 0 i)) (fun i => θ ρ (Y 0 i)))
    rw [hA]
    simp only [hR, Formalism.UG.hform, map_sum, map_mul]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [GlobalTheory.Mem.VolInfIso.infEmb_sigR σ (τ ρ) (θ ρ) h (hθ ρ)]
    congr 2
    exact (hθ ρ).1 _

end GlobalTheory.RealSpaceCoord
