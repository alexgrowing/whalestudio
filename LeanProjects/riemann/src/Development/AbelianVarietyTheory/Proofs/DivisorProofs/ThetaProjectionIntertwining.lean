import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IotaScalarOne
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct

namespace GlobalTheory.DetInv

theorem proj_redC_intertwine : ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] (C : Type) [Field C] [Algebra O C] (Λ : Type) [CommRing Λ] [Algebra ℤ_[p] Λ] (N h : ℕ) (f : RL p O Λ →+* O) (e e' : (Fin N → RL p O Λ) ≃ₗ[Ainf p O] (Fin h → Ainf p O)) (π π' : (Fin h → C) →ₗ[C] (Fin N → C)) (X : Matrix (Fin h) (Fin h) (Ainf p O)) (Y : Matrix (Fin N) (Fin N) (RL p O Λ)), IsProj C e f π → IsProj C e' f π' → IsMat e e' X Y → ∀ z, π' (redC C X z) = Y.map ((algebraMap O C).comp f) *ᵥ π z := by
  intro p _ O _ _ _ C _ _ Λ _ _ N h f e e' π π' X Y hπ hπ' hX z
  have key : ∀ w : Fin N → RL p O Λ,
      π' (redC C X (fun j => algebraMap O C (WittVector.fontaineTheta O p (e w j)))) =
      Y.map ((algebraMap O C).comp f) *ᵥ π (fun j => algebraMap O C (WittVector.fontaineTheta O p (e w j))) := by
    intro w
    rw [hπ w]
    have h1 : redC C X (fun j => algebraMap O C (WittVector.fontaineTheta O p (e w j))) =
        fun j => algebraMap O C (WittVector.fontaineTheta O p (e' (Y *ᵥ w) j)) := by
      rw [← hX w]
      funext i
      simp only [redC, Matrix.toLin'_apply]
      exact (RingHom.map_mulVec ((algebraMap O C).comp (WittVector.fontaineTheta O p)) X (e w) i).symm
    rw [h1, hπ' (Y *ᵥ w)]
    funext i
    exact RingHom.map_mulVec ((algebraMap O C).comp f) Y w i
  have hL : π' ∘ₗ redC C X = (Matrix.toLin' (Y.map ((algebraMap O C).comp f))) ∘ₗ π := by
    refine (Pi.basisFun C (Fin h)).ext fun j => ?_
    have hs : (Pi.basisFun C (Fin h)) j =
        fun k => algebraMap O C (WittVector.fontaineTheta O p (e (e.symm (Pi.single j (1 : Ainf p O))) k)) := by
      rw [LinearEquiv.apply_symm_apply]
      funext k
      rw [Pi.basisFun_apply]
      rcases eq_or_ne k j with rfl | hk <;> simp [*]
    rw [hs, LinearMap.comp_apply, LinearMap.comp_apply, Matrix.toLin'_apply]
    exact key _
  have := LinearMap.congr_fun hL z
  rw [LinearMap.comp_apply, LinearMap.comp_apply, Matrix.toLin'_apply] at this
  exact this

end GlobalTheory.DetInv
