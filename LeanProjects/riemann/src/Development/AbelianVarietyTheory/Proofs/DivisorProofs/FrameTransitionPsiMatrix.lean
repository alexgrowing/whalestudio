import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IotaScalarOne

open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct

namespace GlobalTheory.DetInv

theorem isMat_twist : ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] (Λ : Type) [CommRing Λ] [Algebra ℤ_[p] Λ] (N h : ℕ) (ψ : RL p O Λ →+* RL p O Λ) (e e' t t' : (Fin N → RL p O Λ) ≃ₗ[Ainf p O] (Fin h → Ainf p O)) (X : Matrix (Fin h) (Fin h) (Ainf p O)) (Y : Matrix (Fin N) (Fin N) (RL p O Λ)), Function.Surjective ψ → (∀ w, t (fun i => ψ (w i)) = fun j => phiInv p O (e w j)) → (∀ w, t' (fun i => ψ (w i)) = fun j => phiInv p O (e' w j)) → IsMat e e' X Y → IsMat t t' (X.map (phiInv p O)) (Y.map ψ) := by
  intro p _ O _ _ _ Λ _ _ N h ψ e e' t t' X Y hψ ht ht' hXY v
  obtain ⟨w, rfl⟩ : ∃ w : Fin N → RL p O Λ, (fun i => ψ (w i)) = v :=
    ⟨fun i => (hψ (v i)).choose, funext fun i => (hψ (v i)).choose_spec⟩
  have hY : Y.map ψ *ᵥ (fun i => ψ (w i)) = fun i => ψ ((Y *ᵥ w) i) := by
    funext i
    exact (RingHom.map_mulVec ψ Y w i).symm
  rw [hY, ht, ht', ← hXY w]
  funext j
  exact (RingHom.map_mulVec (phiInv p O) X (e w) j).symm

end GlobalTheory.DetInv
