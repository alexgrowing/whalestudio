import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPrimitiveAnnihilator
import Mathlib
open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_primitive_annihilator' : ∀ (F : Type) [Field F] [NumberField F] (W Ω : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Ω] [CharZero Ω] [IsAlgClosed Ω] (f : W →+* Ω), Function.Injective f → ∀ (n : ℕ) (M : 𝓞 F →+* Matrix (Fin n) (Fin n) W) (σ : 𝓞 F →+* Ω), (∀ c : Fin n → Ω, (∀ a, ((M a).map f).mulVec c = σ a • c) → c = 0) → ∀ (ι : Type) [Fintype ι] (b : Module.Basis ι ℤ (𝓞 F)), ∃ w : ι → W, (∃ i, IsUnit (w i)) ∧ ∑ i, w i • M (b i) = 0 := by
  first | exact @GlobalTheory.PrimAnnih.exists_primitive_annihilator | exact GlobalTheory.PrimAnnih.exists_primitive_annihilator | (intros; apply GlobalTheory.PrimAnnih.exists_primitive_annihilator <;> assumption)
