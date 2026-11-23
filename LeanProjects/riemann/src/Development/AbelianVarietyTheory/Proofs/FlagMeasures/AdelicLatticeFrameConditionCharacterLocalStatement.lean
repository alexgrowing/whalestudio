import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdelicLatticeFrameConditionCharacterLocal
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.SelfDualAt
import Formalism.LocalToGlobal.HermitianForms.TiedStep
open Formalism.BasicNotions Formalism.UG Formalism.L2.Forms NumberField IsDedekindDomain Matrix GlobalTheory.St.G
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelicLatticeFrame_condition_character_local : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (cm : CMData F E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHerm (cm.sig : E →+* E) J → J.det ≠ 0 → ∀ (k : ℕ) (gp : Fin 2 → ℕ) (L : Submodule (𝓞 E) (Fin n → E)) (Fr : AdFrame cm.sig J (hat F L) (gp 0 * gp 1) k), (∀ i, (gp i).Prime) → gp 0 ≠ gp 1 → IsLat L → (∀ x ∈ L, x ∈ dualSet (cm.sig : E →+* E) J L) → ∀ y : GL (Fin n) (E ⊗[F] Ad F), y ∈ stabGL (hat F L) → ((∀ i : Fin k, InModL (hat F L) (gp 0 * gp 1) (Fr.b '' {j | j.1 < i.1}) ((y.1 - 1) *ᵥ Fr.b i)) ↔ ∀ (i : Fin 2) (v : HeightOneSpectrum (𝓞 F)), (gp i : 𝓞 F) ∈ v.asIdeal → Fr.LocK L v (bc (prV (E := E) v) y)) ∧ Fr.chi y = ∏ i : Fin 2, ∏ᶠ (v : HeightOneSpectrum (𝓞 F)) (_ : (gp i : 𝓞 F) ∈ v.asIdeal), Fr.locChi v (bc (prV (E := E) v) y) := by
  first | exact @GlobalTheory.St.G.frame_local | exact GlobalTheory.St.G.frame_local | (intros; apply GlobalTheory.St.G.frame_local <;> assumption)
