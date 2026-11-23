import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DualLatticeLocalCharacterization
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.SelfDualAt
import Formalism.LocalToGlobal.HermitianForms.TiedStep
open Formalism.BasicNotions Formalism.UG Formalism.L2.Forms NumberField IsDedekindDomain Matrix GlobalTheory.St.G
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dual_lattice_local_characterization : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (cm : CMData F E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHerm (cm.sig : E →+* E) J → J.det ≠ 0 → ∀ (L : Submodule (𝓞 E) (Fin n → E)), IsLat L → IsLat (dualL cm.sig J L) ∧ (∀ (v : HeightOneSpectrum (𝓞 F)) (x : Fin n → E ⊗[F] v.adicCompletion F), x ∈ loc v (dualL cm.sig J L) ↔ ∀ z ∈ loc v L, hR cm.sig J (v.adicCompletion F) z x ∈ intV E v) ∧ ∀ x : Fin n → E ⊗[F] Ad F, x ∈ hat F (dualL cm.sig J L) ↔ ∀ z ∈ hat F L, hR cm.sig J (Ad F) z x ∈ OAd F E := by
  first | exact @GlobalTheory.St.G.dualL_local_adelic | exact GlobalTheory.St.G.dualL_local_adelic | (intros; apply GlobalTheory.St.G.dualL_local_adelic <;> assumption)
