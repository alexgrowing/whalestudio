import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocLEqIntVOfDvdUnit
import Mathlib
import Formalism.LocalToGlobal.HermitianColumns.InLocalDiscriminantKernel
import Formalism.LocalRingCardinality.DataLevel
open NumberField IsDedekindDomain
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_locL_iff_forall_mem_intV_of_not_mem : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
    (v : HeightOneSpectrum (𝓞 F)) {n : ℕ} (Λ : Submodule (𝓞 E) (Fin n → E)) (P : Fin n → Prop) (π c : 𝓞 E) (T : ℕ),
    (T : 𝓞 F) ∉ v.asIdeal → π * c = (T : 𝓞 E) →
    (∀ y, y ∈ Λ ↔ ∀ a, ∃ r : 𝓞 E, y a = r ∧ (P a → π ∣ r)) → ∀ (y : Fin n → E ⊗[F] v.adicCompletion F),
    (y ∈ Formalism.L2.Herm.locL v Λ ↔ ∀ a, y a ∈ Formalism.BasicNotions.intV E v) := by
  first | exact @GlobalTheory.locL_eq_intV_of_dvd_unit | exact GlobalTheory.locL_eq_intV_of_dvd_unit | (intros; apply GlobalTheory.locL_eq_intV_of_dvd_unit <;> assumption)
