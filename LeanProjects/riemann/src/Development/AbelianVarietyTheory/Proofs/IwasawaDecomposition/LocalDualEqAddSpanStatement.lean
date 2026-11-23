import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalDualEqAddSpan
import Mathlib
import Formalism.LocalRingCardinality.DataLevel
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Afsplit
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.UG Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_latS_eq_of_lattice_last_coord_dvd : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (w : HeightOneSpectrum (𝓞 F)) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (L : Submodule (𝓞 E) (Fin n → E)) (p : 𝓞 E), J = 1 → p ≠ 0 → (∀ x, x ∈ L ↔ ∀ j : Fin n, ∃ r : 𝓞 E, x j = (r : E) ∧ (j.1 + 1 = n → p ∣ r)) → (∀ x, σ (σ x) = x) → ∃ e : latS (F := F) (w.adicCompletion F) (intV E w) (Submodule.span (𝓞 E) (dualSet (σ : E →+* E) J L)), ∀ t : latS (F := F) (w.adicCompletion F) (intV E w) (Submodule.span (𝓞 E) (dualSet (σ : E →+* E) J L)), ∃ s : intV E w, (t - s • e).1 ∈ latS (F := F) (w.adicCompletion F) (intV E w) L := by
  first | exact @GlobalTheory.Mem.LocalDualBase.localDual_eq_add_span | exact GlobalTheory.Mem.LocalDualBase.localDual_eq_add_span | (intros; apply GlobalTheory.Mem.LocalDualBase.localDual_eq_add_span <;> assumption)
