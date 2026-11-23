import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharConjSelfDualFiniteIdelicIffLocal
import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CGTrue
open Formalism.BasicNotions Formalism.L2.Host GlobalTheory.CuspRep NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeChar_conjSelfDual_finite_idelic_iff_local : ∀ {R : Ranks} (H : Formalism.BasicNotions.Host R) (χ : HChar H.E), haveI := host_isCMField H; (∀ u : (Af H.E)ˣ, χ.1 (finId H.E (Units.map (conjFin (IsCMField.complexConj H.E).toRingEquiv).toMonoidHom u)⁻¹) = χ.1 (finId H.E u)) ↔ ∀ w w', IsConjPl H w w' → ∀ k : H.Eˣ, χ.locK w' (Units.map (MonoidHomClass.toMonoidHom H.conj) k) = (χ.locK w k)⁻¹ := by
  first | exact @GlobalTheory.CuspRep.csdFin_iff | exact GlobalTheory.CuspRep.csdFin_iff | (intros; apply GlobalTheory.CuspRep.csdFin_iff <;> assumption)
