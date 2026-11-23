import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharConjSelfDualInfinityInfinitesimalIffFie
import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CGTrue
open Formalism.BasicNotions Formalism.L2.Host GlobalTheory.CuspRep NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeChar_conjSelfDual_infinity_infinitesimal_iff_field : ∀ {R : Ranks} (H : Formalism.BasicNotions.Host R) (χ : HChar H.E), haveI := host_isCMField H; (∀ z, dchi χ (-star z) = dchi χ z) ↔ ∀ k : H.Eˣ, χ.inf (Units.map (MonoidHomClass.toMonoidHom H.conj) k) = (χ.inf k)⁻¹ := by
  first | exact @GlobalTheory.CuspRep.csdInf_iff | exact GlobalTheory.CuspRep.csdInf_iff | (intros; apply GlobalTheory.CuspRep.csdInf_iff <;> assumption)
