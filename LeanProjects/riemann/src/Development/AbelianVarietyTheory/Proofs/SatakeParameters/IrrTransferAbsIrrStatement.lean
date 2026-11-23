import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IrrTransferAbsIrr
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.HeckeCharEqOfLAdicRealisation
open Formalism.BasicNotions Formalism.ConjugateSelfDual Formalism.MainNotions Formalism.MainNotions.N Polynomial NumberField IsDedekindDomain ReciprocityTheory.Gal GlobalTheory.StringRepresentationDecomposition
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.absIrrSub_map_of_irredOn_map_Fbar : ∀ {l : ℕ} [Fact l.Prime] {Γ : Type} [Group Γ] {k k' : Type} [Field k] [Field k'] {r : ℕ}, 1 ≤ r → ∀ (rb : Γ →* GL (Fin r) k) (ι : k →+* Formalism.CyclotomicNorms.Fbar l), Formalism.CyclotomicNorms.IrredOn (mapRep ι rb) ⊤ → ∀ φ : k →+* k', AbsIrrSub (mapRep φ rb) ⊤ := by
  first | exact @GlobalTheory.StringRepresentationDecomposition.irr_transfer_absIrr | exact GlobalTheory.StringRepresentationDecomposition.irr_transfer_absIrr | (intros; apply GlobalTheory.StringRepresentationDecomposition.irr_transfer_absIrr <;> assumption)
