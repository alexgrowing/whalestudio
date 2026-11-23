import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SymplecticRestrictionIsotropicPartEqPairing
import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HalfSymplZeroRight
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition GlobalTheory.HalfAverage
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.symplectic_restriction_isotropic_part_eq_pairing : ∀ (D : D7) (V V' W : HSp D) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), IsIsoSplit V V' C B → ∀ K : Matrix (Fin r) (Fin V.rank) D.host.E, K * C = 1 → ∀ a t : Mx D W.rank r, symplO V W (restEmb V W K t) (isoPart V W C a) = halfSympl W a t := by
  first | exact @GlobalTheory.HalfAverage.sympl_restEmb_isoPart | exact GlobalTheory.HalfAverage.sympl_restEmb_isoPart | (intros; apply GlobalTheory.HalfAverage.sympl_restEmb_isoPart <;> assumption)
