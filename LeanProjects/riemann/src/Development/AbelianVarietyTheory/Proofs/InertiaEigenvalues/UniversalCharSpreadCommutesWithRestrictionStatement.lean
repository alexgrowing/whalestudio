import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UniversalCharSpreadCommutesWithRestriction
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsIsScalar
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GaloisSideTwistedSelmerAuxiliaryPrimes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.universalChar_spread_commutes_with_restriction : ∀ (D : D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (Y : NExp D.R D.host D.what₂ D.LL0 N X), GlobalTheory.UnivChar.IsUnivChar Y → ∀ (i : X.Tw) (M : ℕ) (ch : Set (Pl D.host.E)), IsChoice ch → ∀ (Q Q' : Finset (Pl D.host.E)) (hQQ : Q' ⊆ Q), admissibleConjugatePairPlaces X i Q M = Q → admissibleConjugatePairPlaces X i Q' M = Q' → ∀ (hsub : ∀ w ∈ half ch (admissibleConjugatePairPlaces X i Q' M), w ∈ half ch (admissibleConjugatePairPlaces X i Q M)) (c : ↥(half ch (admissibleConjugatePairPlaces X i Q M)) → ZMod (X.l i ^ M)) (v : Pl D.host.E) (hv : v ∈ Q'), spread Y i Q M ch c ⟨v, hQQ hv⟩ = spread Y i Q' M ch (fun w => c ⟨w.1, hsub w.1 w.2⟩) ⟨v, hv⟩ := by
  first | exact @GlobalTheory.SpreadRestrict.spread_restrict | exact GlobalTheory.SpreadRestrict.spread_restrict | (intros; apply GlobalTheory.SpreadRestrict.spread_restrict <;> assumption)
