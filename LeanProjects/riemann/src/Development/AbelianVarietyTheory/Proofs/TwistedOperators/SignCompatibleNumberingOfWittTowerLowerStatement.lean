import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SignCompatibleNumberingOfWittTowerLower
import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.L2UnitaryRepresentationData
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum
open Formalism.IndefR.Mult (DSModel dualPar parA parB)
open Formalism.MainNotions.SchurIrreducible (AdmGK ARi ARiiiUp ARiiiDown ARiiiLine DiscreteSeriesBlattner admQ5)
open GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction hiding Mat
open GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix (SignCompat plainMat barMat)
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (fockIp)
open GlobalTheory.Chain (signed)
open GlobalTheory.Chain.RealIt (LPol locS locT IsPolyIso)
open MeasureTheory Matrix
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ArchRec
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.signCompatibleNumbering_of_wittTower_lower : ∀ (D : D7) (T T' : HSp D) (i : ℕ) (τ : D.what₂.Tau) (fr : Mn T.rank) (ε : Fin T.rank → Bool) (fr' : Mn T'.rank) (ε' : Fin T'.rank → Bool) (r s : ℕ) (e : Ix r s ≃ Fin T.rank), IsWittLower T T' i → frᴴ * Formalism.REAL.Jm ε * fr = gramAt D T τ → IsUnit fr → fr'ᴴ * Formalism.REAL.Jm ε' * fr' = gramAt D T' τ → IsUnit fr' → SignCompat ε e → i ≤ r ∧ i ≤ s ∧ ∃ e' : Ix (r - i) (s - i) ≃ Fin T'.rank, SignCompat ε' e' := by
  first | exact @GlobalTheory.WittSign.signCompat_of_isWittLower | exact GlobalTheory.WittSign.signCompat_of_isWittLower | (intros; apply GlobalTheory.WittSign.signCompat_of_isWittLower <;> assumption)
