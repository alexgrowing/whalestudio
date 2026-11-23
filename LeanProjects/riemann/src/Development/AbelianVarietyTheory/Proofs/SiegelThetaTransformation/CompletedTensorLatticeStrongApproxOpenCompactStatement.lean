import Mathlib
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.CompletedTensorLatticeStrongApproxOpenCompact
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsWeakOfDatum
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsHeatZero
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker
open GlobalTheory.SW hiding Level
open GlobalTheory.Dict (hx pv)
open ReciprocityTheory.ChartRestriction.G.I2 (polyDeriv)
open scoped TensorProduct ComplexConjugate Real Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.completedTensorLattice_strongApprox_open_compact : ∀ (D : D7) (S T : HSp D) (C : Ctx S T), ∀ (Λ : Lt D.host.E S.rank) (L : Lt D.host.E T.rank), (Λ.FG ∧ Submodule.span D.host.E (Λ : Set (Fin S.rank → D.host.E)) = ⊤) → (L.FG ∧ Submodule.span D.host.E (L : Set (Fin T.rank → D.host.E)) = ⊤) → (∀ u, IsFinPt u → ∃ y : Matrix (Fin S.rank) (Fin T.rank) D.host.E, u - finW S T y ∈ hatA S T (tens Λ L)) ∧ (∀ y : Matrix (Fin S.rank) (Fin T.rank) D.host.E, finW S T y ∈ hatA S T (tens Λ L) ↔ y ∈ tens Λ L) ∧ (∀ u ∈ hatA S T (tens Λ L), IsFinPt u ∧ ∀ N : ℕ, 0 < N → ∃ y ∈ tens Λ L, ∃ u' ∈ hatA S T (tens Λ L), u = finW S T y + N • u') ∧ (∀ U : AddSubgroup (WO S T), IsOpen (U : Set (WO S T)) → ∃ N : ℕ, 0 < N ∧ ∀ u ∈ hatA S T (tens Λ L), N • u ∈ U) ∧ (∀ N : ℕ, 0 < N → IsOpen {w : WO S T | ∃ u ∈ hatA S T (tens Λ L), IsRealPt (w - N • u)}) ∧ IsCompact (hatA S T (tens Λ L) : Set (WO S T)) := by
  first | exact @GlobalTheory.Ker.HatLat.hatA_tens | exact GlobalTheory.Ker.HatLat.hatA_tens | (intros; apply GlobalTheory.Ker.HatLat.hatA_tens <;> assumption)
