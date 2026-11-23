import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LevelCharacterPlacesOddAndPrincipalLevel
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RevPosRevPos
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levelCharacter_places_odd_and_principal_level : ∀ (D : D7) (T0 : Type) (L : LevCh D T0) (μ0 : T0), L.Is μ0 → L.Pg.Nonempty ∧ (∀ t PP, PP ∈ L.Pg ∨ PP ∈ L.Q t → (2 : 𝓞 D.host.E) ∉ PP.asIdeal) ∧ ∀ (i : Fin D.R.m) (k : GA D (Wc D i)), k ∈ GfC (Wc D i) → Lev.finE (Wc D i) k ∈ Formalism.L2.DIV.St (L.βW i) → (∀ PP ∈ L.Pg, Formalism.L2.DIV.redFn (L.βW i) PP (Lev.finE (Wc D i) k) = 1) → k ∈ Lev.levG (Wc D i) (L.βW i) (L.datWp i L.triv) ∧ Lev.levChi (Wc D i) (L.βW i) (L.datWp i L.triv) k = 1 := by
  first | exact @GlobalTheory.SpanPlaces.places_level | exact GlobalTheory.SpanPlaces.places_level | (intros; apply GlobalTheory.SpanPlaces.places_level <;> assumption)
