import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegularSectionOpenCover
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitKOfIsAlgClosed
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj
open GlobalTheory GlobalTheory.ArInt GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.Mean4O GlobalTheory.LineNorm GlobalTheory.CoverNorm GlobalTheory.VertForm GlobalTheory.HtGen
open Formalism.MainNotions.DIV.Cons (intO)
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.regular_section_open_cover : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (L : HermLB p) (R : L.B.ι → X.functionFieldˣ), IsRatSec L.B R → ∀ (l n : ℕ) (U : X → X.Opens) (s : X → Fin n → X.functionField), (∀ x, x ∈ U x) → (∀ (x : X) (i : L.B.ι) (x₀ : X), x₀ ∈ U x → x₀ ∈ L.B.U i → (l : k) ∈ (p x₀).asIdeal → (∀ J, RegAt x₀ (s x J * R i)) ∧ (∃ J, UnitAt x₀ (s x J * R i)) ∧ ∀ x', x₀ ∈ U x' → ∀ J, ¬ UnitAt x₀ ((s x J - s x' J) * R i)) → NefOver L l := by
  first | exact @GlobalTheory.HtGenCurve.nefOver_of_localGen | exact GlobalTheory.HtGenCurve.nefOver_of_localGen | (intros; apply GlobalTheory.HtGenCurve.nefOver_of_localGen <;> assumption)
