import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LineSCShortExact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HPolyAddTwo
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne

set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxForm GlobalTheory.Points GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.CovTest GlobalTheory.LineForm

namespace GlobalTheory.FibGlob

variable {k : Type} [CommRing k] {B Y : Scheme.{0}} {q : B ⟶ Sp k} {p : Y ⟶ Sp k} {d : ℕ}

def thetaF (hY : IsRegVar p d) (σ : k →+* ℂ) {E : Y.Modules} {m : VMetric p E 2} (H : m.IsCInf) (fl : Vert.Flag E 2) :
    (hY.atlas σ).Pt → Ev d :=
  c1F hY σ (VMetric.grLB fl 0 H) + omF hY σ m fl

def c1EF (hB : IsRegVar q d) (σ : k →+* ℂ) {E : B.Modules} (m : VMetric q E 2) (fl : Vert.Flag E 2) :
    (hB.atlas σ).Pt → Ev d :=
  fun x => (hB.atlas σ).chern ((m.met σ).gram (frameAt fl x.pt).frame) 1 x

end GlobalTheory.FibGlob
