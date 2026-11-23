import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HessRelFnB

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits NumberField IsDedekindDomain TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.CxPts GlobalTheory.ShFam GlobalTheory.Mean4 GlobalTheory.Mean4O
open MeasureTheory GlobalTheory.ChartGlue

namespace GlobalTheory.Mean4O.CoverInt

variable {F : Type} [Field F] [NumberField F] {Y : Var F} {e : ℕ} {M : Man e}

instance measurableSpace (a : Fin (M.n + 1)) : MeasurableSpace (M.X a) := borel _

instance borelSpace (a : Fin (M.n + 1)) : BorelSpace (M.X a) := ⟨rfl⟩

def tChart (I : ManIs M Y) {a : Fin (M.n + 1)} (c : AlgChart Y.str (I.ε a) e) :
    OpenPartialHomeomorph (M.X a) (ReciprocityTheory.L2DbarEstimates.V e) :=
  (I.pt a).transOpenPartialHomeomorph c.e

theorem tChart_apply (I : ManIs M Y) {a : Fin (M.n + 1)} (c : AlgChart Y.str (I.ε a) e) (x : M.X a) :
    tChart I c x = c.e (I.pt a x) := rfl

theorem mem_tChart_source (I : ManIs M Y) {a : Fin (M.n + 1)} (c : AlgChart Y.str (I.ε a) e) {x : M.X a} :
    x ∈ (tChart I c).source ↔ I.pt a x ∈ c.e.source := by
  simp [tChart]

def potDens (I : ManIs M Y) {a : Fin (M.n + 1)} (P : LocPot (M.X a)) (c : AlgChart Y.str (I.ε a) e)
    (x : M.X a) : ℝ :=
  e.factorial / Real.pi ^ e * (ReciprocityTheory.L2DbarEstimates.cHess e
    (fun v => ((2 * P.φ x ((I.pt a).symm (c.e.symm v)) : ℝ) : ℂ)) (c.e (I.pt a x))).det.re

def potMeas (I : ManIs M Y) {a : Fin (M.n + 1)} (P : LocPot (M.X a)) (s : ℤˣ) : Measure (M.X a) :=
  glueMeas (fun c : AlgChart Y.str (I.ε a) e => tChart I c)
    fun c x => ENNReal.ofReal ((s : ℤ) * potDens I P c x)

end GlobalTheory.Mean4O.CoverInt
