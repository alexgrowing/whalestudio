import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.KFiniteThetaLifts.RationalPrimesBelowPlaces
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnfoldingMirabolicCosetsStatement

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3
open Ad3.R (G2 Jd md Dt KA Set0 Coord LInv pt dia2 pri)
open scoped NumberField.AdeleRing ENNReal

namespace GlobalTheory.CompanionTheory.UnfoldingAlt

def dl2 : GL (Fin 2) ℚ := dg2 1 (-1)

def dl3 : GL (Fin 3) ℚ := dg 1 (-1) 1

def tr (W : G3 → ℂ) (g : G3) : ℂ := dualWhittakerAdelicGL3 W (dia dl3 * g)

def trL : (G3 → ℂ) →ₗ[ℂ] (G3 → ℂ) where
  toFun := tr
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def tV (V : Submodule ℂ (G3 → ℂ)) : Submodule ℂ (G3 → ℂ) := V.map trL

def cstD (Cst : G2 → ℂ) (h : G2) : ℂ := Cst (w2 * ti h)

def wtD (Wt : G2 → ℂ) (h : G2) : ℂ := dualWhittakerAdelic Wt (dia2 dl2 * h)

end GlobalTheory.CompanionTheory.UnfoldingAlt
