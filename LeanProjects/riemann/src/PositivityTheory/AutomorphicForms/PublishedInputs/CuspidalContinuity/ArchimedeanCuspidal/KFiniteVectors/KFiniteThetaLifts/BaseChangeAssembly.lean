import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.KFiniteThetaLifts.RationalPrimesBelowPlaces
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.VerticalStrips.UnramifiedEulerProductIntegral

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.GodementSection (localChar)
open Ad3.R (G2 Jd md KA Set0 Coord LInv)
open scoped NumberField.AdeleRing ValuativeRel

namespace Ad3.K.QuadraticBaseChangeGL3

variable (K : Type) [Field K] [NumberField K]

def EULH : Prop := ∀ (DK : DatK K) (c : HeckeCharacter K) (S : Finset (PlK K)), DifferentiableOn ℂ (eulK DK c S) {s | 1 < s.re}

def TILI : Prop := Continuous (ti : G3 → G3) ∧ Continuous (ti : G2 → G2) ∧
  (∀ φ : G3 → ℂ, IsLeftInvariant φ → IsLeftInvariant (fun g => φ (ti g))) ∧
  (∀ θ : G2 → ℂ, LInv θ → LInv (fun h => θ (ti h))) ∧ ∀ h : G2, e3A (ti h) = ti (e3A h)

def BaseChangeAssembly : Prop := BCEX K → BCOF K → RationalPrimesBelowPlaces K → REGRP K → SphericalWhittakerAtOne → SPH K → CasselmanShalikaGL3GL2 K → TEST K → HOLV K → LFEV K → GLUE K →
  TSH → GAMB → THETA K → DEC → ENT → GFE → UNF → FAC K → EULH K → TILI →
  GL2LocalData.LocalFunctionalEquationFinite → GL2LocalData.WeilJLF → GL2LocalData.WeilJLS → GL2LocalData.LocalFunctionalEquationReal → R.G0 → R.G2a → Out2 K

end Ad3.K.QuadraticBaseChangeGL3
