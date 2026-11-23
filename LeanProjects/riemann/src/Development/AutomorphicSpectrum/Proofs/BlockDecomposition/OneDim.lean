import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.VerticalStrips.UnramifiedEulerProductIntegral
import GroundTheory.AutomorphicForms.GL2.GJMatrixLocal

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.GodementSection (localChar adeleAt glAt restrictedTensor2 vecAt awayIntegral awayBox)
open GroundTheory.Automorphic.GJMatrix (cosetInd localTensor localFourierPi localMeasurePi)
open Ad3 Ad3.R
open scoped NumberField.AdeleRing ValuativeRel ENNReal ComplexConjugate SchwartzMap nonZeroDivisors Classical

namespace GlobalTheory.CompanionTheory.RSFT

def oneDim (S : Finset Pl) (g : ∀ v : S, Qv v.1 → ℂ) : Af → ℂ :=
  (awayIntegral S : Set Af).indicator fun x => ∏ v : S, g v (x v.1)

def idl (S : Finset Pl) (N : S → ℤ) : (FractionalIdeal (𝓞 ℚ)⁰ ℚ)ˣ :=
  ∏ᶠ w : Pl, primeIdealUnit w ^ (if h : w ∈ S then N ⟨w, h⟩ else 0)

def sup (S : Finset Pl) (a : ∀ v : S, Qv v.1) : Af := ∑ v : S, finiteAdeleSingleAdd v.1 (a v)

def cE {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (N : ℤ) (a : Fin 2 → F) : (Fin 2 → F) → ℂ :=
  localTensor fun i => cosetInd (valBall F N) (a i)

end GlobalTheory.CompanionTheory.RSFT

end
