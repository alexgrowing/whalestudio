import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.KFiniteThetaLifts.PureThetaTransfer.ConstantTermModerateGrowth

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open Ad3.R (G2 Jd md KA LInv pri dia2 pt)
open scoped NumberField.AdeleRing ValuativeRel

namespace Ad3.K.QuadraticBaseChangeGL3.Th

variable {K : Type} [Field K] [NumberField K]

variable (K) in

def FourierExpansionCentral : Prop := Module.finrank ℚ K = 2 → IsTotallyComplex K → ∀ (DK : DatK K) c n t S, AdmK DK c n t S →
  ∀ M : ∀ v : Pl, LM c v, AdmM M → ∃ (R : Finset (Pl →₀ ℤ)) (Sv : Finset Pl) (κ₀ : ℂ), κ₀ ≠ 0 ∧ (∀ g ∈ Gp M,
    HasSum (fun α : ℚˣ => κ₀ * WM n t M (dg2 (pri α) 1 * g)) (thA R Sv n t M g - th0 R Sv n t M g) ∧
    (∀ x : 𝔸[ℚ], th0 R Sv n t M (uni2 x * g) = th0 R Sv n t M g) ∧
    (∀ κ : Kˣ, th0 R Sv n t M (dg2 (pri (Units.map (Algebra.norm ℚ : K →* ℚ) κ)) 1 * g) = th0 R Sv n t M g)) ∧
    ∀ z : Jd, ∃ u : ℂ, ‖u‖ = 1 ∧ (∀ g, WM n t M (dg2 z z * g) = u * WM n t M g) ∧
      ∀ g ∈ Gp M, th0 R Sv n t M (dg2 z z * g) = u * th0 R Sv n t M g

variable (K) in

def PureTensorAssembly : Prop := MEX K → THS K → AVG K → FourierExpansionCentral K → GPD K → CONTG K → ConstantTermModerateGrowth K → WPSI K → WSUP K → WCONT K →
  WGAU K → WSUM K → REALTH → EXTA → TPURE K

end Ad3.K.QuadraticBaseChangeGL3.Th
