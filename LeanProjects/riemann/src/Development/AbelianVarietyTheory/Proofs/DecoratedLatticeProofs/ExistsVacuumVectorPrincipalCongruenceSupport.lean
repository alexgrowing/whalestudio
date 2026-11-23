import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PrinInf
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSmallPrincipalCongruenceLiftVectorStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DefiniteStepSmallVectorFockVacuumSphericalStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PrincipalCongruenceFixesDefiniteStepVectorStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SmallVectorCoefficientVanishesOffPrincipalLevelStatement
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SkewGramHalfModule
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HeckeLPartialContinuationHolds
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec)
open GlobalTheory.Mem.Th (CptF)
open GlobalTheory.Core.Rk.IP
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.Exh GlobalTheory.RegSW

namespace GlobalTheory.Core.Rk.Small

theorem exists_small_vac_vec : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (A H : HSp D) (χA : (AE D)ˣ →* Circle) (om : WRep A H) (sA : RealMat A) (sH : RealMat H), IsInfFam θ → (∃ η, GlobalTheory.WeilParts.IsEtaTilde D η) → IsWeilDatumO ψ A H χA 1 om → (∀ τ, IsCartanInv (gramAt D A τ) (sA τ)) → (∀ τ, IsCartanInv (gramAt D H τ) (sH τ)) → A.rank ≤ H.rank → ∀ (β : GL (Fin A.rank) (Formalism.IndefR.Lev.EAf D)) (Z : Finset (Formalism.L2.DIV.Pl D.host.E)), Places A β Z → ∃ f, IsThetaFunO ψ A H f ∧ f ≠ 0 ∧ (∀ τ, IsFockVacAt (heisO ψ A H) θ τ (cplxO (sA τ) (sH τ)) f) ∧ IsSphOff ψ A H (frameLat A) (frameLat H) (under Z) f ∧ (∀ κ ∈ prin A β Z, om (κ, 1) f = f) ∧ ∀ ν 𝓕, IsCovolOne (ratL H A) ν 𝓕 → ∀ g ∈ openOff A (frameLat A) (under Z), g ∉ prinInf A β Z → wcoef om ν 𝓕 f f g = 0 := by
  intro D ψ θ A H χA om sA sH hθ hη hW hA hH hr β Z hZ
  obtain ⟨βH, f₀, f, hfr, hs⟩ := GlobalTheory.T.exists_small_principal_congruence_lift_vector D ψ θ A H χA om sA sH hθ hη hW hA hH hr β Z hZ
  obtain ⟨h1, h2, h3, h4⟩ := GlobalTheory.T.definiteStep_smallVector_fockVacuum_spherical D ψ θ A H χA om sA sH hθ hη hW hA hH hr β Z hZ βH f₀ f hfr hs
  exact ⟨f, h1, h2, h3, h4,
    GlobalTheory.T.principalCongruence_fixes_definiteStepVector D ψ θ A H χA om sA sH hθ hη hW hA hH hr β Z hZ βH f₀ f hfr hs h1,
    GlobalTheory.T.smallVector_coefficient_vanishes_off_principalLevel D ψ θ A H χA om sA sH hθ hη hW hA hH hr β Z hZ βH f₀ f hfr hs h1⟩

end GlobalTheory.Core.Rk.Small
