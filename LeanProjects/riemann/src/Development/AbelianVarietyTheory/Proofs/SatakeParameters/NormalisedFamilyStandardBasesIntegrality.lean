import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.StdBases
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.BeData
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsConstantCoeffOne
import Formalism.LocalRingCardinality.CoeNeZeroOfNotMem
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsOfInertPrimeEllipticCurveLocalDataStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.StandardBasesHyperbolicPairOrthonormalStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.OrbitIdentityAllOfIntegralClassHostLogStatement

noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric GlobalTheory.KerStd Classical
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.Th1.D (F1 F2 OwOK TrDual phFF)
open Formalism.InvariantFactorPaths.G7 (UnrOK IsLawOfLog cob)

namespace GlobalTheory.KerStd

theorem normalisedFamily_standardBases_integrality : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Formalism.L2.Ker.Base D cc δ) (χ : IdE D → ℂ) (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]), HostAt B χ p lam → OrbitPlaces.OrbOK D p → ((IsResidueClassZero D p ∧ hP D p ≠ 0) ∨ IsSg D p) → ∃ (ep : ℂ_[p]) (be : MvPowerSeries (ZMod (nP D p)) ℂ_[p]), ‖ep‖ = 1 ∧ BeStd p (nP D p) be ∧ ∀ (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) (P : D.what₂.Tau → Matrix (Fin N) (Fin N) D.host.E) (P' : D.what₂.Tau → Matrix (Fin N') (Fin N') D.host.E), admitted D N N' L L' → StdBases D lam L P → StdBases D lam L' P' → ∀ G, IsComb D B.tor (B.eNat χ) lam L L' G → ∀ R, OrbitPlaces.IsReps D p R → OrbitPlaces.ThetaExpansionAllPlaces D p R ep (fun _ => -1) (fun _ => be) (stdSer D lam (fun _ => 1) P P' G) := by
  intro D cc δ B χ p _ lam hA hO hCS
  obtain ⟨c, g2, g3, s2, ε, σ, F, hc, hCD, hH⟩ := hA
  obtain ⟨om, oms, ζ, hBD⟩ := GlobalTheory.T.exists_of_inertPrimeEllipticCurveLocalData p g2 g3 s2 ε σ F hCD (nP D p) hO.even
  refine ⟨c, beOf p (nP D p) σ (cob F (phFF p g2 g3 s2 ε)) om oms ζ, hc,
    ⟨σ, F, cob F (phFF p g2 g3 s2 ε), om, oms, ζ, hBD, rfl⟩, ?_⟩
  intro N N' L L' P P' hAdm hP hP' G hG R hR
  obtain ⟨r, b, hb, ho, hint⟩ := hH N N' L L' hAdm
  obtain ⟨f, f', hf, heq⟩ := GlobalTheory.T.standardSeries_scaled_eq_orthonormalSeries_hyperbolicSubst D p lam σ hCD.2.2.2.2.2.1 hO hCS om oms hBD.2.2.2.2.1 hBD.2.2.2.2.2.1
    R hR N N' L L' P P' hAdm hP hP' r b hb ho
  exact GlobalTheory.T.orbitIdentity_all_of_integralClass_hostLog_alt D p g2 g3 s2 ε σ F hCD hO om oms ζ hBD R hR N N' r f f' hf (thOrth D lam c b G) (hint G hG) c
    (stdSer D lam (fun _ => 1) P P' G) (heq c G)

end GlobalTheory.KerStd
