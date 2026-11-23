import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.StdBases
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.BeData
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsConstantCoeffOne
import Formalism.LocalRingCardinality.CoeNeZeroOfNotMem
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SubstUnitaryLogarithmicCoordinatesStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnitaryMatrixOfOrthonormalLocalBasisAllPlacesStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExponentShapeOfIntegralClassOneLetterStatement
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric GlobalTheory.KerStd Classical
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.Th1.D (F1 F2 OwOK TrDual phFF)
open Formalism.InvariantFactorPaths.G7 (UnrOK IsLawOfLog cob)

namespace GlobalTheory.KerStd

theorem nP_eq_one_of_hP_eq_zero (D : D7) (p : ℕ) (hC : IsResidueClassZero D p) (h0 : hP D p = 0) : nP D p = 1 := by
  have hS : ¬ IsSg D p := by
    intro hs
    unfold IsResidueClassZero at hC
    unfold IsSg at hs
    rw [hC] at hs
    exact absurd hs (by decide)
  unfold nP
  rw [if_neg hS, h0, addOrderOf_zero]

theorem thetaExpansionRealPlaces_stdSer_of_adm : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Formalism.L2.Ker.Base D cc δ) (χ : IdE D → ℂ) (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]), HostAt B χ p lam → 5 ≤ p → IsResidueClassZero D p → hP D p = 0 → ∀ (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) (P : D.what₂.Tau → Matrix (Fin N) (Fin N) D.host.E) (P' : D.what₂.Tau → Matrix (Fin N') (Fin N') D.host.E), admitted D N N' L L' → StdBases D lam L P → StdBases D lam L' P' → ∀ G, IsComb D B.tor (B.eNat χ) lam L L' G → OrbitPlaces.ThetaExpansionRealPlaces D p (stdSer D lam (fun _ => 1) P P' G) := by
  intro D cc δ B χ p _ lam hHost h5 hC hP0 N N' L L' P P' hAdm hS hS' G hG
  obtain ⟨c, g2, g3, s2, ε, σ, F, hc, hcd, hfam⟩ := hHost
  obtain ⟨r, b, hLB, hON, hInt⟩ := hfam N N' L L' hAdm
  obtain ⟨γ, hγ1, hγ2, hγ3⟩ := GlobalTheory.T.unitaryMatrix_of_orthonormal_localBasis_allPlaces D p lam σ hcd.2.2.2.2.2.1 h5 hC hP0 N N' L L' P P' hAdm hS hS' r b hLB hON
  have hU := GlobalTheory.T.subst_unitary_logarithmic_coordinates p g2 g3 s2 ε σ F hcd (Fin r) (OrbitPlaces.Pl D × Fin N × Fin N') γ hγ1 (by convert hγ2) _ (hInt G hG)
  rw [← hγ3 c G] at hU
  exact GlobalTheory.T.exponentShape_of_integralClass_oneLetter D p g2 g3 s2 ε σ F hcd (nP_eq_one_of_hP_eq_zero D p hC hP0) N N' c _ hc hU

end GlobalTheory.KerStd
