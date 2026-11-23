import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsFormsVanishingComplexPointsFullJets
import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FRatioSelf
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAffCoverSpec
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_forms_vanishing_complexPoints_fullJets : ∀ (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp ℂ) (d : ℕ) [SmoothOfRelativeDimension d p] (N : ℕ)
    (ι : X ⟶ PSpace ℂ N), IsClosedImmersion ι → ι ≫ PSpace.str ℂ N = p → ∀ S : Finset (CxPts p (RingHom.id ℂ)),
    ∃ (n : ℕ) (h : MvPolynomial (Fin (N + 1)) ℂ) (g : Fin d → MvPolynomial (Fin (N + 1)) ℂ)
      (hh : h ∈ GlobalTheory.ProjSpace.grading ℂ N n) (hg : ∀ j, g j ∈ GlobalTheory.ProjSpace.grading ℂ N n), 0 < n ∧
      (∀ j, genericPoint X ∈ GlobalTheory.EtProj.fOpen ι (g j)) ∧
      (∀ y ∈ S, ∀ j, y ∉ CxPts.ptsIn p (RingHom.id ℂ) (GlobalTheory.EtProj.fOpen ι (g j))) ∧
      (∀ z : CxPts p (RingHom.id ℂ), z ∉ CxPts.ptsIn p (RingHom.id ℂ) (GlobalTheory.EtProj.fOpen ι h) →
        (∀ j, z ∉ CxPts.ptsIn p (RingHom.id ℂ) (GlobalTheory.EtProj.fOpen ι (g j))) → z ∈ S) ∧
      ∀ y ∈ S, ∀ (f₀ : MvPolynomial (Fin (N + 1)) ℂ) (hf₀ : f₀ ∈ GlobalTheory.ProjSpace.grading ℂ N n)
        (hy : y ∈ CxPts.ptsIn p (RingHom.id ℂ) (GlobalTheory.EtProj.fOpen ι f₀)),
        GlobalTheory.EtProj.fRatio ι h f₀ hh hf₀ ∈ RingHom.ker (CxPts.evHom hy) ^ 2 ∧
        RingHom.ker (CxPts.evHom hy) ≤ Ideal.span (Set.range fun j => GlobalTheory.EtProj.fRatio ι (g j) f₀ (hg j) hf₀) ⊔
          RingHom.ker (CxPts.evHom hy) ^ 2 := by
  first | (exact @GlobalTheory.EtProj.Jets.exists_jet_forms) | (exact GlobalTheory.EtProj.Jets.exists_jet_forms) | (intros; apply GlobalTheory.EtProj.Jets.exists_jet_forms  <;> assumption)
