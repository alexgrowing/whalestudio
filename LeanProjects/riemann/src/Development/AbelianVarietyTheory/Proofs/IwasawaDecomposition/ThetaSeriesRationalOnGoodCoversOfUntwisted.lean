import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SeriesRatSOf
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.TwistSeries
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RationalFormsDetTwistMulRationalStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaWeilTwist

set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links
  Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels GlobalTheory.SerRatRay
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SerStdTwist

theorem seriesRatS_of_untwRatS (hRF : GlobalTheory.Published.RayClassFieldSt) (hU : GlobalTheory.SerStd.UntwRatS) : GlobalTheory.SerStd.SeriesRatS := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ hL hIs hG hFam hMod hThP hTie i hV hFP hstd gramR c0R c0L hFT u hu
  obtain ⟨ph, hph, hU'⟩ := hU D G Pl0 T0 A T R F κ v₀ hL hIs hG hFam hMod hThP hTie i hV hFP hstd gramR c0R c0L hFT u hu
  refine ⟨ph, hph, fun C hC s hs f hf w hw => ⟨hU' C hC s hs f hf w hw, fun δ δc hδ => ⟨fun dd hdd => ?_, fun om hom => ?_⟩⟩⟩
  · have := GlobalTheory.T.rationalForms_detTwist_mul_rational hRF D G Pl0 T0 A T R F κ v₀ hL hIs hG hFam hMod hThP hTie i hV hFP gramR c0R c0L hFT u hu C hC δ δc hδ dd
      (Or.inl hdd) _ (hU' C hC s hs f hf w hw)
    simpa [mul_assoc] using this
  · obtain ⟨c, hc, dd, hdd, heq⟩ :=
      GlobalTheory.WeilTwistSeries.theta_weil_twist D G Pl0 T0 A T R F κ v₀ hL hIs hG hFam hMod hThP hTie i hV hFP gramR c0R c0L hFT u hu C hC δ δc hδ om hom s hs
        f hf w hw
    have h1 := GlobalTheory.T.rationalForms_detTwist_mul_rational hRF D G Pl0 T0 A T R F κ v₀ hL hIs hG hFam hMod hThP hTie i hV hFP gramR c0R c0L hFT u hu C hC δ δc
      hδ dd hdd _ (hU' C hC s hs f hf w hw)
    have h2 := isRat_const_mul T i hV C (κ i) _ c h1 hc
    convert h2 using 2 with g
    rw [heq g]; ring

end GlobalTheory.SerStdTwist
