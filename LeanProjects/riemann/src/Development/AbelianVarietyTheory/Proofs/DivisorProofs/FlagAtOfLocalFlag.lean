import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormsAtOfNorms
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsLinearMapMultilinearMapBaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowOfFramesTriv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoverMapGenericPointSpecializesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoverMorphismGenericPointSpecializesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FramesModPGenericOpenStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallSectionUnitsGenericOpenStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModpFramesPullbackStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModpFramesPowerSectionsLiftStatement
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj GlobalTheory GlobalTheory.Cartier GlobalTheory.CechPic GlobalTheory.ArInt GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.CoverNorm GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.VertForm GlobalTheory.TrivFlag GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.TrueCx
open scoped Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FrameGlue

theorem flagAt_of_locFlag : ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (C : CxSt F) (N : ℕ) (A : Fin N → Adl C Y) (p : ℕ), p.Prime → LocFlag A p → FlagAt A p := by
  intro F _ _ Y C N A p hp hloc
  obtain ⟨V, W, ι, U, M, c, hW, hcov, hM, hunit, htest⟩ := hloc
  have hη := GlobalTheory.T.cover_map_generic_point_specializes F Y V
  obtain ⟨c', hc', hfr⟩ := GlobalTheory.T.frames_mod_p_generic_open F Y C N A p hp V hη W ι U M c hW hcov hM hunit htest
  refine ⟨V, fun V' π _ hlies L hL m hN Z _ ιZ hpZ => ?_⟩
  have hπ := GlobalTheory.T.cover_morphism_generic_point_specializes F Y V V' π hlies
  exact GlobalTheory.T.modp_frames_power_sections_lift V'.X p ι N (fun a => π ⁻¹ᵁ U a) _ _ (GlobalTheory.T.modp_frames_pullback V.X V'.X π hπ p ι N U M c' hfr) L hL m
    (fun i => GlobalTheory.T.small_section_units_generic_open F Y C (A i) p hp V hη W ι U (fun a => c a i) (fun a => c' a i) hW (fun a => hc' a i)
      (fun a z hz => hunit a i z hz) (fun v hv e y hy z yt h1 h2 a ha => (htest v hv e y hy z yt h1 h2 a ha).1 i)
      V' π hπ hlies (L i) m (hN i)) Z ιZ hpZ

end GlobalTheory.FrameGlue

end
