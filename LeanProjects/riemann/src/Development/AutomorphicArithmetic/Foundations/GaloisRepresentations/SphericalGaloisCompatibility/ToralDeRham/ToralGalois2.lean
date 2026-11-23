import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.CyclicStrongAtCusp
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalGaloisCompatibility.ToralDeRham.FrobeniusCharpolyOfUnlinkedUnramifiedSupport
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeilDeligneParamEqUnramifiedSatakeOfFrobeniusStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeaklyAttachedGaloisRepresentationBaseChangeRest
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RestrictsLpDimMono0CharPol
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CharPolEqOfDegNeZero
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.GaloisRestrictionWdCompatible
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemWeilGroupAtPlaceOfFixesExtension
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalGaloisCompatibility.Chl

open GlobalTheory.RoadU

namespace GalTw
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GalCut GlobalTheory.RoadU GlobalTheory.AboveL
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.RoadU

theorem toralGal_of_holds : UpperTheory.Gal.ToralGalois.Inq → SphericalLevelCondition .all .unr → ToralGal := by
  intro hI hS E Ω _ _ _ _ _ _ l _ ι n hn π χ hπ r hr w hl A h σ hσ ξ hξ hsupp hunl a ha
  have key : ∀ g : Weil h, deg g ≠ 0 →
      (wdOf h hl ι r).mono0 ∧ (wdOf h hl ι r).charPol g = ∏ j, (X - C ((ξ j (a g) : ℂˣ) : ℂ)) := by
    intro g hg
    obtain ⟨M, _, _, _, _, _, _, _, u, h', P, χ', hP, hlift, hfix, B, hB, hchar⟩ :=
      GlobalTheory.T.frobenius_charpoly_of_unlinked_unramified_support hI Ω E l ι n hn π χ hπ r hr w A h σ hσ ξ hξ hsupp hunl a ha g hg
    have hl' : ((l : ℕ) : 𝓞 M) ∉ u.asIdeal := by
      intro hm
      apply hl
      rw [← h]
      rw [← h'] at hm
      simpa using hm
    have hr' : Weak P ι (resTo M r) := GlobalTheory.GalCut.weak_comp_res E M Ω l ι n π P hlift r hr
    have hF : UpperTheory.V.Af.FrobEig ι (resTo M r) u (UpperTheory.V.Af.algSat n (normV u) B) :=
      hS M Ω l ι n hn P χ' hP (resTo M r) hr' u trivial B hB hl'
    have hwd : wdOf h' hl' ι (resTo M r) = satWD h' n B :=
      GlobalTheory.T.weilDeligneParam_eq_unramifiedSatake_of_frobenius Ω M l ι n (resTo M r) hr'.1 u hl' A h' B hF
    have hres := GlobalTheory.AboveL.wdOf_restricts E M Ω A w u h h' l ι n r hl hl' hr.1
    obtain ⟨-, hmono, hcp⟩ := GlobalTheory.AboveL.restricts_lpDim_mono0_charPol E M Ω A w u h h' _ _ hres
    let g' : G M Ω := AlgEquiv.ofRingEquiv (f := (g : G E Ω).toRingEquiv) hfix
    have hmem : g' ∈ Weil h' := GlobalTheory.AboveL.mem_weil_of_fix E M Ω A w u h h' g g' fun _ => rfl
    refine ⟨hmono.mp ?_, ?_⟩
    · rw [hwd]
      simp [satWD, WD.lpUnr]
    · rw [← hcp g ⟨g', hmem⟩ fun _ => rfl, hwd]
      exact hchar g ⟨g', hmem⟩ fun _ => rfl
  have hy : ∀ g : Weil h, (WD.mk (WDRep.ofChars h (fun j : Fin n => (ξ j).comp a) fun j => ha.smooth (hξ j))).charPol g =
      ∏ j, (X - C ((ξ j (a g) : ℂˣ) : ℂ)) := by
    intro g
    rw [WD.charPol_mk, WDRep.ofChars_ρ, charpoly_diagEnd]
    rfl
  refine ⟨(key (frob h) (by rw [deg_frob]; exact one_ne_zero)).1, fun g => ?_⟩
  rw [← hy g]
  exact GlobalTheory.AboveL.charPol_eq_of_deg_ne_zero E Ω A w h _ _ (fun g hg => (key g hg).2.trans (hy g).symm) g

end GlobalTheory.RoadU

section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GalCut GlobalTheory.RoadU GlobalTheory.AboveL
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

end
