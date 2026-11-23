import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.PstIneAt
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.CyclicStrongAtCusp
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalGaloisCompatibility.ToralDeRham.FrobeniusCharpolyOfUnlinkedUnramifiedSupport
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeaklyAttachedGaloisRepresentationBaseChangeRest
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RestrictsLpDimMono0CharPol
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CharPolEqOfDegNeZero
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.GaloisRestrictionWdCompatible
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemWeilGroupAtPlaceOfFixesExtension
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsModelOfMem
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RestrictsWdPst
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsSstAtOfIsCrysAt
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsPstOfIsSst
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CrystallineDecompositionGroupNoMonodromy
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLocCompAndIsLocLoc
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CuspRepSatakeIffLocalComponentSatake
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSphericalOfHasSatGL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AutomorphicFormsFiniteGL
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalGaloisCompatibility.Chl

open GlobalTheory.RoadU

namespace GalTw
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GalCut GlobalTheory.RoadU GlobalTheory.AboveL
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.RoadU

theorem toralAbove_of_holds : UpperTheory.Gal.ToralGalois.Inq → GlobalTheory.RoadU.SphericalLevelCondition .all .crys → GlobalTheory.RoadU.SphericalLevelCondition .all .phi → ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (n : ℕ), 1 ≤ n → ∀ (π : CuspSub E n) (χ : HChar (maximalRealSubfield E)), InScope .all l π χ → ∀ r : G E Ω →* GL (Fin n) (Qbar l), Weak π ι r → ∀ (w : HeightOneSpectrum (𝓞 E)), ((l : ℕ) : 𝓞 E) ∈ w.asIdeal → ∀ (A : ValuationSubring Ω) (h : IsPlaceOver A w) σ, π.IsLocComp w σ → ∀ (ξ : Fin n → ((w.adicCompletion E)ˣ →* ℂˣ)) (hξ : ∀ j, IsSmoothChar (ξ j)), HasSupport (algNorm σ).rep (chars ξ hξ) → Unlinked (chars ξ hξ) → ∀ a : Weil h →* (w.adicCompletion E)ˣ, IsLocalArtin h a → ∀ (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) → ∀ (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω (Dec (F := E) A) O) (hj : GlobalTheory.Pst.Induces Bw), IsPstAt P Bw (r.comp (Dec (F := E) A).subtype) ∧ (wdAt P ι Bw h hj (r.comp (Dec (F := E) A).subtype)).mono0 ∧ ∀ g : Weil h, (wdAt P ι Bw h hj (r.comp (Dec (F := E) A).subtype)).charPol g = ∏ j, (X - C ((ξ j (a g) : ℂˣ) : ℂ)) := by
  intro hI hC hF E Ω _ _ _ _ _ _ l _ ι n hn π χ hπ r hr w hl A h σ hσ ξ hξ hsupp hunl a ha P AI hT O _ _ _ Bw hj
  have key : ∀ g : Weil h, deg g ≠ 0 →
      IsPstAt P Bw (r.comp (Dec (F := E) A).subtype) ∧
      (wdAt P ι Bw h hj (r.comp (Dec (F := E) A).subtype)).mono0 ∧
      (wdAt P ι Bw h hj (r.comp (Dec (F := E) A).subtype)).charPol g = ∏ j, (X - C ((ξ j (a g) : ℂˣ) : ℂ)) := by
    intro g hg
    obtain ⟨M, _, _, _, _, _, _, _, u, h', Q, χ', hQ, hlift, hfix, B, hB, hchar⟩ :=
      GlobalTheory.T.frobenius_charpoly_of_unlinked_unramified_support hI Ω E l ι n hn π χ hπ r hr w A h σ hσ ξ hξ hsupp hunl a ha g hg
    have hr' : Weak Q ι (resTo M r) := GlobalTheory.GalCut.weak_comp_res E M Ω l ι n π Q hlift r hr
    obtain ⟨τ, hτ, -⟩ := GlobalTheory.CuspRep.LocEx.exists_isLocComp GlobalTheory.automorphicFormsFiniteGL M n Q u
    have hsph : IsSpherical τ.ρ :=
      GlobalTheory.TempSatUnr.isSpherical_of_hasSatGL (((GlobalTheory.Cong.satake_locComp M n Q u τ hτ).1 B).1 hB)
    have hcl : ClauseAt .crys Q ι (resTo M r) u := hC M Ω l ι n hn Q χ' hQ (resTo M r) hr' u trivial B hB
    have hph : SphAt .phi Q ι (resTo M r) u B := hF M Ω l ι n hn Q χ' hQ (resTo M r) hr' u trivial B hB
    obtain ⟨LL₀, Bw₀, hjj₀, -, -⟩ := GlobalTheory.AboveLRes.exists_bridge (L := M) Bw hj Bw.LL
    have hj₀ : GlobalTheory.Pst.Induces Bw₀ := fun x => by rw [hjj₀]; exact hj x
    have hc₀ := hcl P AI hT A h' _ Bw₀ hj₀ τ hτ hsph
    have hp₀ : IsPstAt P Bw₀ ((resTo M r).comp (Dec (F := M) A).subtype) :=
      GlobalTheory.GalCut.IwaAll.isPstAt_of_isSstAt P AI hT Bw₀ _
        (GlobalTheory.CrysSst.isSstAt_of_isCrysAt l P AI hT M Ω _ _ Bw₀ n _ hc₀)
    have hpst : IsPstAt P Bw (r.comp (Dec (F := E) A).subtype) :=
      GlobalTheory.AboveLRes.isPstAt_of_resTo E M Ω A l P AI hT n r hr.1 O _ Bw Bw₀ hj hj₀ hp₀
    obtain ⟨O', _, _, _, Bw', hj', -, hres⟩ :=
      GlobalTheory.AboveLRes.wdAt_resTo E M Ω A w u h h' l ι P AI hT n r O Bw hj hpst
    obtain ⟨-, hmono, hcp⟩ := GlobalTheory.AboveL.restricts_lpDim_mono0_charPol E M Ω A w u h h' _ _ hres
    have hc' := hcl P AI hT A h' O' Bw' hj' τ hτ hsph
    let g' : G M Ω := AlgEquiv.ofRingEquiv (f := (g : G E Ω).toRingEquiv) hfix
    have hmem : g' ∈ Weil h' := GlobalTheory.AboveL.mem_weil_of_fix E M Ω A w u h h' g g' fun _ => rfl
    refine ⟨hpst, hmono.mp (GlobalTheory.CrysNoMono.crystalline_decompositionGroup_no_monodromy M Ω l ι n P u A h' O' Bw' hj' _ hc'), ?_⟩
    rw [← hcp g ⟨g', hmem⟩ fun _ => rfl, hph P AI hT A h' O' Bw' hj' ⟨g', hmem⟩]
    exact hchar g ⟨g', hmem⟩ fun _ => rfl
  have hy : ∀ g : Weil h, (WD.mk (WDRep.ofChars h (fun j : Fin n => (ξ j).comp a) fun j => ha.smooth (hξ j))).charPol g =
      ∏ j, (X - C ((ξ j (a g) : ℂˣ) : ℂ)) := by
    intro g
    rw [WD.charPol_mk, WDRep.ofChars_ρ, charpoly_diagEnd]
    rfl
  obtain ⟨hpst, hmono, -⟩ := key (frob h) (by rw [deg_frob]; exact one_ne_zero)
  refine ⟨hpst, hmono, fun g => ?_⟩
  rw [← hy g]
  exact GlobalTheory.AboveL.charPol_eq_of_deg_ne_zero E Ω A w h _ _ (fun g hg => (key g hg).2.2.trans (hy g).symm) g

end GlobalTheory.RoadU
