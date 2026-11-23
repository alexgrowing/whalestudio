import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.UnrRecOfHasSat
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.WeightsConj
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RecAlgNorm
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.EventuallyUnr
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRecTLocRecT

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace UpperTheory.GalS
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial Formalism.L2.Host
open GlobalTheory GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.Pst GlobalTheory.GalOfCusp GlobalTheory.HeightCounting GlobalTheory.SmGL
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
variable {E Ω : Type} [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {l : ℕ} [Fact l.Prime] {a : ℕ}
  {π : CuspSub E a} {χ : HChar (maximalRealSubfield E)} {ι : Qbar l ≃+* ℂ} {r : G E Ω →* GL (Fin a) (Qbar l)} {wt : ℤ}
  {HT : (E →+* Qbar l) → Multiset ℤ} {w : HeightOneSpectrum (𝓞 E)} {A : ValuationSubring Ω}
theorem IsGalUAlt.aw_locPar (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (hF : GlobalTheory.Published.AutomorphicFormsFiniteGL)
    (H : _root_.UpperTheory.GalS.IsGalUAlt π χ ι r wt HT) (hl : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal) (h : IsPlaceOver A w) :
    Aw (wdOf h hl ι r) ((_root_.GlobalTheory.CuspRep.ParLawsT.locParT hL (CG.mk π) h).lpTw ((1 - (a : ℝ)) / 2)) := by
  obtain ⟨σ, hσ, -⟩ := LocEx.exists_isLocComp hF E a π w
  rw [_root_.GlobalTheory.CuspRep.ParLaws.local_parameter_eq_reciprocity_of_is_local_component hL hσ h]
  exact H.aw hl (_root_.GlobalTheory.CuspRep.ParLawsT.isRecT_locRecT hL h) hσ
theorem IsGalUAlt.eq_locPar (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (hF : GlobalTheory.Published.AutomorphicFormsFiniteGL)
    (H : _root_.UpperTheory.GalS.IsGalUAlt π χ ι r wt HT) (hl : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal) (h : IsPlaceOver A w)
    (hu : (_root_.GlobalTheory.CuspRep.ParLawsT.locParT hL (CG.mk π) h).unr) :
    wdOf h hl ι r = (_root_.GlobalTheory.CuspRep.ParLawsT.locParT hL (CG.mk π) h).lpTw ((1 - (a : ℝ)) / 2) :=
  (H.aw_locPar hL hF hl h).eq_unr ((WD.unr_tw _ _).2 hu)
omit [IsCMField E] in
theorem unr_rec_of_has_sat {h : IsPlaceOver A w} {rc : IrrGL (w.adicCompletion E) → WD h} (hrc : _root_.UpperTheory.Zero.LLC.IsRecT h rc)
    (σ : SmIrr (GL (Fin a) (w.adicCompletion E))) (S : Multiset ℂˣ) (hS : GlobalTheory.LFun.HasSatGL w σ.ρ S) :
    (rc (IrrGL.of σ.ρ σ.smooth σ.irred)).unr := by
  obtain ⟨α, rfl, hα⟩ := (GlobalTheory.LGrp.SatakeCompare.hasSatakeGL_iff _ _ _ σ.ρ S).1
    (GlobalTheory.LFun.SatCompare.hasSatakeGL_iff.2 ⟨⟨σ.smooth, σ.irred⟩, hS⟩)
  have e := _root_.GlobalTheory.CuspRep.ParLaws.reciprocity_eq_diagonal_inv_of_has_satake hrc (σ := ParLaws.toRep σ) hα
  have e' : rc (IrrGL.of σ.ρ σ.smooth σ.irred) = WD.mk (WDRep.diag h fun i => (α i)⁻¹) := e
  rw [e', WD.unr_mk]
  exact WDRep.unr_diag _
theorem exists_aw_alt (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (hF : GlobalTheory.Published.AutomorphicFormsFiniteGL)
    (hG : _root_.UpperTheory.GalS.CuspUAlt) {E : Type} (Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω]
    [Algebra E Ω] [IsAlgClosure E Ω] {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) {a : ℕ} (ha : 1 ≤ a) (π : CG E a)
    (hc : π.IsCsd) (hr : π.IsRegAlg) :
    ∃ r : G E Ω →* GL (Fin a) (Qbar l), Continuous (fun g => (r g : Matrix (Fin a) (Fin a) (Qbar l))) ∧ IsSSRep r ∧
      ∀ (w : HeightOneSpectrum (𝓞 E)) (hl : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal) (A : ValuationSubring Ω) (h : IsPlaceOver A w),
        Aw (wdOf h hl ι r) ((_root_.GlobalTheory.CuspRep.ParLawsT.locParT hL π h).lpTw ((1 - (a : ℝ)) / 2)) := by
  induction π using Quotient.inductionOn with | _ π =>
  obtain ⟨r, wt, HT, H⟩ := hG.of_isCsd Ω ι ha (π := π) hr hc
  exact ⟨r, Units.continuous_val.comp H.cont, H.ss, fun w hl A h => H.aw_locPar hL hF hl h⟩
theorem nice_of_loc_par (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (hF : GlobalTheory.Published.AutomorphicFormsFiniteGL) (h : IsPlaceOver A w)
    (k : NcW ((_root_.GlobalTheory.CuspRep.ParLawsT.locParT hL (CG.mk π) h).lpTw ((1 - (a : ℝ)) / 2))) : _root_.UpperTheory.GalS.NiceAlt π h := by
  obtain ⟨σ, hσ, -⟩ := LocEx.exists_isLocComp hF E a π w
  refine ⟨σ, hσ, _, _root_.GlobalTheory.CuspRep.ParLawsT.isRecT_locRecT hL h, ?_⟩
  rw [_root_.GlobalTheory.GalOfCusp.rec_algNorm_alt (_root_.GlobalTheory.CuspRep.ParLawsT.isRecT_locRecT hL h) σ]
  rwa [_root_.GlobalTheory.CuspRep.ParLaws.local_parameter_eq_reciprocity_of_is_local_component hL hσ h] at k
theorem nice_of_spherical' {h : IsPlaceOver A w} {rc : IrrGL (w.adicCompletion E) → WD h} (hrc : _root_.UpperTheory.Zero.LLC.IsRecT h rc)
    {σ : SmIrr (GL (Fin a) (w.adicCompletion E))} (hσ : π.IsLocComp w σ) (hs : SmGL.IsSpherical σ.ρ) : _root_.UpperTheory.GalS.NiceAlt π h := by
  refine ⟨σ, hσ, rc, hrc, NcW.of_unr ?_⟩
  rw [_root_.GlobalTheory.GalOfCusp.rec_algNorm_alt hrc, WD.unr_tw]
  exact (_root_.GlobalTheory.CuspRep.ParLaws.reciprocity_unramified_iff_spherical hrc (ParLaws.toRep σ)).2 hs
end UpperTheory.GalS
end
end
