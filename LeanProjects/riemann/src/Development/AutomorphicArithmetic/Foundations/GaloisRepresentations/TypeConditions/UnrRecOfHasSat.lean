import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.InePolOfUnr
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EventuallyNatCastNotMem
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEquivOfMapEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIrreducibleFixed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSubquotSmIndCongr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalLanglandsGaloisCompat

noncomputable section

namespace UpperTheory.GalS

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial Formalism.L2.Host
open GlobalTheory GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.Pst GlobalTheory.GalOfCusp GlobalTheory.HeightCounting GlobalTheory.SmGL

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

variable {E Ω : Type} [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {l : ℕ} [Fact l.Prime] {a : ℕ}
  {π : CuspSub E a} {χ : HChar (maximalRealSubfield E)} {ι : Qbar l ≃+* ℂ} {r : G E Ω →* GL (Fin a) (Qbar l)} {wt : ℤ}
  {HT : (E →+* Qbar l) → Multiset ℤ} {w : HeightOneSpectrum (𝓞 E)} {A : ValuationSubring Ω}

theorem IsGalU.aw_locPar (hL : GlobalTheory.Published.LocalLanglandsGL) (hF : GlobalTheory.Published.AutomorphicFormsFiniteGL)
    (H : IsGalU π χ ι r wt HT) (hl : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal) (h : IsPlaceOver A w) :
    Aw (wdOf h hl ι r) ((ParLaws.locPar hL (CG.mk π) h).lpTw ((1 - (a : ℝ)) / 2)) := by
  obtain ⟨σ, hσ, -⟩ := LocEx.exists_isLocComp hF E a π w
  rw [ParLaws.locPar_mk hL hσ h]
  exact H.aw hl (ParLaws.isRec_locRec hL h) hσ

omit [IsCMField E] in
theorem Aw.eq_unr {h : IsPlaceOver A w} {x y : WD h} (k : Aw x y) (hy : y.unr) : x = y := k.unr hy

theorem IsGalU.eq_locPar (hL : GlobalTheory.Published.LocalLanglandsGL) (hF : GlobalTheory.Published.AutomorphicFormsFiniteGL)
    (H : IsGalU π χ ι r wt HT) (hl : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal) (h : IsPlaceOver A w)
    (hu : (ParLaws.locPar hL (CG.mk π) h).unr) :
    wdOf h hl ι r = (ParLaws.locPar hL (CG.mk π) h).lpTw ((1 - (a : ℝ)) / 2) :=
  (H.aw_locPar hL hF hl h).eq_unr ((WD.unr_tw _ _).2 hu)

omit [IsCMField E] in

theorem unr_rec_of_hasSat {h : IsPlaceOver A w} {rc : IrrGL (w.adicCompletion E) → WD h} (hrc : IsRec h rc)
    (σ : SmIrr (GL (Fin a) (w.adicCompletion E))) (S : Multiset ℂˣ) (hS : GlobalTheory.LFun.HasSatGL w σ.ρ S) :
    (rc (IrrGL.of σ.ρ σ.smooth σ.irred)).unr := by
  obtain ⟨α, rfl, hα⟩ := (GlobalTheory.LGrp.SatakeCompare.hasSatakeGL_iff _ _ _ σ.ρ S).1
    (GlobalTheory.LFun.SatCompare.hasSatakeGL_iff.2 ⟨⟨σ.smooth, σ.irred⟩, hS⟩)
  have e := ParLaws.rec_eq_diag hrc (σ := ParLaws.toRep σ) hα
  have e' : rc (IrrGL.of σ.ρ σ.smooth σ.irred) = WD.mk (WDRep.diag h fun i => (α i)⁻¹) := e
  rw [e', WD.unr_mk]
  exact WDRep.unr_diag _

theorem exists_aw (hL : GlobalTheory.Published.LocalLanglandsGL) (hF : GlobalTheory.Published.AutomorphicFormsFiniteGL)
    (hG : CuspU) {E : Type} (Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω]
    [Algebra E Ω] [IsAlgClosure E Ω] {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) {a : ℕ} (ha : 1 ≤ a) (π : CG E a)
    (hc : π.IsCsd) (hr : π.IsRegAlg) :
    ∃ r : G E Ω →* GL (Fin a) (Qbar l), Continuous (fun g => (r g : Matrix (Fin a) (Fin a) (Qbar l))) ∧ IsSSRep r ∧
      ∀ (w : HeightOneSpectrum (𝓞 E)) (hl : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal) (A : ValuationSubring Ω) (h : IsPlaceOver A w),
        Aw (wdOf h hl ι r) ((ParLaws.locPar hL π h).lpTw ((1 - (a : ℝ)) / 2)) := by
  induction π using Quotient.inductionOn with | _ π =>
  obtain ⟨r, wt, HT, H⟩ := hG.of_isCsd Ω ι ha (π := π) hr hc
  exact ⟨r, Units.continuous_val.comp H.cont, H.ss, fun w hl A h => H.aw_locPar hL hF hl h⟩

theorem nice_of_locPar (hL : GlobalTheory.Published.LocalLanglandsGL) (hF : GlobalTheory.Published.AutomorphicFormsFiniteGL) (h : IsPlaceOver A w)
    (k : NcW ((ParLaws.locPar hL (CG.mk π) h).lpTw ((1 - (a : ℝ)) / 2))) : Nice π h := by
  obtain ⟨σ, hσ, -⟩ := LocEx.exists_isLocComp hF E a π w
  refine ⟨σ, hσ, _, ParLaws.isRec_locRec hL h, ?_⟩
  rw [rec_algNorm (ParLaws.isRec_locRec hL h) σ]
  rwa [ParLaws.locPar_mk hL hσ h] at k

theorem nice_of_spherical {h : IsPlaceOver A w} {rc : IrrGL (w.adicCompletion E) → WD h} (hrc : IsRec h rc)
    {σ : SmIrr (GL (Fin a) (w.adicCompletion E))} (hσ : π.IsLocComp w σ) (hs : SmGL.IsSpherical σ.ρ) : Nice π h := by
  refine ⟨σ, hσ, rc, hrc, NcW.of_unr ?_⟩
  rw [rec_algNorm hrc, WD.unr_tw]
  exact (ParLaws.unr_iff hrc (ParLaws.toRep σ)).2 hs

end UpperTheory.GalS
