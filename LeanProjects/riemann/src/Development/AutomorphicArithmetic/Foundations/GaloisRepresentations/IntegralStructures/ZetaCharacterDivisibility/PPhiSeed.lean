import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.ZetaCharacterDivisibility.PhiOfDivOf
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PDetWD
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PUnrGeom
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PSatGeom
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SplitLineSubtraction.PSatPol
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WdParameterMonodromyZeroIffPotentiallyCrystallin
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.CongL GlobalTheory.RoadWGeo
open Formalism.MainNotions.SumRepresentations.At (sumRep)
open GlobalTheory.TripleGal (rk1)
open UpperTheory.V.Af (FrobEig algSat RepIso)
open UpperTheory.Gal.TP.Sub (Cl Above unrPol)
open UpperTheory.Gal.crystallineComparison (GenericMul rootPol)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.BlockSum (blockRep)
open PositivityTheory.AutomorphicGaloisHodgeTate.Div (DivWCoreLac SenWLac HTLac IsSSMat)
open UpperTheory.Gal.Int.Div

theorem UpperTheory.Gal.Int.Div.phiSeed_of :
    SubLoc → LocConj → RootPin → AlgGen → PhiSeed := by
  intro hSub hConj hRoot hAlg E Ω _ _ _ _ _ _ l _ ι a dd U ψ hψ r ρ hc hs hin hdet w hw B hB hgen hk
  refine ⟨fun P AI hT A hA O _ _ _ Bw hj => ?_, fun P AI hT A h O _ _ _ Bw hj => ?_⟩
  · exact ((hSub E Ω l a dd r ρ hs hin ι w P AI hT A hA O Bw hj).1 (hk P AI hT A hA O Bw hj).1).1
  · obtain ⟨hρc, g, hg, m, hdiv⟩ := hk P AI hT A h O Bw hj
    obtain ⟨hrc, hdvd⟩ := (hSub E Ω l a dd r ρ hs hin ι w P AI hT A h O Bw hj).1 hρc
    have hpol : (GlobalTheory.RoadU.satWD h a B).charPol g = rootPol (algSat a (normV w) B) := by
      rw [UpperTheory.Gal.TP.Sub.satPol_holds E Ω A w h a B g, hg]
      simp [unrPol, rootPol]
    have hcd : ∀ x, Matrix.GeneralLinearGroup.det (((rk1 ψ).comp (Dec (F := E) A).subtype) x) =
        Matrix.GeneralLinearGroup.det ((r.comp (Dec (F := E) A).subtype) x) := by
      intro x
      apply Units.ext
      simp [rk1, Matrix.det_fin_one, hdet]
    obtain ⟨J, hCl⟩ := hψ.2 w hw B hB
    obtain ⟨hcC, -, -, hcP⟩ := hCl.2 P AI hT A h O Bw hj
    have hcPst := ((hConj l P AI hT E Ω A O Bw 1 ((rk1 ψ).comp (Dec (F := E) A).subtype)
      ((rk1 ψ).comp (Dec (F := E) A).subtype)).1 hcC).2
    have hprod := UpperTheory.Gal.crystallineComparison.detWD_holds l P AI hT ι E Ω A w h O Bw hj a
      (r.comp (Dec (F := E) A).subtype) ((rk1 ψ).comp (Dec (F := E) A).subtype) hcd hrc hcPst g hg
    have heig : (wdAt P ι Bw h hj ((rk1 ψ).comp (Dec (F := E) A).subtype)).eig g =
        {(algSat a (normV w) B).prod} := by
      rw [WD.eig, hcP g, hg]
      simp [unrPol]
    rw [heig, Multiset.prod_singleton, WD.eig] at hprod
    have hq : normV w ≠ 0 := GlobalTheory.LFun.qV_ne_zero w
    have hcard : (algSat a (normV w) B).card = a := by
      obtain ⟨σ, -, hσ⟩ := hB
      simpa [algSat] using GlobalTheory.LFun.HasSatGL.card hσ
    have hx : (wdAt P ι Bw h hj (r.comp (Dec (F := E) A).subtype)).charPol g =
        rootPol (algSat a (normV w) B) := by
      refine hRoot _ _ m (WD.charPol_monic _ g) ?_ ?_ hprod (hAlg a _ B hq hgen)
      · rw [WD.charPol_natDegree, GlobalTheory.PstLaws.lpDim_wdAt, hcard]
      · rw [← hpol]
        exact (hdvd g).trans hdiv
    have hxu := (GlobalTheory.PstLaws.unr_wdAt_iff Bw h hj P ι _
      ((hConj l P AI hT E Ω A O Bw a (r.comp (Dec (F := E) A).subtype)
        (r.comp (Dec (F := E) A).subtype)).1 hrc).2).2 hrc
    have hsu := (UpperTheory.Gal.crystallineComparison.satGeom_of E Ω A w h a B).1
    intro g'
    rw [UpperTheory.Gal.crystallineComparison.unrGeom_of E Ω A w h _ _ hxu hsu g hg (hx.trans hpol.symm)]
