import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsLevMeas
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilDatumAtPlaceEqLatticeIntertwinerMulDetChar
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitIdempotentPrimeProjectionCorrespondence
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitProjAdeleComponentChartProperties
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsSplitChartOfBasis
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsEigenSysOfHeckeLin
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemHomLatticeCompletionIffSupportedMaps
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LiftsCharOfResidueCharAtSplitPlace
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitProjectionUnderEqResidueCardEqAbsNorm
import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TransferOn
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CartFrSgn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.LocUnifVal

theorem valued_eq_of_unif {D : D7} {v : HeightOneSpectrum (𝓞 D.host.F)} (ϖ : (Fv D.host.F v)ˣ)
    (hϖ : ValuativeRel.valuation (Fv D.host.F v) (ϖ : Fv D.host.F v) = ValuativeRel.uniformizer (Fv D.host.F v)) :
    Valued.v (ϖ : Fv D.host.F v) = WithZero.exp (-1 : ℤ) := by
  haveI : (Valued.v : Valuation (Fv D.host.F v) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  have key : ∀ a b : Fv D.host.F v, ValuativeRel.valuation (Fv D.host.F v) a ≤ ValuativeRel.valuation (Fv D.host.F v) b ↔
      Valued.v a ≤ Valued.v b := fun a b =>
    (Valuation.Compatible.vle_iff_le (v := ValuativeRel.valuation (Fv D.host.F v)) a b).symm.trans
      (Valuation.Compatible.vle_iff_le (v := (Valued.v : Valuation (Fv D.host.F v) (WithZero (Multiplicative ℤ)))) a b)
  have hlt : Valued.v (ϖ : Fv D.host.F v) < 1 := by
    have h1 : ValuativeRel.valuation (Fv D.host.F v) (ϖ : Fv D.host.F v) < ValuativeRel.valuation (Fv D.host.F v) 1 := by
      rw [map_one, hϖ]; exact ValuativeRel.uniformizer_lt_one
    rw [← map_one (Valued.v : Valuation (Fv D.host.F v) _)]
    exact lt_of_not_ge fun h => (not_le.2 h1) ((key _ _).2 h)
  obtain ⟨π, hπ⟩ := v.valuation_exists_uniformizer D.host.F
  have hx : Valued.v (algebraMap D.host.F (Fv D.host.F v) π) = WithZero.exp (-1 : ℤ) := by
    rw [ReciprocityTheory.Aut.adic_valued_algebraMap, hπ]
  have hle : WithZero.exp (-1 : ℤ) ≤ Valued.v (ϖ : Fv D.host.F v) := by
    rw [← hx]
    refine (key _ _).1 ?_
    rw [hϖ, ValuativeRel.le_uniformizer_iff, ← map_one (ValuativeRel.valuation (Fv D.host.F v))]
    refine lt_of_not_ge fun h => ?_
    have := (key _ _).1 h
    rw [map_one, hx] at this
    exact absurd this (by rw [← WithZero.exp_zero, WithZero.exp_le_exp]; norm_num)
  have h0 : Valued.v (ϖ : Fv D.host.F v) ≠ 0 := (map_ne_zero _).2 ϖ.ne_zero
  rw [← WithZero.exp_log h0] at hlt hle ⊢
  rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at hlt
  rw [WithZero.exp_le_exp] at hle
  congr 1
  omega

theorem value_eq_val : ∀ (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)) (φ : SplitProj D v) (PP : Pl D.host.E), IsProjAt φ PP → ∀ (x : (AE D)ˣ) (ϖ : (Fv D.host.F v)ˣ), IsLocUnif φ x ϖ → ∀ χ : (AE D)ˣ →* Circle, GlobalTheory.LFun.UnrAt (F := D.host.F) χ PP → Circle.toUnits (χ x) = GlobalTheory.LFun.val (F := D.host.F) χ PP := by
  intro D v φ PP hφ x ϖ hloc χ hχ
  obtain ⟨e, he, hx1, hx2, hx3⟩ := hloc
  have h : PP.under (𝓞 D.host.F) = v := (GlobalTheory.PlaceProjAt.under_resCard D v φ PP hφ).1.symm
  have hAt : Formalism.L2.NTheta.IsIdemAt e PP := (((GlobalTheory.SplitIdemDict.idem_dictionary D).2 v φ PP hφ).2.2 e he).1
  have hP : IsPrimeIdem PP e (e + cA D e) := Or.inl ⟨hAt, rfl⟩
  have hxe : e * ((x : AE D) - 1) = (x : AE D) - 1 := by linear_combination -hx1
  obtain ⟨y, hy, hxy⟩ := GlobalTheory.WeilAtPlace.exists_eq_locIdele (GlobalTheory.WeilAtPlace.isPrimeIdem_infPart hP)
    (GlobalTheory.LFun.finPart_of_isPrimeIdem hP) x hxe
  have hτ : GlobalTheory.AdelicU.splitPrime (GlobalTheory.SplitProjChart.emb φ) = PP := (GlobalTheory.ResLift.eq_splitPrime hφ).symm
  have hc : (y : PP.adicCompletion D.host.E) = GlobalTheory.LFun.complMap h (ϖ : Fv D.host.F v) := by
    have e1 : Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV D.host.F v) (AlgHom.id D.host.F D.host.E) (finPart D (x : AE D)) =
        GlobalTheory.AdelicU.compFin D.host.F D.host.E v (x : AE D) := by
      rw [GlobalTheory.FinPl.LatMem.compFin_eq_compAt]; rfl
    rw [hy, GlobalTheory.LFun.compAt_apply, GlobalTheory.LFun.finAdEquiv_apply h, e1,
      GlobalTheory.LFun.ConjPlace.toCompl_eq (GlobalTheory.AdelicU.isCMExt_host D) h hτ, GlobalTheory.SplitProjChart.splitProj_emb, ← hx2]
    rfl
  have hu : Formalism.L2.Host.IsUnifAt PP y := by
    unfold Formalism.L2.Host.IsUnifAt
    rw [hc, GlobalTheory.LFun.ConjPlace.valued_complMap (GlobalTheory.AdelicU.isCMExt_host D) h hτ]
    exact GlobalTheory.LocUnifVal.valued_eq_of_unif ϖ hx3
  have := hχ.locChar_eq_val hu
  rw [← this, hxy]
  rfl

end GlobalTheory.LocUnifVal
