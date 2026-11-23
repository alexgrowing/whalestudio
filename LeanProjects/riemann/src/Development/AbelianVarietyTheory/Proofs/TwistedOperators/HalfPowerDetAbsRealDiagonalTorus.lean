import Mathlib
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicUnitaryTopology
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SkewGramHalfModule
import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceTensorProductFiniteExtension
import Development.AbelianVarietyTheory.Definitions.Foundations.OfInfProjInfMulOfFinProjFin
import Development.AbelianVarietyTheory.Proofs.HeightProofs.EqOrConjOfPlaceOf
import Development.AbelianVarietyTheory.Proofs.HeightProofs.CmTypeRestrictRealSubfieldInfinitePlaceBijective
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CmDataIsCMExtAndGramIsHermND
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped Pointwise
open Formalism.IndefR.Datum
open GlobalTheory.Grid

noncomputable section

namespace GlobalTheory.HalfModTorus

open GlobalTheory.Doubling

theorem compFin_eq_one {D : D7} (v : HeightOneSpectrum (𝓞 D.host.F)) (y : AE D) (h : finPart D y = 1) :
    GlobalTheory.AdelicU.compFin D.host.F D.host.E v y = 1 := by
  have h' : Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E) y = 1 := h
  have e : GlobalTheory.AdelicU.compFin D.host.F D.host.E v y =
      Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV D.host.F v) (AlgHom.id D.host.F D.host.E)
        (Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E) y) := by
    rw [← AlgHom.comp_apply, ← Algebra.TensorProduct.map_comp, AlgHom.comp_id]
    rfl
  rw [e, h', map_one]

theorem unitFin_eq_one {D : D7} (v : HeightOneSpectrum (𝓞 D.host.F)) (x : (AE D)ˣ) (h : finPart D (x : AE D) = 1) :
    unitFin D.host.F D.host.E v x = 1 :=
  Units.ext (compFin_eq_one v (x : AE D) h)

theorem compInf_eq {D : D7} (w : InfinitePlace D.host.F) (t' : GlobalTheory.AdelicU.EmbOver D.host.E w) (y : AE D) :
    GlobalTheory.AdelicU.infEmb t' (GlobalTheory.AdelicU.compInf D.host.F D.host.E w y) = GlobalTheory.AdelicU.infProj t' (infPart D y) := by
  have e : GlobalTheory.AdelicU.compInf D.host.F D.host.E w y =
      Algebra.TensorProduct.map (GlobalTheory.AutFunCompare.evW w) (AlgHom.id D.host.F D.host.E)
        (Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E) y) := by
    rw [← AlgHom.comp_apply, ← Algebra.TensorProduct.map_comp, AlgHom.comp_id]
    rfl
  rw [e]
  rfl

theorem absE_of_components {D : D7} (x : (AE D)ˣ) (c : NNReal)
    (hf : ∀ v, absEv D.host.F D.host.E v (unitFin D.host.F D.host.E v x) = 1)
    (hw : ∀ τ : D.what₂.Tau, absEw D.host.F D.host.E
      (InfinitePlace.mk ((tauE D τ).comp (algebraMap D.host.F D.host.E))) (unitInf D.host.F D.host.E _ x) = c) :
    absE D.host.F D.host.E x = c ^ Fintype.card D.what₂.Tau := by
  have e1 : (∏ᶠ v, absEv D.host.F D.host.E v (unitFin D.host.F D.host.E v x)) = 1 :=
    finprod_eq_one_of_forall_eq_one hf
  have e2 : (∏ w, absEw D.host.F D.host.E w (unitInf D.host.F D.host.E w x)) = c ^ Fintype.card D.what₂.Tau := by
    rw [← (GlobalTheory.CMTypePlaces.places_bijective D).prod_comp
      (fun w => absEw D.host.F D.host.E w (unitInf D.host.F D.host.E w x))]
    simp only [hw, Finset.prod_const, Finset.card_univ]
  rw [absE_apply, e1, e2, mul_one]

theorem halfMod_torus : ∀ {D : D7} (θ : InfFam D), IsInfFam θ → ∀ (r n : ℕ) (t : Fin r → ℝ), (∀ i, 0 < t i) →
    ∀ α : GL (Fin r) (Formalism.L2.Theta.AE D), α.1.map (finPart D) = 1 →
      (∀ τ, compAt θ τ α.1 = diagonal (fun i => (t i : ℂ))) →
      GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.halfMod n α = ∏ i, t i ^ (Module.finrank ℚ D.host.F * n) := by
  intro D θ hθ r n t ht α hfin hinf
  have hcm := (GlobalTheory.Mem.Vol.cmData_isCMExt_and_gram_isHermND _ _ D.sp.cm).1
  haveI := hcm.1
  have hxv : ((Matrix.GeneralLinearGroup.det α : (AE D)ˣ) : AE D) = α.1.det := rfl
  have h1 : finPart D ((Matrix.GeneralLinearGroup.det α : (AE D)ˣ) : AE D) = 1 := by
    rw [hxv, RingHom.map_det, RingHom.mapMatrix_apply, hfin, Matrix.det_one]
  have hf : ∀ v, absEv D.host.F D.host.E v (unitFin D.host.F D.host.E v (Matrix.GeneralLinearGroup.det α)) = 1 :=
    fun v => by rw [unitFin_eq_one v _ h1, map_one]
  have hdet : ∀ τ, θ τ (infPart D ((Matrix.GeneralLinearGroup.det α : (AE D)ˣ) : AE D)) = ((∏ i, t i : ℝ) : ℂ) := by
    intro τ
    have e : θ τ (infPart D ((Matrix.GeneralLinearGroup.det α : (AE D)ˣ) : AE D)) = (compAt θ τ α.1).det := by
      rw [hxv, ← RingHom.comp_apply, RingHom.map_det]
      rfl
    rw [e, hinf τ, Matrix.det_diagonal, Complex.ofReal_prod]
  have hw : ∀ τ : D.what₂.Tau, absEw D.host.F D.host.E
      (InfinitePlace.mk ((tauE D τ).comp (algebraMap D.host.F D.host.E)))
      (unitInf D.host.F D.host.E _ (Matrix.GeneralLinearGroup.det α)) = ‖((∏ i, t i : ℝ) : ℂ)‖₊ ^ 2 := by
    intro τ
    let t' : GlobalTheory.AdelicU.EmbOver D.host.E (InfinitePlace.mk ((tauE D τ).comp (algebraMap D.host.F D.host.E))) :=
      ⟨tauE D τ, (InfinitePlace.embedding_mk_eq_of_isReal
        (InfinitePlace.isReal_mk_iff.1 (IsTotallyReal.isReal _))).symm⟩
    rw [absEw_eq_sq hcm t', ← hdet τ,
      GlobalTheory.AutFunCompare.isInfEmb_unique _ _ _ (hθ τ) (GlobalTheory.AdelicU.isInfEmb_infProj t')]
    exact congrArg (fun z : ℂ => ‖z‖₊ ^ 2) (compInf_eq _ t' _)
  have hcard : Fintype.card D.what₂.Tau = Module.finrank ℚ D.host.F := by
    rw [Fintype.card_of_bijective (GlobalTheory.CMTypePlaces.places_bijective D), IsTotallyReal.finrank,
      InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces, IsTotallyReal.nrComplexPlaces_eq_zero, add_zero]
  have hP : 0 < ∏ i, t i := Finset.prod_pos fun i _ => ht i
  have habs : ((absE D.host.F D.host.E (Matrix.GeneralLinearGroup.det α) : NNReal) : ℝ) =
      (∏ i, t i) ^ (2 * Module.finrank ℚ D.host.F) := by
    rw [absE_of_components _ _ hf hw, hcard, NNReal.coe_pow, NNReal.coe_pow, coe_nnnorm, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hP, ← pow_mul]
  unfold GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.halfMod
  rw [habs, Finset.prod_pow, ← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul hP.le]
  congr 1
  push_cast
  ring

end GlobalTheory.HalfModTorus
