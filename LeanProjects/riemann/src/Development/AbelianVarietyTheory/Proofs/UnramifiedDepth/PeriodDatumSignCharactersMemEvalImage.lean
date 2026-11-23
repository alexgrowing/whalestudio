import Mathlib
import ReciprocityTheory.DualLattices.HtdOf
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.EvBasicNEvalSubCoeffMem
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ChartFirstOrderMemSpan
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.NsmulFAddSqZeroEq
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.CoeffDvdOfAevalAddSqZero
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.PSerFrobOfInvariance
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.CoeffDecomp
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ChartPSmulLiftEqBt
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.FAddNsmulFEqEvalPolyFrob
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.LocalFactorModPNilOver
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.EvBtOfTangentOfSeries
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.HtDualExists
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.EvImgIsLatSubring
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ValNatCastSmul
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.PairingNsmulRight
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.IsLocalRingTensorProductOfFiniteOfPoints
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.EvHopfOfTensorLocal
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.PointsEqTangent
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.UniversalDerivation
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.EvCotOfUnivDer
open TensorProduct IsLocalRing Matrix ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2

noncomputable section

namespace GlobalTheory.EvClose

theorem pSerFrob {R₀ : Type} [CommRing R₀] (p : ℕ) [Fact p.Prime] {g : ℕ} {B : BX R₀}
    (K : LAlg R₀) (ch : FormalChartAtZero B K g) : PSerFrobStatement p K ch :=
  GlobalTheory.pSerFrob_of_invariance @GlobalTheory.nEval_basic
    (GlobalTheory.nsmulF_add_sqZero_eq @GlobalTheory.nEval_basic (GlobalTheory.chart_fAdd_firstOrder @GlobalTheory.nEval_basic))
    @GlobalTheory.coeff_dvd_of_aeval_add_sq_zero p K ch

theorem wFrob {R₀ : Type} [CommRing R₀] {p : ℕ} [Fact p.Prime] {Tw : ATowerL R₀ p}
    {K : LAlg R₀} (wd : WData Tw K) (g : ℕ) : WFrobStatement wd g :=
  GlobalTheory.WFrob.wFrob wd g

section Leaves

variable {R₀ : Type} [CommRing R₀] {p : ℕ} [Fact p.Prime] {g : ℕ} {B : BX R₀} {Tw : ATowerL R₀ p}
  {Dt : DualTower Tw} [Algebra ℤ_[p] (Tw.O : Type)] {Oe : Type} [CommRing Oe] [Algebra ℤ_[p] Oe]
  {σ : Oe ≃ₐ[ℤ_[p]] Oe} {cp : (Tw.O : Type)}

theorem evLat (D : Dat p g B Tw Dt Oe σ cp) : EvLatStatement D :=
  GlobalTheory.evImg_isLat_subring D

theorem evHopf (D : Dat p g B Tw Dt Oe σ cp) : EvHopfStatement D :=
  GlobalTheory.EvHopf.evHopf_of_tensorLocal GlobalTheory.isLocalRing_tensorProduct_of_finite_of_points D

theorem evAct (D : Dat p g B Tw Dt Oe σ cp) : EvActStatement D :=
  GlobalTheory.EvAct.evImg_act_stable D

theorem evHt (D : Dat p g B Tw Dt Oe σ cp) : EvHtStatement D :=
  GlobalTheory.evHt_of_lam @GlobalTheory.localFactor_mod_p_nilOver D

theorem evBt (D : Dat p g B Tw Dt Oe σ cp) : EvBtStatement D :=
  GlobalTheory.evBt_of_tangent_of_series
    (GlobalTheory.chart_p_smul_lift_eq_bt (GlobalTheory.chart_fAdd_firstOrder @GlobalTheory.nEval_basic))
    (GlobalTheory.fAdd_nsmulF_eq_eval_poly_frob @GlobalTheory.nEval_basic @pSerFrob)
    @GlobalTheory.localFactor_mod_p_nilOver @wFrob D

theorem periodDatum_signCharacters_mem_evalImage (D : Dat p g B Tw Dt Oe σ cp) : EvenTwoEvaluationSign D :=
  GlobalTheory.signChar_mem_evImg D

theorem evCot (D : Dat p g B Tw Dt Oe σ cp) : EvCotStatement D :=
  GlobalTheory.evCot_of_univDer (GlobalTheory.CotUniv.universal_derivation @GlobalTheory.CotPoints.points_eq_tangent) D

def htdOfDat (D : Dat p g B Tw Dt Oe σ cp) (C : Type) [Field C] (v : Valuation C NNReal)
    [Algebra (Tw.O : Type) C] (hdom : IsDomain (Tw.O : Type))
    (hinj : Function.Injective (algebraMap (Tw.O : Type) C)) :
    HodgeTateDatum p g v (Tw.O : Type) Oe σ cp :=
  htd_of D C v hdom hinj (evLat D) (evHopf D) (evAct D) (evHt D) (evBt D) (periodDatum_signCharacters_mem_evalImage D) (evCot D)

end Leaves

end GlobalTheory.EvClose
