import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RangeSndRel
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.FinitePartTypes
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegrableOnOfRapidDec
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaGrowthOfThetaSquareIntegrable
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.UnifModGrowthOfIsUnifModerate
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CuspAlongOfPairLifts
import Development.AbelianVarietyTheory.Proofs.HeightProofs.TypeAtOfDiscreteSeries
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsGrowthSobNeTopOfIsAutFunSm
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section
open GlobalTheory.Grow GlobalTheory.Size
open scoped ENNReal

namespace GlobalTheory.CuspApproxAll

variable {D : D7}

def avgList (θ : InfFam D) (N : GlobalTheory.Grid.Node D) (e : ∀ τ, Formalism.REAL.KG (N.M.ε τ) → ℂ)
    (l : List D.what₂.Tau) (φ : GA D N.V → ℂ) : GA D N.V → ℂ :=
  l.foldr (fun τ f => GlobalTheory.SeriesToClosure.avg θ N.V τ (N.M.ε τ) (N.M.fr τ) (e τ) f) φ

theorem avgList_nil (θ : InfFam D) (N : GlobalTheory.Grid.Node D) (e : ∀ τ, Formalism.REAL.KG (N.M.ε τ) → ℂ) (φ : GA D N.V → ℂ) :
    avgList θ N e [] φ = φ := rfl

theorem avgList_cons (θ : InfFam D) (N : GlobalTheory.Grid.Node D) (e : ∀ τ, Formalism.REAL.KG (N.M.ε τ) → ℂ) (τ : D.what₂.Tau)
    (l : List D.what₂.Tau) (φ : GA D N.V → ℂ) :
    avgList θ N e (τ :: l) φ = GlobalTheory.SeriesToClosure.avg θ N.V τ (N.M.ε τ) (N.M.fr τ) (e τ) (avgList θ N e l φ) := rfl

theorem growthSob_zero_ne_top {θ : InfFam D} {V : HSp D} {φ : GA D V → ℂ} (h : RapidDecSm θ V φ) (d : ℕ) :
    growthSob θ V d 0 φ ≠ ∞ := by
  let M : Submodule ℂ (GA D V → ℂ) :=
    { carrier := {f | growthSize V 0 f ≠ ∞}
      add_mem' := fun a b => ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨a, b⟩) growthSize_add_le
      zero_mem' := (growthSize_const (0 : ℂ)).trans_ne enorm_ne_top
      smul_mem' := fun c _ a => (growthSize_smul c).trans_ne (ENNReal.mul_ne_top enorm_ne_top a) }
  have hM : φ ∈ allDer θ V M := ⟨h.smooth, fun l hl => modGrowthExp_iff.1
    ((h.decay l hl).bounded.imp fun _ hC g => (hC g).trans_eq (by simp))⟩
  refine wordSum_ne_top_iff.2 fun l _ => ?_
  exact (wordAct_rel (A := glDer θ V) (B := glDer θ V) (R := fun f _ => f ∈ allDer θ V M) l
    (fun a _ _ _ hf => RderC_mem_allDer hf a.1 _) (y := φ) hM).2 [] (fun _ h => by simp at h)

def Good (θ : InfFam D) (V : HSp D) (f : GA D V → ℂ) : Prop := RapidDecSm θ V f ∧ IsCuspFun V f

theorem good_add {θ : InfFam D} {V : HSp D} {f f' : GA D V → ℂ} (h : Good θ V f) (h' : Good θ V f') :
    Good θ V (f + f') :=
  ⟨h.1.add h'.1, GlobalTheory.MultMem.isCuspFun_add h.1.toIsAutFun h'.1.toIsAutFun h.2 h'.2⟩

theorem good_smul {θ : InfFam D} {V : HSp D} {f : GA D V → ℂ} (c : ℂ) (h : Good θ V f) : Good θ V (c • f) :=
  ⟨h.1.smul c, GlobalTheory.MultMem.isCuspFun_smul c h.2⟩

theorem good_zero (θ : InfFam D) (V : HSp D) : Good θ V 0 := by
  refine ⟨rapidDecSm_iff.2 ⟨zero_mem _, ⊤, isOpen_univ, fun _ _ _ _ => rfl⟩, ?_⟩
  exact fun _ _ _ _ _ _ _ _ => by simp

theorem good_value (hP : GlobalTheory.Published.CuspRapidDecay) {θ : InfFam D} (hθ : IsInfFam θ) (N : GlobalTheory.Grid.Node D) {Φ : N.Maps}
    (hΦ : Φ ∈ N.Cusp θ) (v : SmT N.M) : Good θ N.V (Φ v) := by
  obtain ⟨U, hU, rfl⟩ := Submodule.mem_map.1 hΦ
  clear hΦ
  have hU' : ∀ w, Good θ N.V (U w) := by
    induction hU using Submodule.span_induction with
    | mem x hx => exact fun w => ⟨rapidDecSm_of_cuspForm hP hθ (hx.aut w) (hx.cusp w), hx.cusp w⟩
    | zero => exact fun w => good_zero θ N.V
    | add x y _ _ hx hy => exact fun w => good_add (hx w) (hy w)
    | smul c x _ hx => exact fun w => good_smul c (hx w)
  induction v using PiTensorProduct.induction_on with
  | smul_tprod r f => simpa using good_smul r (hU' f)
  | add x y hx hy => simpa using good_add hx hy

end GlobalTheory.CuspApproxAll
