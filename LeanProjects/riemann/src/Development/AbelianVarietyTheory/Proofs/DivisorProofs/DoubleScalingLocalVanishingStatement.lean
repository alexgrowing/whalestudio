import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubleScalingLocalVanishing
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndicatorIntMMemSB
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaActionExistsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FromBlocksSubOne
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.KSplit
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.double_scaling_local_vanishing : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ)
    (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (v : Pl F) (t : E →ₐ[F] Fv F v) (b : GL (Fin n) (Fv F v)) (c : GL (Fin d) (Fv F v))
      (dd : GlobalTheory.DblScal.DblCo σ X W) (omd : GlobalTheory.DblScal.DblRep σ (n := n) W),
      IsDblCoord (cA σ) (-1) (incM F X.J) (incM F W.J) M.co dd →
      IsUWeilSplit (cA σ) (adeleClass F) B.ψ (-1) (incM F X.J) (dbl (incM F W.J)) dd χX (diagCols (Fin d)) omd →
      GlobalTheory.DblScal.LocOps omd v →
      ∀ ιd, GlobalTheory.DblScal.IsLinD B.ψ dd t b c ιd → ∀ cd, GlobalTheory.DblScal.IsShapeD omd t c ιd cd →
      ∀ p ∈ GlobalTheory.DblScal.UDAt σ W.J (evFin F v),
        (∃ T : Matrix (Fin d) (Fin d) (Fv F v),
          ((GlobalTheory.DblScal.locMatD t c p).val : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (Fv F v)) *
            (diagCols (Fin d) : Matrix (Fin d ⊕ Fin d) (Fin d) (Fv F v)) =
            (diagCols (Fin d) : Matrix (Fin d ⊕ Fin d) (Fin d) (Fv F v)) * T) →
        cd p = (chrW χX t (GlobalTheory.SplitFlip.gdet (GlobalTheory.DblScal.locMatD t c p)) : ℂ) *
          GlobalTheory.SplitFlip.apow (GlobalTheory.SplitFlip.gdet (GlobalTheory.DblScal.locMatD t c p)) (-(n : ℂ) / 2) := by
  first | exact @GlobalTheory.DblSiegelScal.scalar_siegel | exact GlobalTheory.DblSiegelScal.scalar_siegel | (intros; apply GlobalTheory.DblSiegelScal.scalar_siegel <;> assumption)
