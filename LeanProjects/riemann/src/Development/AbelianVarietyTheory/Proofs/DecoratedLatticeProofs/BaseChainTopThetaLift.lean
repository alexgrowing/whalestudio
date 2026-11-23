import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StageY
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FrameTopAlt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RatioOKOfRootOfUnity
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExtraColumnRangeMembershipStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualFrameVacuumStepStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TopStepVectorPropertyStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.BaseChain

theorem setIntegral_smul_measure_complex {H : Type*} [MeasurableSpace H] (c : ENNReal) (ν : Measure H) (s : Set H) (f : H → ℂ) :
    ∫ y in s, f y ∂(c • ν) = c.toReal • ∫ y in s, f y ∂ν := by
  rw [Measure.restrict_smul, integral_smul_measure]

theorem stepX_isIo : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex) (u : D.what₂.Word) (f : FamCh W u), PkHyp W → f.RowOK → ∀ j (h : j + 2 * 0 + 2 = D.R.m), Lift.IsIo (GlobalTheory.BaseChain.stageX W).ν (GlobalTheory.BaseChain.stageX W).fd (thetaKO (GlobalTheory.BaseChain.stepX f j h).ω) (GlobalTheory.BaseChain.stepX f j h).pt (GlobalTheory.BaseChain.stepX f j h).It ((GlobalTheory.BaseChain.stageX W).CC (GlobalTheory.BaseChain.com W)) ((GlobalTheory.BaseChain.stageY W (j + 1)).CC (GlobalTheory.BaseChain.com W)) (GlobalTheory.BaseChain.stepX f j h).io := by
  intro D L hT Gi Gl Kc Yd cX ex W u f hP hf j h
  have hcard : Nat.card (lvP W).H ≠ 0 := by
    have hf' : ∀ PP : (pk W).Pg, Finite (kP PP.1) := fun PP => Ideal.finiteQuotientOfFreeOfNeBot _ PP.1.ne_bot
    exact Nat.card_pos.ne'
  have hcH : GlobalTheory.BaseChain.cH W ≠ ⊤ := by
    simp [GlobalTheory.BaseChain.cH]
  refine ⟨fun F φ v g => ?_, fun F φ v g => ?_⟩
  · have h1 := GlobalTheory.T.top_step_vector_property W hP j h _ ((hf.row W.P.A3.A.μ0).vT j h) F φ v g
    unfold IntegrableOn at h1 ⊢
    change Integrable _ ((GlobalTheory.BaseChain.cH W • (pk W).νX W.P.A3.A.μ0).restrict ((pk W).fdX W.P.A3.A.μ0))
    rw [Measure.restrict_smul]
    exact h1.smul_measure hcH
  · obtain ⟨h', -, hL⟩ := GlobalTheory.T.extra_column_range_membership W u hP f.g W.P.A3.A.μ0 j h F
    obtain ⟨h'', he⟩ := (hf.row W.P.A3.A.μ0).ioT j h F
    have e1 := congrFun (hL _ ((hf.row W.P.A3.A.μ0).vT j h) φ v) g
    have key : ∀ X : ℂ, (GlobalTheory.BaseChain.cH W).toReal • ((Nat.card (lvP W).H : ℂ) * X) = X := by
      intro X
      have e3 : (GlobalTheory.BaseChain.cH W).toReal = ((Nat.card (lvP W).H : ℝ))⁻¹ := by
        simp [GlobalTheory.BaseChain.cH, ENNReal.toReal_inv]
      have hc : ((Nat.card (lvP W).H : ℂ)) ≠ 0 := Nat.cast_ne_zero.2 hcard
      rw [e3, Complex.real_smul, ← mul_assoc]
      push_cast
      rw [inv_mul_cancel₀ hc, one_mul]
    change ∫ y in (pk W).fdX W.P.A3.A.μ0, _ ∂(GlobalTheory.BaseChain.cH W • (pk W).νX W.P.A3.A.μ0) =
      ((f.row W.P.A3.A.μ0).ioT j h F).1 (f.c.ItT j h φ v) g
    rw [setIntegral_smul_measure_complex, he]
    have e2 : (∫ y in (pk W).fdX W.P.A3.A.μ0, thetaKO (omT (pk W) W.P.A3.A.μ0 j h) g y
        (pureTensorO (pk W).ψ (pk W).θ (Yc D (j + 1)) D.sp.X' (cart ((pk W).MY (j + 1))) (cart (pk W).MX)
          (onb ((pk W).MY (j + 1))) (onb (pk W).MX) ((f.row W.P.A3.A.μ0).vT j h) φ) * F.1 v y ∂(pk W).νX W.P.A3.A.μ0) =
        (Nat.card (lvP W).H : ℂ) * (ioXT (pk W) W.P.A3.A.μ0 j h ⟨F.1, h''⟩).1 (f.c.ItT j h φ v) g := e1
    exact (congrArg (fun z : ℂ => (GlobalTheory.BaseChain.cH W).toReal • z) e2).trans (key _)

end GlobalTheory.BaseChain

end
