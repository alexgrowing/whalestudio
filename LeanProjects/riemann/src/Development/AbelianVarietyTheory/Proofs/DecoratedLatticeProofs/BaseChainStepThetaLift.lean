import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StageY
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FrameTopAlt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChainProjectionLevelCharacterStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsLevelElementsStepVectorStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.BaseChain.thetaKO_sum_smul_act {D : D7} {S T : HSp D} {ι : Type} (s : Finset ι) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ))
    (g : GA D S) (h : GA D T) (c : ι → ℂ) (κ : ι → GA D S) (f : WO S T → ℂ) :
    thetaKO om g h (∑ p ∈ s, c p • om (κ p, 1) f) = ∑ p ∈ s, c p * thetaKO om (g * κ p) h f := by
  simp only [thetaKO, map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun p _ => ?_
  congr 1
  rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one]

set_option maxHeartbeats 1000000 in

theorem GlobalTheory.BaseChain.stepY_integrable_and_eq {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex) (hW : PkHyp W) (t) (j) (hj : j + 1 < D.R.m) (F : CP (pk W) (lvP W) t (j + 1)) (hF : F.1 ∈ (pk W).CC t (j + 1)) (v) (hv : IsStepVecOf (pk W).ψ (pk W).θ (Yc D j) (Yc D (j + 1)) (cart ((pk W).MY j)) (cart ((pk W).MY (j + 1))) ((pk W).ΛY j) ((pk W).ΛY (j + 1)) ((pk W).βY j) ((pk W).βY (j + 1)) ((pk W).datYt t j (lvP W)) ((pk W).chi (j + 1)) ((pk W).Q t) ((pk W).xiR t) ((pk W).vac j) v) (Q x g) :
  IntegrableOn (fun h => thetaKO ((pk W).ωY t j) g h (pureTensorO (pk W).ψ (pk W).θ (Yc D j) (Yc D (j + 1)) (cart ((pk W).MY j)) (cart ((pk W).MY (j + 1))) (onb ((pk W).MY j)) (onb ((pk W).MY (j + 1))) v Q) * F.1 x h) ((pk W).fdY t (j + 1)) ((pk W).νY t (j + 1)) ∧
  (∫ y in (pk W).fdY t (j + 1), thetaKO ((pk W).ωY t j) g y (pureTensorO (pk W).ψ (pk W).θ (Yc D j) (Yc D (j + 1)) (cart ((pk W).MY j)) (cart ((pk W).MY (j + 1))) (onb ((pk W).MY j)) (onb ((pk W).MY (j + 1))) v Q) * F.1 x y ∂((pk W).νY t (j + 1))) = (Nat.card (lvP W).H : ℂ) * ((pk W).ioY t j ⟨F.1, hF⟩).1 ((pk W).ItY j Q x) g := by
  have hio : Lift.IsIo ((pk W).νY t (j + 1)) ((pk W).fdY t (j + 1)) (thetaKO ((pk W).ωY t j)) ((pk W).ptY t j)
      ((pk W).ItY j) ((pk W).CC t (j + 1)) ((pk W).CC t j) ((pk W).ioY t j) :=
    hW.bot.hyp.2.2.2.1.chain.ioY t j (by omega)
  have hfin : ∀ PP : (pk W).Pg, Finite (kP PP.1) := fun PP => Ideal.finiteQuotientOfFreeOfNeBot _ PP.1.ne_bot
  haveI : Fintype (lvP W).H := Fintype.ofFinite _
  obtain ⟨κ, hκ, hsum⟩ := GlobalTheory.T.exists_level_elements_step_vector W hW t j hj
  rw [hsum v hv Q]
  simp_rw [GlobalTheory.BaseChain.thetaKO_sum_smul_act]
  have hint : ∀ p ∈ (Finset.univ : Finset (lvP W).H), IntegrableOn (fun h => (levChi (Yc D j) ((pk W).βY j) ((pk W).datYt t j (lvP W)) (κ p))⁻¹ * thetaKO ((pk W).ωY t j) (g * κ p) h ((pk W).ptY t j Q) * F.1 x h) ((pk W).fdY t (j + 1)) ((pk W).νY t (j + 1)) := by
    intro p _
    simp_rw [mul_assoc]
    exact (hio.integ ⟨F.1, hF⟩ Q x (g * κ p)).const_mul _
  simp_rw [Finset.sum_mul]
  refine ⟨integrable_finset_sum _ hint, ?_⟩
  rw [integral_finset_sum _ hint]
  have e : ∀ p ∈ (Finset.univ : Finset (lvP W).H), ∫ h in (pk W).fdY t (j + 1), (levChi (Yc D j) ((pk W).βY j) ((pk W).datYt t j (lvP W)) (κ p))⁻¹ * thetaKO ((pk W).ωY t j) (g * κ p) h ((pk W).ptY t j Q) * F.1 x h ∂(pk W).νY t (j + 1) =
      ((pk W).ioY t j ⟨F.1, hF⟩).1 ((pk W).ItY j Q x) g := by
    intro p _
    simp_rw [mul_assoc]
    rw [integral_const_mul]
    have h1 := hio.eq ⟨F.1, hF⟩ Q x (g * κ p)
    simp only [Lift.liftInt] at h1
    rw [h1, GlobalTheory.T.chain_projection_level_character W hW t j hj ⟨F.1, hF⟩ F.2 (κ p) (hκ p) Q x g]
    rw [← mul_assoc, inv_mul_cancel₀ (Lev.levChi_ne_zero (V := Yc D j) (β := (pk W).βY j) ((pk W).datYt t j (lvP W)) (κ p)), one_mul]
  rw [Finset.sum_congr rfl e, Finset.sum_const, Finset.card_univ]
  simp only [Nat.card_eq_fintype_card, nsmul_eq_mul]

set_option maxHeartbeats 1000000 in

theorem GlobalTheory.BaseChain.stepY_isIo : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex) (u : D.what₂.Word) (f : FamCh W u), PkHyp W → f.RowOK → ∀ j, j + 1 < D.R.m → Lift.IsIo (GlobalTheory.BaseChain.stageY W (j + 1)).ν (GlobalTheory.BaseChain.stageY W (j + 1)).fd (thetaKO (GlobalTheory.BaseChain.stepY f j).ω) (GlobalTheory.BaseChain.stepY f j).pt (GlobalTheory.BaseChain.stepY f j).It ((GlobalTheory.BaseChain.stageY W (j + 1)).CC (GlobalTheory.BaseChain.com W)) ((GlobalTheory.BaseChain.stageY W j).CC (GlobalTheory.BaseChain.com W)) (GlobalTheory.BaseChain.stepY f j).io := by
  intro D L hT Gi Gl Kc Yd cX ex W u f hW hf j hj
  have hrow := hf.row W.P.A3.A.μ0
  have hfin : ∀ PP : (pk W).Pg, Finite (kP PP.1) := fun PP => Ideal.finiteQuotientOfFreeOfNeBot _ PP.1.ne_bot
  have hc : Nat.card (lvP W).H ≠ 0 := Nat.card_pos.ne'
  have hne : GlobalTheory.BaseChain.cH W ≠ ⊤ := ENNReal.inv_ne_top.2 (Nat.cast_ne_zero.2 hc)
  refine ⟨fun F φ v g => ?_, fun F φ v g => ?_⟩
  · obtain ⟨h, hio⟩ := hrow.io j hj F
    have hI := (GlobalTheory.BaseChain.stepY_integrable_and_eq W hW W.P.A3.A.μ0 j hj F h _ (hrow.vP j hj) φ v g).1.smul_measure hne
    rw [← Measure.restrict_smul] at hI
    exact hI
  · obtain ⟨h, hio⟩ := hrow.io j hj F
    have e := (GlobalTheory.BaseChain.stepY_integrable_and_eq W hW W.P.A3.A.μ0 j hj F h _ (hrow.vP j hj) φ v g).2
    have hk : (GlobalTheory.BaseChain.cH W).toReal • (Nat.card (lvP W).H : ℂ) = 1 := by
      rw [Complex.real_smul, GlobalTheory.BaseChain.cH, ENNReal.toReal_inv, ENNReal.toReal_natCast, Complex.ofReal_inv, Complex.ofReal_natCast,
        inv_mul_cancel₀ (Nat.cast_ne_zero.2 hc)]
    show (∫ y in (pk W).fdY W.P.A3.A.μ0 (j + 1), thetaKO ((pk W).ωY W.P.A3.A.μ0 j) g y (pureTensorO (pk W).ψ (pk W).θ (Yc D j) (Yc D (j + 1)) (cart ((pk W).MY j)) (cart ((pk W).MY (j + 1))) (onb ((pk W).MY j)) (onb ((pk W).MY (j + 1))) ((f.row W.P.A3.A.μ0).vP j) φ) * F.1 v y ∂(GlobalTheory.BaseChain.cH W • (pk W).νY W.P.A3.A.μ0 (j + 1))) = ((f.row W.P.A3.A.μ0).io j F).1 ((pk W).ItY j φ v) g
    rw [hio, Measure.restrict_smul, integral_smul_measure]
    exact (congrArg (fun z => (GlobalTheory.BaseChain.cH W).toReal • z) e).trans (by rw [← smul_mul_assoc, hk, one_mul])
