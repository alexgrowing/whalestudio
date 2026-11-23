import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaLiftTopScalar
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RealPack
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TrueW
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TopReadAt
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IndefRRealT
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.STiesR
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LinkedFamiliesFixedValues
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LinkedFamiliesKernelFrame
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LayerTwoFamilyClass
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ColJoinSOfSTiesR
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FormsAtZero
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IoXTLevelPStatement

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.Fam.IoTop
theorem omT_weil_chr {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D}
    {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex)
    (hc : W.Q.Rl.Char3 W.Q.F) (t : W.P.T) (j : ℕ) (h : j + 2 * 0 + 2 = D.R.m) :
    IsWeilDatumO (_root_.GlobalTheory.Fam.pk_z W).ψ (Yc D (j + 1)) D.sp.X' (Lift.chrStep ((_root_.GlobalTheory.Fam.pk_z W).toLevCh.mu t) (_root_.GlobalTheory.Fam.pk_z W).eta D.R.m).1
      (Lift.chrStep ((_root_.GlobalTheory.Fam.pk_z W).toLevCh.mu t) (_root_.GlobalTheory.Fam.pk_z W).eta D.R.m).2 (omT (_root_.GlobalTheory.Fam.pk_z W) t j h) := by
  have key : ∀ n (e : D.R.m - 1 = n), IsWeilDatumO (_root_.GlobalTheory.Fam.pk_z W).ψ (Yc D n) D.sp.X' (Lift.chrStep ((_root_.GlobalTheory.Fam.pk_z W).toLevCh.mu t) (_root_.GlobalTheory.Fam.pk_z W).eta D.R.m).1
      (Lift.chrStep ((_root_.GlobalTheory.Fam.pk_z W).toLevCh.mu t) (_root_.GlobalTheory.Fam.pk_z W).eta D.R.m).2
      (Eq.rec (motive := fun n _ => Om (Yc D n) D.sp.X') ((_root_.GlobalTheory.Fam.pk_z W).ωX t) e) := by
    rintro n rfl
    exact hc.chain.ωX t
  exact key (j + 1) (idx_top h)
end GlobalTheory.Fam.IoTop
set_option maxHeartbeats 1000000 in
open GlobalTheory.Fam.IoTop in
theorem GlobalTheory.Fam.liftS_ptT_eq_cI_smul_ioT : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (u : D.what₂.Word), _root_.GlobalTheory.Fam.PackageHypotheses W → ∀ f : _root_.GlobalTheory.Fam.FamilyCharacter W u, f.RowOK → ∀ t j (h : j + 2 * 0 + 2 = D.R.m) (F : (f.t t).CT) P v, liftS ((f.t t).omT j h) f.c.volT.μ f.c.volT.𝓕 (F.1 v) ((f.t t).ptT j h P) = (f.t t).cI (j + 1) • ((f.t t).ioT j h F).1 (f.c.ItT j h P v) := by
  intro D L hT Gi Gl Kc Yd cX ex W u hP f hR t j h F P v
  have hc := hP.bot.hyp.2.2.2.1
  obtain ⟨h', -, hL⟩ := _root_.GlobalTheory.T.extra_column_range_membership_alt W u hP f.g t j h F
  have key := hL ((f.row t).vT j h) ((hR.row t).vT j h) P v
  obtain ⟨h'', hio⟩ := (hR.row t).ioT j h F
  have hm := hR.meas.volT t
  rw [show D.R.m - 1 = j + 1 by omega, show f.g.κ D.R.m = f.g.κ (j + 1 + 1) from congrArg f.g.κ (by omega)] at hm
  have hom := _root_.GlobalTheory.Fam.IoTop.omT_weil_chr W hc t j h
  have hth : IsThetaFunO (_root_.GlobalTheory.Fam.pk_z W).ψ (Yc D (j + 1)) D.sp.X' (pureTensorO (_root_.GlobalTheory.Fam.pk_z W).ψ (_root_.GlobalTheory.Fam.pk_z W).θ (Yc D (j + 1)) D.sp.X'
      (cart ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1))) (cart (_root_.GlobalTheory.Fam.pk_z W).MX) (onb ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1))) (onb (_root_.GlobalTheory.Fam.pk_z W).MX) ((f.row t).vT j h) P) := by
    obtain ⟨cY, hcY⟩ := hc.lev.βY (j + 1) (by omega)
    obtain ⟨cX', hcX⟩ := hc.lev.βX
    have hf := (GlobalTheory.VecTheta.vecThetaSD D).1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      (GlobalTheory.Mem.EasyInputs.selfDualOK D _ _ _ _ hcY) (GlobalTheory.Mem.EasyInputs.selfDualOK D _ _ _ _ hcX) hcY.1 hcX.1
      ((hR.row t).vT j h)
    have e0 : ∀ (V : HSp D) (ρ : D.what₂.Tau), compAt (_root_.GlobalTheory.Fam.pk_z W).θ ρ (Formalism.L2.Theta.mt V 1) = 1 := fun V ρ => by
      have : Formalism.L2.Theta.mt V 1 = 1 := by simp [Formalism.L2.Theta.mt]
      rw [this]
      exact Matrix.map_one _ (by simp) (by simp)
    exact (GlobalTheory.OrientedHeis.om_pureTensorO D _ _ _ _ _ _ _ hom hc.models.inf (cart ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1))) (cart ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1)))
      (onb ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1))) (onb ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1))) (cart (_root_.GlobalTheory.Fam.pk_z W).MX) (cart (_root_.GlobalTheory.Fam.pk_z W).MX) (onb (_root_.GlobalTheory.Fam.pk_z W).MX) (onb (_root_.GlobalTheory.Fam.pk_z W).MX) 1 1
      (fun ρ => by rw [e0, Matrix.mul_one, Matrix.one_mul]) (fun ρ => by rw [e0, Matrix.mul_one, Matrix.one_mul]) (fun ρ => by rw [e0, Matrix.one_mul]) (fun ρ => by rw [e0, Matrix.one_mul]) _ hf P).1
  have hκ := hR.meas.κ (j + 1 + 1)
  have hvl : 0 ≤ volLev (_root_.GlobalTheory.Fam.pk_z W) f.g t (j + 1) := by unfold volLev; split_ifs <;> exact ENNReal.toReal_nonneg
  have hc0 : ENNReal.ofReal (f.g.κ (j + 1 + 1) * volLev (_root_.GlobalTheory.Fam.pk_z W) f.g t (j + 1)) ≠ 0 := by
    have := (hR.meas.cIOf_ne_zero (_root_.GlobalTheory.Fam.complexLevelStructure W) t (j + 1) (by omega))
    unfold cIOf at this
    intro h0
    rw [ENNReal.ofReal_eq_zero] at h0
    refine this ?_
    have : f.g.κ (j + 1 + 1) * volLev (_root_.GlobalTheory.Fam.pk_z W) f.g t (j + 1) = 0 := le_antisymm h0 (mul_nonneg hκ.le hvl)
    rw [mul_assoc, ← Complex.ofReal_mul, this, Complex.ofReal_zero, mul_zero]
  have hfd := (hc.models.νX t).2
  show liftS (omT (_root_.GlobalTheory.Fam.pk_z W) t j h) f.g.volT.μ f.g.volT.𝓕 (F.1 v) _ = cIOf (_root_.GlobalTheory.Fam.pk_z W) (_root_.GlobalTheory.Fam.complexLevelStructure W) f.g t (j + 1) • _
  funext x
  have e1 := liftS_smul_domain (omT (_root_.GlobalTheory.Fam.pk_z W) t j h) ((_root_.GlobalTheory.Fam.pk_z W).νX t) f.g.volT.μ _ hc0 hm f.g.volT.haar f.g.volT.fund hfd
    (F.1 v) (pureTensorO (_root_.GlobalTheory.Fam.pk_z W).ψ (_root_.GlobalTheory.Fam.pk_z W).θ (Yc D (j + 1)) D.sp.X' (cart ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1))) (cart (_root_.GlobalTheory.Fam.pk_z W).MX)
      (onb ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1))) (onb (_root_.GlobalTheory.Fam.pk_z W).MX) ((f.row t).vT j h) P) x (fun γ hγ y => by
        have a1 : (omT (_root_.GlobalTheory.Fam.pk_z W) t j h) (x, γ * y) = (omT (_root_.GlobalTheory.Fam.pk_z W) t j h) (1, γ) * (omT (_root_.GlobalTheory.Fam.pk_z W) t j h) (x, y) := by
          rw [← map_mul, Prod.mk_mul_mk, one_mul]
        rw [a1, Module.End.mul_apply, hom.om_aut 1 (one_mem _) γ hγ _ (hom.om_pres _ _ hth),
          GlobalTheory.ChainLiftEquiv.multT_left _ _ _ _ F.1 F.2 v γ hγ y])
  have hio' : (((f.t t).ioT j h) F).1 = ((ioXT (_root_.GlobalTheory.Fam.pk_z W) t j h) ⟨F.1, h'⟩).1 := hio
  have e2 : (((f.t t).ioT j h) F).1 (((f.c.ItT j h) P) v) x = ((ioXT (_root_.GlobalTheory.Fam.pk_z W) t j h) ⟨F.1, h'⟩).1 (((f.c.ItT j h) P) v) x :=
    congrFun (LinearMap.congr_fun hio' _) x
  have e3 := congrFun key x
  rw [Pi.smul_apply] at e3
  exact e1.trans ((congrArg _ e3).trans ((smul_const _ _ _ _ (mul_nonneg hκ.le hvl)).trans (congrArg _ e2.symm)))
end
end
