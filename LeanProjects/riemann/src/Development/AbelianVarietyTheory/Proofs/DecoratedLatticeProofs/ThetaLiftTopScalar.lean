import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FrameTopAlt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RatioOKOfRootOfUnity
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExtraColumnRangeMembershipStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EasyInputs
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ChainCompositeLiftIntertwinesFiniteGroupActions
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.PureTensorLIntertwine
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChainStepVectorsAndAdjointVectorsAreTheta
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Fam.IoTop

theorem liftS_smul_domain {D : D7} {S T : HSp D} (om : Om S T) (ν μ : Measure (GA D T)) (c : ENNReal) (hc0 : c ≠ 0)
    (hμ : μ = c • ν) (hH : μ.IsHaarMeasure) {𝓕 𝓖 : Set (GA D T)} (h₁ : IsFundamentalDomain (GQ T) 𝓕 μ)
    (h₂ : IsFundamentalDomain (GQ T) 𝓖 ν) (G : GA D T → ℂ) (φ : WO S T → ℂ) (x : GA D S)
    (hinv : ∀ γ ∈ GQ T, ∀ y, om (x, γ * y) φ 0 * G (γ * y) = om (x, y) φ 0 * G y) :
    liftS om μ 𝓕 G φ x = (c.toReal : ℂ) • liftS om ν 𝓖 G φ x := by
  have : IsTopologicalGroup (GA D T) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
  have : BorelSpace (GA D T) := ⟨rfl⟩
  have : Countable (GQ T) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.countableGamma D.sp.cm.sig T.gram
  have h₂' : IsFundamentalDomain (GQ T) 𝓖 μ := h₂.mono (hμ ▸ Measure.smul_absolutelyContinuous)
  rw [liftS_apply, liftS_apply, h₁.setIntegral_eq h₂' fun γ y => hinv γ.1 γ.2 y, hμ, Measure.restrict_smul,
    integral_smul_measure, Complex.real_smul]
  rfl

theorem omT_weil {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D}
    {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex)
    (hc : W.Q.Rl.Char3 W.Q.F) (t : W.P.T) (j : ℕ) (h : j + 2 * 0 + 2 = D.R.m) :
    IsWeilDatumO (pk W).ψ (Yc D (j + 1)) D.sp.X' (Lift.chrStep ((pk W).toLevCh.mu t) (pk W).eta D.R.m).1
      (Lift.chrStep ((pk W).toLevCh.mu t) (pk W).eta D.R.m).2 (omT (pk W) t j h) := by
  have key : ∀ n (e : D.R.m - 1 = n), IsWeilDatumO (pk W).ψ (Yc D n) D.sp.X' (Lift.chrStep ((pk W).toLevCh.mu t) (pk W).eta D.R.m).1
      (Lift.chrStep ((pk W).toLevCh.mu t) (pk W).eta D.R.m).2
      (Eq.rec (motive := fun n _ => Om (Yc D n) D.sp.X') ((pk W).ωX t) e) := by
    rintro n rfl
    exact hc.chain.ωX t
  exact key (j + 1) (idx_top h)

theorem smul_const (a b : ℝ) (H z : ℂ) (hab : 0 ≤ a * b) :
    ((ENNReal.ofReal (a * b)).toReal : ℂ) • (H • z) = (H * (a : ℂ) * (b : ℂ)) • z := by
  rw [ENNReal.toReal_ofReal hab, smul_eq_mul, smul_eq_mul, smul_eq_mul, Complex.ofReal_mul]
  ring

end GlobalTheory.Fam.IoTop

set_option maxHeartbeats 1000000 in
open GlobalTheory.Fam.IoTop in
theorem GlobalTheory.Fam.ioT_lift : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex) (u : D.what₂.Word), PkHyp W → ∀ f : FamCh W u, f.RowOK → ∀ t j (h : j + 2 * 0 + 2 = D.R.m) (F : (f.t t).CT) P v, liftS ((f.t t).omT j h) f.c.volT.μ f.c.volT.𝓕 (F.1 v) ((f.t t).ptT j h P) = (f.t t).cI (j + 1) • ((f.t t).ioT j h F).1 (f.c.ItT j h P v) := by
  intro D L hT Gi Gl Kc Yd cX ex W u hP f hR t j h F P v
  have hc := hP.bot.hyp.2.2.2.1
  obtain ⟨h', -, hL⟩ := GlobalTheory.T.extra_column_range_membership W u hP f.g t j h F
  have key := hL ((f.row t).vT j h) ((hR.row t).vT j h) P v
  obtain ⟨h'', hio⟩ := (hR.row t).ioT j h F
  have hm := hR.meas.volT t
  rw [show D.R.m - 1 = j + 1 by omega, show f.g.κ D.R.m = f.g.κ (j + 1 + 1) from congrArg f.g.κ (by omega)] at hm
  have hom := omT_weil W hc t j h
  have hth : IsThetaFunO (pk W).ψ (Yc D (j + 1)) D.sp.X' (pureTensorO (pk W).ψ (pk W).θ (Yc D (j + 1)) D.sp.X'
      (cart ((pk W).MY (j + 1))) (cart (pk W).MX) (onb ((pk W).MY (j + 1))) (onb (pk W).MX) ((f.row t).vT j h) P) := by
    obtain ⟨cY, hcY⟩ := hc.lev.βY (j + 1) (by omega)
    obtain ⟨cX', hcX⟩ := hc.lev.βX
    have hf := (GlobalTheory.VecTheta.vecThetaSD D).1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      (GlobalTheory.Mem.EasyInputs.selfDualOK D _ _ _ _ hcY) (GlobalTheory.Mem.EasyInputs.selfDualOK D _ _ _ _ hcX) hcY.1 hcX.1
      ((hR.row t).vT j h)
    have e0 : ∀ (V : HSp D) (ρ : D.what₂.Tau), compAt (pk W).θ ρ (Formalism.L2.Theta.mt V 1) = 1 := fun V ρ => by
      have : Formalism.L2.Theta.mt V 1 = 1 := by simp [Formalism.L2.Theta.mt]
      rw [this]
      exact Matrix.map_one _ (by simp) (by simp)
    exact (GlobalTheory.OrientedHeis.om_pureTensorO D _ _ _ _ _ _ _ hom hc.models.inf (cart ((pk W).MY (j + 1))) (cart ((pk W).MY (j + 1)))
      (onb ((pk W).MY (j + 1))) (onb ((pk W).MY (j + 1))) (cart (pk W).MX) (cart (pk W).MX) (onb (pk W).MX) (onb (pk W).MX) 1 1
      (fun ρ => by rw [e0, Matrix.mul_one, Matrix.one_mul]) (fun ρ => by rw [e0, Matrix.mul_one, Matrix.one_mul]) (fun ρ => by rw [e0, Matrix.one_mul]) (fun ρ => by rw [e0, Matrix.one_mul]) _ hf P).1
  have hκ := hR.meas.κ (j + 1 + 1)
  have hvl : 0 ≤ volLev (pk W) f.g t (j + 1) := by unfold volLev; split_ifs <;> exact ENNReal.toReal_nonneg
  have hc0 : ENNReal.ofReal (f.g.κ (j + 1 + 1) * volLev (pk W) f.g t (j + 1)) ≠ 0 := by
    have := (hR.meas.cIOf_ne_zero (lvP W) t (j + 1) (by omega))
    unfold cIOf at this
    intro h0
    rw [ENNReal.ofReal_eq_zero] at h0
    refine this ?_
    have : f.g.κ (j + 1 + 1) * volLev (pk W) f.g t (j + 1) = 0 := le_antisymm h0 (mul_nonneg hκ.le hvl)
    rw [mul_assoc, ← Complex.ofReal_mul, this, Complex.ofReal_zero, mul_zero]
  have hfd := (hc.models.νX t).2
  show liftS (omT (pk W) t j h) f.g.volT.μ f.g.volT.𝓕 (F.1 v) _ = cIOf (pk W) (lvP W) f.g t (j + 1) • _
  funext x
  have e1 := liftS_smul_domain (omT (pk W) t j h) ((pk W).νX t) f.g.volT.μ _ hc0 hm f.g.volT.haar f.g.volT.fund hfd
    (F.1 v) (pureTensorO (pk W).ψ (pk W).θ (Yc D (j + 1)) D.sp.X' (cart ((pk W).MY (j + 1))) (cart (pk W).MX)
      (onb ((pk W).MY (j + 1))) (onb (pk W).MX) ((f.row t).vT j h) P) x (fun γ hγ y => by
        have a1 : (omT (pk W) t j h) (x, γ * y) = (omT (pk W) t j h) (1, γ) * (omT (pk W) t j h) (x, y) := by
          rw [← map_mul, Prod.mk_mul_mk, one_mul]
        rw [a1, Module.End.mul_apply, hom.om_aut 1 (one_mem _) γ hγ _ (hom.om_pres _ _ hth),
          GlobalTheory.ChainLiftEquiv.multT_left _ _ _ _ F.1 F.2 v γ hγ y])
  have hio' : (((f.t t).ioT j h) F).1 = ((ioXT (pk W) t j h) ⟨F.1, h'⟩).1 := hio
  have e2 : (((f.t t).ioT j h) F).1 (((f.c.ItT j h) P) v) x = ((ioXT (pk W) t j h) ⟨F.1, h'⟩).1 (((f.c.ItT j h) P) v) x :=
    congrFun (LinearMap.congr_fun hio' _) x
  have e3 := congrFun key x
  rw [Pi.smul_apply] at e3
  exact e1.trans ((congrArg _ e3).trans ((smul_const _ _ _ _ (mul_nonneg hκ.le hvl)).trans (congrArg _ e2.symm)))

end
