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
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualFrameVacuumStepStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BiThetaOfVac
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergCombinationCommFockPolynomialVectors
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PtYAndItYOfPair
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsThetaFunOOfThetaAt
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.GEqBase
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TopStepVectorThetaStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.BaseChainTop

variable {D : D7}

theorem comb_pureTensorO {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D} (hψ : IsStdChar D ψ (-1))
    (hθ : IsInfFam θ) (sS sT BS BT) {e : WO S T →₀ ℂ} (he : IsFinComb e) {f₀ : WO S T → ℂ}
    (hf₀ : IsThetaFunO ψ S T f₀) (P) :
    comb ψ S T e (pureTensorO ψ θ S T sS sT BS BT f₀ P) = pureTensorO ψ θ S T sS sT BS BT (comb ψ S T e f₀) P := by
  let q := e.support.equivFin
  have key := (GlobalTheory.FockFiniteHeis.heis_comb_pureTensorO D ψ θ S T hψ hθ sS sT BS BT f₀ hf₀ e.support.card
    (fun i => e (q.symm i).1) (fun i => (q.symm i).1) (fun i => he _ (q.symm i).2) P).1
  have h1 : ∀ g : WO S T → (WO S T → ℂ), ∑ u ∈ e.support, e u • g u = ∑ i, e (q.symm i).1 • g (q.symm i).1 := by
    intro g
    rw [← Finset.sum_coe_sort e.support]
    exact (Equiv.sum_comp q.symm (fun u : e.support => e u.1 • g u.1)).symm
  simp only [comb]
  rw [h1, h1]
  exact key

theorem isItW_of_comb {V W : HSp D} {S S' : D.what₂.Tau → SPar} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D}
    {M : DSModel V S} {M' : DSModel W S'} {χS χT : (AE D)ˣ →* Circle}
    {ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)} (hω : IsWeilDatumO ψ V W χS χT ω) (hθ : IsInfFam θ)
    {f g : WO V W → ℂ} (hf : IsThetaFunO ψ V W f) {b : WO V W →₀ ℂ} (hb : IsFinComb b) (hg : comb ψ V W b f = g)
    {It : PolF D W.rank V.rank →ₗ[ℂ] SmT M' →ₗ[ℂ] SmT M}
    (hI : IsItW θ M M' ω (pureTensorO ψ θ V W (cart M) (cart M') (onb M) (onb M') g) It) :
    IsItW θ M M' ω (pureTensorO ψ θ V W (cart M) (cart M') (onb M) (onb M') f) It := by
  have hψ : IsStdChar D ψ (-1) := hω.std
  have hpt : ∀ φ, IsThetaFunO ψ V W (pureTensorO ψ θ V W (cart M) (cart M') (onb M) (onb M') f φ) := fun φ =>
    GlobalTheory.Chain.InnerSteps.theta_pureTensorO hψ hθ _ _ _ _ hf φ
  have hrel : ∀ φ, comb ψ V W b (pureTensorO ψ θ V W (cart M) (cart M') (onb M) (onb M') f φ) =
      pureTensorO ψ θ V W (cart M) (cart M') (onb M) (onb M') g φ := fun φ => by
    rw [← hg]
    exact comb_pureTensorO hψ hθ _ _ _ _ hb hf φ
  have hcomm : ∀ a ∈ GinfC V, ∀ a' ∈ GinfC W, ∀ φ,
      ω (a, a') (pureTensorO ψ θ V W (cart M) (cart M') (onb M) (onb M') g φ) =
        comb ψ V W b (ω (a, a') (pureTensorO ψ θ V W (cart M) (cart M') (onb M) (onb M') f φ)) := fun a ha a' ha' φ => by
    rw [← hrel, GlobalTheory.FrComb.om_comb hω ha ha' hb (hpt φ)]
  refine ⟨hI.ne, hI.bdd, fun τ x hx φ φ' h v => ?_, fun τ X hX φ φ' hd v => ?_, fun τ y hy φ φ' v v' h hv => ?_,
    fun τ X hX φ φ' v v' hd hD => ?_⟩
  · refine hI.eqK τ x hx φ φ' ?_ v
    rw [hcomm _ (Formalism.IndefR.Eqv.Act.atTau_mem θ τ x) 1 (one_mem _) φ, ← h, hrel]
  · refine hI.eqg τ X hX φ φ' (fun z => ?_) v
    have e1 : (fun t : ℝ => ω (oneP θ V τ X t, 1) (pureTensorO ψ θ V W (cart M) (cart M') (onb M) (onb M') g φ) z) =
        fun t => ∑ x ∈ b.support, b x * (ψ (symplOH V W z x) *
          ω (oneP θ V τ X t, 1) (pureTensorO ψ θ V W (cart M) (cart M') (onb M) (onb M') f φ) (z + x)) := funext fun t => by
      rw [hcomm _ (Formalism.IndefR.Eqv.Act.oneP_mem θ τ X t) 1 (one_mem _) φ, GlobalTheory.FrComb.comb_apply]
    rw [e1, ← hrel φ', GlobalTheory.FrComb.comb_apply]
    exact HasDerivAt.fun_sum fun x _ => ((hd (z + x)).const_mul _).const_mul _
  · refine hI.invK τ y hy φ φ' v v' ?_ hv
    rw [hcomm 1 (one_mem _) _ (Formalism.IndefR.Eqv.Act.atTau_mem θ τ y) φ, ← h, hrel]
  · refine hI.invg τ X hX φ φ' v v' (fun z => ?_) hD
    have e1 : (fun t : ℝ => ω (1, oneP θ W τ X t) (pureTensorO ψ θ V W (cart M) (cart M') (onb M) (onb M') g φ) z) =
        fun t => ∑ x ∈ b.support, b x * (ψ (symplOH V W z x) *
          ω (1, oneP θ W τ X t) (pureTensorO ψ θ V W (cart M) (cart M') (onb M) (onb M') f φ) (z + x)) := funext fun t => by
      rw [hcomm 1 (one_mem _) _ (Formalism.IndefR.Eqv.Act.oneP_mem θ τ X t) φ, GlobalTheory.FrComb.comb_apply]
    rw [e1, ← hrel φ', GlobalTheory.FrComb.comb_apply]
    exact HasDerivAt.fun_sum fun x _ => ((hd (z + x)).const_mul _).const_mul _

end GlobalTheory.BaseChainTop

namespace GlobalTheory.BaseChainTop

theorem theta_and_it : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex) (u : D.what₂.Word) (f : FamCh W u), PkHyp W → f.RowOK → ∀ j (h : j + 2 * 0 + 2 = D.R.m), (∀ φ, IsThetaFunO (GlobalTheory.BaseChain.com W).ψ (GlobalTheory.BaseChain.stageY W (j + 1)).V (GlobalTheory.BaseChain.stageX W).V ((GlobalTheory.BaseChain.stepX f j h).pt φ)) ∧ IsItW (GlobalTheory.BaseChain.com W).θ (GlobalTheory.BaseChain.stageY W (j + 1)).M (GlobalTheory.BaseChain.stageX W).M (GlobalTheory.BaseChain.stepX f j h).ω (GlobalTheory.BaseChain.stepX f j h).pt (GlobalTheory.BaseChain.stepX f j h).It := by
  intro D L hT Gi Gl Kc Yd cX ex W u f hP hR j h
  have hC := Formalism.IndefR.Links.RealDat3.characterisation_of_weak W.Q.charW hP.ex
  have hvT := (hR.row W.P.A3.A.μ0).vT j h
  have hθ : IsInfFam (pk W).θ := hvT.1.2.inf
  have hth : IsThetaFunO (pk W).ψ (Yc D (j + 1)) D.sp.X' ((f.row W.P.A3.A.μ0).vT j h) :=
    GlobalTheory.VecTheta.isThetaFunO_stepVec hvT
  have key : ∀ n (e : D.R.m - 1 = n),
      IsWeilDatumO (pk W).ψ (Yc D n) D.sp.X' (Lift.chrStep ((pk W).toLevCh.mu W.P.A3.A.μ0) (pk W).eta D.R.m).1
        (Lift.chrStep ((pk W).toLevCh.mu W.P.A3.A.μ0) (pk W).eta D.R.m).2
        (Eq.rec (motive := fun n _ => Om (Yc D n) D.sp.X') ((pk W).ωX W.P.A3.A.μ0) e) ∧
      IsItW (pk W).θ ((pk W).MY n) (pk W).MX (Eq.rec (motive := fun n _ => Om (Yc D n) D.sp.X') ((pk W).ωX W.P.A3.A.μ0) e)
        (pureTensorO (pk W).ψ (pk W).θ (Yc D n) D.sp.X' (cart ((pk W).MY n)) (cart (pk W).MX) (onb ((pk W).MY n))
          (onb (pk W).MX) (Eq.rec (motive := fun n _ => WO (Yc D n) D.sp.X' → ℂ) ((pk W).vX W.P.A3.A.μ0) e))
        (Eq.rec (motive := fun n _ => PolF D D.sp.X'.rank (Yc D n).rank →ₗ[ℂ] SmT (pk W).MX →ₗ[ℂ] SmT ((pk W).MY n))
          (pk W).ItX e) := by
    intro n e
    subst e
    exact ⟨hC.chain.ωX _, hC.chain.ItX _⟩
  obtain ⟨hW', hI'⟩ := key (j + 1) (idx_top h)
  obtain ⟨b, hb, hbv⟩ := GlobalTheory.T.top_step_vector_theta W hP j h _ hvT
  exact ⟨fun φ => GlobalTheory.Chain.InnerSteps.theta_pureTensorO hW'.std hθ _ _ _ _ hth φ, isItW_of_comb hW' hθ hth hb hbv hI'⟩

end GlobalTheory.BaseChainTop
