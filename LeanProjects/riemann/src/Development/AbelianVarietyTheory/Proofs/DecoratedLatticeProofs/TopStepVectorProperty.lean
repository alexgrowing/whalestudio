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
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaChainLastStepIntertwinesMatchedHecke
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EasyInputs
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChainStepVectorsAndAdjointVectorsAreTheta
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PtYAndItYOfPair
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MultValueLeftContLevel
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.BaseChain

theorem multT_apply_continuous {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (θ : InfFam D) (M : DSModel V S)
    (J : Set (GA D V)) (χ : GA D V → ℂ) (u : SmT M →ₗ[ℂ] (GA D V → ℂ)) (hu : u ∈ MultT θ M J χ) (v : SmT M) :
    Continuous (u v) := by
  have h1 := (mem_multT θ M J χ u).1 hu
  induction v using PiTensorProduct.induction_on with
  | smul_tprod r f =>
    have h2 : Continuous (u (PiTensorProduct.tprod ℂ f)) := (GlobalTheory.mult_value_left_cont_level θ M J χ _ h1 f).2.1
    rw [map_smul]
    exact h2.const_smul r
  | add x y hx hy =>
    rw [map_add]
    exact hx.add hy

theorem multT_apply_left {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (θ : InfFam D) (M : DSModel V S)
    (J : Set (GA D V)) (χ : GA D V → ℂ) (u : SmT M →ₗ[ℂ] (GA D V → ℂ)) (hu : u ∈ MultT θ M J χ) (v : SmT M) :
    ∀ γ ∈ GQ V, ∀ h, u v (γ * h) = u v h := by
  intro γ hγ h
  have h1 := (mem_multT θ M J χ u).1 hu
  induction v using PiTensorProduct.induction_on with
  | smul_tprod r f =>
    have h2 : u (PiTensorProduct.tprod ℂ f) (γ * h) = u (PiTensorProduct.tprod ℂ f) h :=
      (GlobalTheory.mult_value_left_cont_level θ M J χ _ h1 f).1 γ hγ h
    rw [map_smul, Pi.smul_apply, Pi.smul_apply, h2]
  | add x y hx hy =>
    rw [map_add, Pi.add_apply, Pi.add_apply, hx, hy]

theorem weil_transport {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {T : HSp D} {a b : (AE D)ˣ →* Circle}
    (ω : Om (Yc D (D.R.m - 1)) T) (hω : IsWeilDatumO ψ _ _ a b ω) :
    ∀ n (e : D.R.m - 1 = n), IsWeilDatumO ψ (Yc D n) T a b (Eq.rec (motive := fun n _ => Om (Yc D n) T) ω e) := by
  rintro n rfl
  exact hω

theorem lastStep_integrableOn : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex), PkHyp W → ∀ j (h : j + 2 * 0 + 2 = D.R.m) v, IsStepVecOf (pk W).ψ (pk W).θ (Yc D (j + 1)) D.sp.X' (cart ((pk W).MY (j + 1))) (cart (pk W).MX) ((pk W).ΛY (j + 1)) (pk W).ΛX ((pk W).βY (j + 1)) (pk W).βX ((pk W).datYt W.P.A3.A.μ0 (j + 1) (lvP W)) ((pk W).chi D.R.m) ((pk W).Q W.P.A3.A.μ0) ((pk W).xiR W.P.A3.A.μ0) (vacT (pk W) j h) v → ∀ (F : CXP (pk W) (lvP W) W.P.A3.A.μ0) Q x g, IntegrableOn (fun y => thetaKO (omT (pk W) W.P.A3.A.μ0 j h) g y (pureTensorO (pk W).ψ (pk W).θ (Yc D (j + 1)) D.sp.X' (cart ((pk W).MY (j + 1))) (cart (pk W).MX) (onb ((pk W).MY (j + 1))) (onb (pk W).MX) v Q) * F.1 x y) ((pk W).fdX W.P.A3.A.μ0) ((pk W).νX W.P.A3.A.μ0) := by
  intro D L hT Gi Gl Kc Yd cX ex W hP j h v hv F Q x g
  have hC := hP.bot.hyp.2.2.2.1
  have hω : IsWeilDatumO (pk W).ψ (Yc D (j + 1)) D.sp.X' _ _ (omT (pk W) W.P.A3.A.μ0 j h) :=
    weil_transport ((pk W).ωX W.P.A3.A.μ0) (hC.chain.ωX W.P.A3.A.μ0) (j + 1) (idx_top h)
  obtain ⟨c1, hc1⟩ := hC.lev.βY (j + 1) (by omega)
  obtain ⟨c2, hc2⟩ := hC.lev.βX
  have hv' : IsThetaFunO (pk W).ψ (Yc D (j + 1)) D.sp.X' v :=
    (GlobalTheory.VecTheta.vecThetaSD D).1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      (GlobalTheory.Mem.EasyInputs.selfDualOK D _ _ _ _ hc1) (GlobalTheory.Mem.EasyInputs.selfDualOK D _ _ _ _ hc2) hc1.1 hc2.1 hv
  have hf := GlobalTheory.Chain.InnerSteps.theta_pureTensorO hω.std hC.models.inf (cart ((pk W).MY (j + 1))) (onb ((pk W).MY (j + 1)))
    (cart (pk W).MX) (onb (pk W).MX) hv' Q
  have hν := hC.models.νX W.P.A3.A.μ0
  have key := GlobalTheory.Hk3.StepX.integ_X hω hf (F.1 x)
    (multT_apply_continuous _ _ _ _ F.1 F.2 x) (multT_apply_left _ _ _ _ F.1 F.2 x) _ hν.1.1 _ hν.2 g 1
  simpa only [mul_one] using key

end GlobalTheory.BaseChain
