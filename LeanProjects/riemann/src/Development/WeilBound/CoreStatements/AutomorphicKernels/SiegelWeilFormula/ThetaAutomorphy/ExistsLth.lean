import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.ThetaAutomorphy.ThetaSumSRat
import Development.WeilBound.ThetaLifts.LatticeBasics.FdEqZero
import Development.WeilBound.ThetaLifts.FrameEstimates.GrpTop
import Development.WeilBound.ThetaLifts.FrameEstimates.BlockForm
import Development.WeilBound.ThetaLifts.FrameEstimates.SiegelAll
import Development.WeilBound.ThetaLifts.FrameEstimates.FundamentalDomainFiniteVolume
import Development.WeilBound.ThetaLifts.CartanFactorisation.Unimod
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdmittedFormEqAdelicThetaDistributionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzMapBarrelledSpaceStatement

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.Tauto

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem cpt (hS : GlobalTheory.Published.SiegelSetUnitary) (d : SD σ) : Cpt σ d.A.J := by
  have h := cptAll_of PositivityTheory.ThKEst.grpTop_of PositivityTheory.ThKEst.epsOf_of (PositivityTheory.ThKEst.siegelAll_of hS)
    PositivityTheory.ThKEst.finVolU PositivityTheory.ThKF.unimodularity_holds
  rcases d.ok.sign with ⟨hA, -⟩ | ⟨hA, -⟩
  · exact h F E σ d.B d.m d.A d.r d.s d.ok.good (Or.inl hA) d.ok.aniso
  · exact h F E σ d.B d.m d.A d.r d.s d.ok.good (Or.inr hA) d.ok.aniso

theorem exists_lth (d : SD σ) : ∃ l ∈ (adeleClass F).adm d.κ, ∀ Φ ∈ d.sch, l Φ = thetaSum F Φ :=
  GlobalTheory.T.exists_admitted_form_eq_adelicThetaDistribution F d.κ

theorem cont_S (d : SD σ) {Ψ : d.Fn} (hΨ : Ψ ∈ d.sch) : Continuous fun g : UA σ d.A.J => thetaSum F (d.S g Ψ) := by
  obtain ⟨l, hl, hlθ⟩ := exists_lth d
  exact (d.ok.dbl.lin.cont l hl Ψ hΨ).congr fun g => hlθ _ (d.ok.dbl.lin.pres g Ψ hΨ)

theorem inv_S (hP : TPar) (hT : TTheta) (d : SD σ) {Ψ : d.Fn} (hΨ : Ψ ∈ d.sch) :
    ∀ γ ∈ ratU σ d.A.J, ∀ g, thetaSum F (d.S (γ * g) Ψ) = thetaSum F (d.S g Ψ) := fun γ hγ g => by
  rw [map_mul, Module.End.mul_apply, thetaSum_S_rat hP hT d hγ (d.ok.dbl.lin.pres g Ψ hΨ)]

theorem bdd_S (hS : GlobalTheory.Published.SiegelSetUnitary) (hP : TPar) (hT : TTheta) (d : SD σ) {Ψ : d.Fn} (hΨ : Ψ ∈ d.sch) :
    ∃ C : ℝ, ∀ g, ‖thetaSum F (d.S g Ψ)‖ ≤ C :=
  (cpt hS d).bdd (cont_S d hΨ) (inv_S hP hT d hΨ)

theorem intOn_S (hS : GlobalTheory.Published.SiegelSetUnitary) (hP : TPar) (hT : TTheta) (d : SD σ) {Ψ : d.Fn} (hΨ : Ψ ∈ d.sch) :
    IntegrableOn (fun g => thetaSum F (d.S g Ψ)) d.D d.μ := by
  obtain ⟨C, hC⟩ := bdd_S hS hP hT d hΨ
  exact Measure.integrableOn_of_bounded (M := C) ((cpt hS d).fin d.μ d.D d.ok.haar d.ok.dom).ne
    (cont_S d hΨ).aestronglyMeasurable (Eventually.of_forall hC)

end PositivityTheory.SiegelWeilFormula.Tauto

end
