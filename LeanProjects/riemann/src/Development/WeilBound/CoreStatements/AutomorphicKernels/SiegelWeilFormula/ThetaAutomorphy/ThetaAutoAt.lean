import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.ThetaAutomorphy.ExistsMeanAdm
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.ThetaAutomorphy.ThetaSumRationalInvariant

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.Tauto

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem thetaAuto_at (hS : GlobalTheory.Published.SiegelSetUnitary) (hP : TPar) (hT : TTheta) (d : SD σ) :
    d.μ d.D ≠ 0 ∧ d.μ d.D ≠ ⊤ ∧ ∀ Φ ∈ d.sch,
      (∀ x, IntegrableOn (fun g => thetaSum F (d.om x (d.S g Φ))) d.D d.μ) ∧ Continuous (d.I Φ) ∧
      ∀ γ ∈ rat2 σ d.Y, ∀ x, d.I Φ (γ * x) = d.I Φ x := by
  have hc := cpt hS d
  haveI := hc.cnt
  haveI := d.ok.haar
  have hom : ∀ x, ∀ Ψ ∈ d.sch, d.om x Ψ ∈ d.sch := fun x Ψ hΨ => d.ok.dbl.weil.2.1.pres x Ψ hΨ
  have hcomm : ∀ Φ ∈ d.sch, ∀ x g, d.om x (d.S g Φ) = d.S g (d.om x Φ) := fun Φ hΦ => (hT F E σ d Φ hΦ).2
  obtain ⟨Λ, hΛ, hΛv⟩ := exists_meanAdm hS hP hT d
  refine ⟨fd_ne d.ok.dom, (hc.fin d.μ d.D d.ok.haar d.ok.dom).ne, fun Φ hΦ => ⟨fun x => ?_, ?_, fun γ hγ x => ?_⟩⟩
  · simp only [hcomm Φ hΦ]
    exact intOn_S hS hP hT d (hom x Φ hΦ)
  · have e : d.I Φ = fun x => Λ (d.om x Φ) := funext fun x => by
      rw [hΛv _ (hom x Φ hΦ)]
      show PositivityTheory.SiegelWeilFormula.thetaMean d.om d.S d.μ d.D Φ x = _
      rw [PositivityTheory.SiegelWeilFormula.thetaMean, setAverage_eq]
      simp only [hcomm Φ hΦ]
    rw [e]
    exact d.ok.dbl.weil.2.1.cont Λ hΛ Φ hΦ
  · show PositivityTheory.SiegelWeilFormula.thetaMean d.om d.S d.μ d.D Φ (γ * x) = PositivityTheory.SiegelWeilFormula.thetaMean d.om d.S d.μ d.D Φ x
    simp only [PositivityTheory.SiegelWeilFormula.thetaMean, map_mul, Module.End.mul_apply]
    refine congrArg (fun f : UA σ d.A.J → ℂ => ⨍ g in d.D, f g ∂d.μ) (funext fun g => ?_)
    exact theta_sum_rational_invariant d γ hγ _ (hom x _ (d.ok.dbl.lin.pres g Φ hΦ))

theorem thetaAuto (hS : GlobalTheory.Published.SiegelSetUnitary) (hP : TPar) (hT : TTheta) : ThetaAuto :=
  fun _ _ _ _ _ _ _ _ d => thetaAuto_at hS hP hT d

end PositivityTheory.SiegelWeilFormula.Tauto

end
