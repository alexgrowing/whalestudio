import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DblApply
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.WeilSiegelFormulaUnitary
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IntegrandPeriodic
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrameOfFst
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SiegelWeilDoublingProductRationalTranslateEqFramStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegralHermitianAdjointCovolOnePeriodicEqStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsDoubledLagrangianOfRationalUnitaryFrameStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DoubledLagrangianEqIffSiegelParabolicCosetStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsRationalUnitaryDoubledLagrangianFrameWittStatement

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open GlobalTheory.RawLift
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SWLagTerms

variable {D : D7}

theorem rat_of_mem (V : HSp D) (γ : GA D V) (h : γ ∈ GQ V) :
    ∃ g₀ : Matrix (Fin V.rank) (Fin V.rank) D.host.E, Formalism.L2.Theta.mt V γ = g₀.map (incA D) := by
  obtain ⟨g, -, hg⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 h)
  exact ⟨g.1, (congrArg Units.val hg).symm⟩

theorem integral_eq {ψ : AddChar (AF D.host.F) ℂ} {V W : HSp D} {χV χW : (AE D)ˣ →* Circle}
    {om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)} {νV : Measure (GA D V)} {𝓗 : Set (GA D V)}
    {νW : Measure (GA D W)} {𝓖 : Set (GA D W)} {μ : Measure (WO V W)} {𝓕 : Set (WO V W)}
    {fr : Lag W → Matrix (Fin W.rank) (Fin W.rank) D.host.E × Matrix (Fin W.rank) (Fin W.rank) D.host.E}
    (hS : SWSetup ψ V W χV χW om νV 𝓗 νW 𝓖 μ 𝓕 fr) {f₁ f₂ : WO V W → ℂ}
    (h₁ : IsThetaFunO ψ V W f₁) (h₂ : IsThetaFunO ψ V W f₂) (ν : Measure (Mx D V.rank W.rank))
    (𝓖' : Set (Mx D V.rank W.rank)) (hν : IsCovolOne (ratL V W) ν 𝓖') (γ : GA D (GlobalTheory.Doubling.dblSp W))
    (g₀ : Matrix (Fin (W.rank + W.rank)) (Fin (W.rank + W.rank)) D.host.E)
    (hγ : Formalism.L2.Theta.mt (GlobalTheory.Doubling.dblSp W) γ = g₀.map (incA D)) (Y : Lag W)
    (hY : IsLagFrame W Y (frameOf W g₀)) :
    ∫ y in 𝓖', GlobalTheory.SWPairProof.dbl V W f₁ f₂ (actO (GlobalTheory.Doubling.dblSp W) V γ⁻¹ 1 (GlobalTheory.SiegelFormula.lagr W V y)) ∂ν =
      lagTerm μ 𝓕 (frameOf W g₀) f₁ f₂ := by
  have hψ : ∀ x, ‖ψ x‖ = 1 := hS.weil.std.1.2.1
  simp_rw [GlobalTheory.T.siegelWeilDoublingProduct_rational_translate_eq_frame D V W f₁ f₂ γ g₀ hγ]
  unfold lagTerm
  exact GlobalTheory.T.integral_hermitianAdjoint_covolOne_periodic_eq D V W ν 𝓖' μ 𝓕 hν hS.covol
    (fun u => f₁ (ratMul (frameOf W g₀).1 u) * star (f₂ (ratMul (frameOf W g₀).2 u)))
    (fun c u => GlobalTheory.RawLift.Model.integrand_periodic hψ hY h₁ h₂ c u)

theorem classes (W : HSp D) :
    ∃ e : GlobalTheory.Eis.Cosets (GlobalTheory.Doubling.siegel W) (GQ (GlobalTheory.Doubling.dblSp W)) ≃ Lag W, ∀ q,
      ∃ g₀ : Matrix (Fin (W.rank + W.rank)) (Fin (W.rank + W.rank)) D.host.E,
        Formalism.L2.Theta.mt (GlobalTheory.Doubling.dblSp W) ((q.out : GQ (GlobalTheory.Doubling.dblSp W)) : GA D (GlobalTheory.Doubling.dblSp W)) =
          g₀.map (incA D) ∧ IsLagFrame W (e q) (frameOf W g₀) := by
  classical
  have hg : ∀ γ : GQ (GlobalTheory.Doubling.dblSp W), ∃ g₀ : Matrix (Fin (W.rank + W.rank)) (Fin (W.rank + W.rank)) D.host.E,
      Formalism.L2.Theta.mt (GlobalTheory.Doubling.dblSp W) (γ : GA D (GlobalTheory.Doubling.dblSp W)) = g₀.map (incA D) :=
    fun γ => rat_of_mem (GlobalTheory.Doubling.dblSp W) γ γ.2
  choose g₀ hg₀ using hg
  have hY : ∀ γ : GQ (GlobalTheory.Doubling.dblSp W), ∃ Y : Lag W, IsLagFrame W Y (frameOf W (g₀ γ)) :=
    fun γ => GlobalTheory.T.exists_doubledLagrangian_of_rational_unitary_frame D W γ (g₀ γ) (hg₀ γ)
  choose Y hY using hY
  have key : ∀ a b : GQ (GlobalTheory.Doubling.dblSp W), Y a = Y b ↔
      ((b : GA D (GlobalTheory.Doubling.dblSp W)) * (a : GA D (GlobalTheory.Doubling.dblSp W))⁻¹ ∈ GlobalTheory.Doubling.siegel W) :=
    fun a b => GlobalTheory.T.doubledLagrangian_eq_iff_siegelParabolic_coset D W a b (g₀ a) (g₀ b) (hg₀ a) (hg₀ b) (Y a) (Y b) (hY a) (hY b)
  let f : GlobalTheory.Eis.Cosets (GlobalTheory.Doubling.siegel W) (GQ (GlobalTheory.Doubling.dblSp W)) → Lag W :=
    Quotient.lift Y (fun a b hab => (key a b).2 (by
      have := QuotientGroup.rightRel_apply.1 hab
      rw [Subgroup.mem_subgroupOf] at this
      simpa using this))
  have hf : ∀ a, f (Quotient.mk _ a) = Y a := fun a => rfl
  have inj : Function.Injective f := by
    intro p q hpq
    induction p using Quotient.inductionOn
    induction q using Quotient.inductionOn
    rename_i a b
    rw [hf, hf] at hpq
    apply Quotient.sound
    refine QuotientGroup.rightRel_apply.2 ?_
    rw [Subgroup.mem_subgroupOf]
    simpa using (key a b).1 hpq
  have surj : Function.Surjective f := by
    intro Z
    obtain ⟨γ, hγQ, g₁, hg₁, hZ⟩ := GlobalTheory.T.exists_rational_unitary_doubledLagrangianFrame_witt D W Z
    refine ⟨Quotient.mk _ ⟨γ, hγQ⟩, ?_⟩
    rw [hf]
    have := (GlobalTheory.T.doubledLagrangian_eq_iff_siegelParabolic_coset D W γ γ (g₀ ⟨γ, hγQ⟩) g₁ (hg₀ ⟨γ, hγQ⟩) hg₁ (Y ⟨γ, hγQ⟩) Z (hY ⟨γ, hγQ⟩) hZ).2
    exact this (by simpa using (GlobalTheory.Doubling.siegel W).one_mem)
  refine ⟨Equiv.ofBijective f ⟨inj, surj⟩, fun q => ⟨g₀ q.out, hg₀ q.out, ?_⟩⟩
  show IsLagFrame W (f q) _
  conv_lhs => rw [← Quotient.out_eq q]
  exact hY q.out

theorem lagTerms_eq : ∀ (D : D7) ψ (V W : HSp D) χV χW om νV 𝓗 νW 𝓖 μ 𝓕 fr, SWSetup ψ V W χV χW om νV 𝓗 νW 𝓖 μ 𝓕 fr → ∀ f₁ f₂, IsThetaFunO ψ V W f₁ → IsThetaFunO ψ V W f₂ → ∀ (ν : Measure (Mx D V.rank W.rank)) (𝓖' : Set (Mx D V.rank W.rank)), IsCovolOne (ratL V W) ν 𝓖' → ∃ e : GlobalTheory.Eis.Cosets (GlobalTheory.Doubling.siegel W) (GQ (GlobalTheory.Doubling.dblSp W)) ≃ Lag W, ∀ q, ∃ C, IsLagFrame W (e q) C ∧ ∫ y in 𝓖', GlobalTheory.SWPairProof.dbl V W f₁ f₂ (actO (GlobalTheory.Doubling.dblSp W) V ((q.out : GQ (GlobalTheory.Doubling.dblSp W)) : GA D (GlobalTheory.Doubling.dblSp W))⁻¹ 1 (GlobalTheory.SiegelFormula.lagr W V y)) ∂ν = lagTerm μ 𝓕 C f₁ f₂ := by
  intro D ψ V W χV χW om νV 𝓗 νW 𝓖 μ 𝓕 fr hS f₁ f₂ h₁ h₂ ν 𝓖' hν
  obtain ⟨e, he⟩ := classes W
  refine ⟨e, fun q => ?_⟩
  obtain ⟨g₀, hg₀, hY⟩ := he q
  exact ⟨frameOf W g₀, hY, integral_eq hS h₁ h₂ ν 𝓖' hν _ g₀ hg₀ (e q) hY⟩

end GlobalTheory.SWLagTerms

end
