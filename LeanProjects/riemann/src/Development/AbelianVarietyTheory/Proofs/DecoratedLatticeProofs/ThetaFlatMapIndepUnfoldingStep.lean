import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HzUnit
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsMulRightInvariantOfFundamentalDomain
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.MixedModelTargetHeisenbergAnisotropicPart
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FlatIndep

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ}

theorem mixT_indep_quasi {S T T₀ : HSp D} {ρ : ℕ} (d : HypDec T T₀ ρ) {μ μ' : Measure (Mx D ρ S.rank)}
    {𝓕 𝓕' : Set (Mx D ρ S.rank)} (hμ : IsCovolOne (ratMx D ρ S.rank) μ 𝓕) (hμ' : IsCovolOne (ratMx D ρ S.rank) μ' 𝓕')
    {f : WO S T → ℂ} (hq : ∀ γ w, f (ratW T S γ + w) = ψ (-(symplOH S T (ratW T S γ) w)) * f w) :
    d.mixT S ψ μ' 𝓕' f = d.mixT S ψ μ 𝓕 f := by
  funext y w₀
  refine covolOne_integral_eq hμ hμ' _ ?_
  intro γ hγ ξ
  obtain ⟨δ, hδ⟩ : d.incX S γ ∈ ratMx D _ _ := ratMx_mul (rat_mem _) hγ
  have h := hq δ (d.incX S ξ + d.incAdj S y + d.inc0 S w₀)
  rw [show ratW T S δ = d.incX S γ from hδ] at h
  rw [HypDec.integrandT_eq, HypDec.integrandT_eq, map_add (d.incX S), add_assoc (d.incX S γ), add_assoc (d.incX S γ), h,
    ← mul_assoc, ← AddChar.map_add_eq_mul]
  simp only [GlobalTheory.OrientedHeis.symplOH_add_left, GlobalTheory.OrientedHeis.symplOH_add_right, HypDec.symplOH_incX_incX,
    HypDec.wittDecomp_sympl_inclIsotropic_inclAnisotropic, zero_add, add_zero]
  rw [add_comm (symplOH S T (d.incX S γ) _), add_neg_cancel_right]

theorem evalAt_indep {V V₀ W W₀ : HSp D} {ρ σ : ℕ} (dV : HypDec V V₀ ρ) (dW : HypDec W W₀ σ)
    {μS μS' : Measure (Mx D W.rank ρ)} {𝓕S 𝓕S' : Set (Mx D W.rank ρ)}
    {μT μT' : Measure (Mx D σ V₀.rank)} {𝓕T 𝓕T' : Set (Mx D σ V₀.rank)}
    (hS : IsCovolOne (ratMx D W.rank ρ) μS 𝓕S) (hS' : IsCovolOne (ratMx D W.rank ρ) μS' 𝓕S')
    (hT : IsCovolOne (ratMx D σ V₀.rank) μT 𝓕T) (hT' : IsCovolOne (ratMx D σ V₀.rank) μT' 𝓕T')
    {Ψ : WO V W → ℂ} (hΨ : IsThetaFunO ψ V W Ψ) (x : Mx D W.rank ρ) (y : Mx D V₀.rank σ) :
    evalAt ψ dV dW μS' 𝓕S' μT' 𝓕T' Ψ x y = evalAt ψ dV dW μS 𝓕S μT 𝓕T Ψ x y := by
  unfold evalAt
  rw [dV.mixS_indep hS hS' hΨ]
  exact congrFun (mixT_indep_quasi dW hT hT' (GlobalTheory.MixModel.Check.mixS_quasi dV μS 𝓕S hΨ x)) y

theorem flatAt_indep {V V₀ W W₀ : HSp D} {ρ σ : ℕ} (dV : HypDec V V₀ ρ) (dW : HypDec W W₀ σ)
    {μS μS' : Measure (Mx D W.rank ρ)} {𝓕S 𝓕S' : Set (Mx D W.rank ρ)}
    {μT μT' : Measure (Mx D σ V₀.rank)} {𝓕T 𝓕T' : Set (Mx D σ V₀.rank)}
    (hS : IsCovolOne (ratMx D W.rank ρ) μS 𝓕S) (hS' : IsCovolOne (ratMx D W.rank ρ) μS' 𝓕S')
    (hT : IsCovolOne (ratMx D σ V₀.rank) μT 𝓕T) (hT' : IsCovolOne (ratMx D σ V₀.rank) μT' 𝓕T')
    (νU : Measure (UX D ρ)) (x : Mx D W.rank ρ) (y : Mx D V₀.rank σ) {Ψ : WO V W → ℂ} (hΨ : IsThetaFunO ψ V W Ψ) :
    flatAt ψ dV dW μS' 𝓕S' μT' 𝓕T' νU x y Ψ = flatAt ψ dV dW μS 𝓕S μT 𝓕T νU x y Ψ := by
  funext w
  unfold flatAt flatFun
  simp only [evalAt_indep dV dW hS hS' hT hT' hΨ]

theorem volU_eq {ρ : ℕ} (v v' : VolU D ρ) : v.ν = v'.ν :=
  (GlobalTheory.UnitU.isUnitU_exists_unique_rightInvariant D ρ).2.1 _ _ v.unit v'.unit

theorem flat_indep : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), (∀ (ρ : ℕ) (B : BesLev D ρ) (J : JacLev D ρ) (s s' : StepBF ψ B J) f, IsThetaFunO ψ B.V J.W f → flatBF s f = flatBF s' f) ∧ ∀ (σ : ℕ) (J : JacLev D (σ + 1)) (B : BesLev D σ) (s s' : StepFB ψ J B) f, IsThetaFunO ψ J.W B.V f → flatFB s f = flatFB s' f := by
  intro D ψ
  refine ⟨fun ρ B J s s' f hf => ?_, fun σ J B s s' f hf => ?_⟩
  · unfold flatBF GlobalTheory.MixPer.flat
    rw [volU_eq s.vU s'.vU]
    exact flatAt_indep _ _ s'.vS.covol s.vS.covol s'.vT.covol s.vT.covol _ _ _ hf
  · unfold flatFB GlobalTheory.MixPer.flatLast
    rw [volU_eq s.vU s'.vU]
    exact flatAt_indep _ _ s'.vS.covol s.vS.covol s'.vT.covol s.vT.covol _ _ _ hf

end GlobalTheory.FlatIndep

end
