import Mathlib
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.InfAdeleTensorBijective
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.StarPurelyImaginaryEqNeg

noncomputable section

namespace GlobalTheory.FockCompare

section General

open NumberField GlobalTheory.InfAdeleCM
open scoped TensorProduct

theorem exists_real_chart_general {F : Type} [Field F] [NumberField F] [IsTotallyReal F] {I : Type}
    (σ : I → (F →+* ℂ)) (hb : Function.Bijective fun i => InfinitePlace.mk (σ i)) :
    ∃ ρ : (I → ℝ) →+ InfiniteAdeleRing F, Continuous ρ ∧ (∀ x i, ext (σ i) (ρ x) = (x i : ℂ)) ∧
      ∀ a : InfiniteAdeleRing F, (∀ i, ext (σ i) a = 0) → a = 0 := by
  let e : I ≃ InfinitePlace F := Equiv.ofBijective _ hb
  let r : ∀ v : InfinitePlace F, v.Completion ≃+* ℝ := fun v =>
    InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal v)
  have hr : ∀ v, Continuous (r v).symm := fun v =>
    (InfinitePlace.Completion.isometryEquivRealOfIsReal (IsTotallyReal.isReal v)).symm.continuous
  refine ⟨{ toFun := fun x v => (r v).symm (x (e.symm v))
            map_zero' := funext fun v => map_zero (r v).symm
            map_add' := fun x y => funext fun v => map_add (r v).symm _ _ }, ?_, ?_, ?_⟩
  · exact continuous_pi fun v => (hr v).comp (continuous_apply _)
  · intro x i
    rw [ext_eq_ofReal]
    congr 1
    have h := (r (e i)).apply_symm_apply (x (e.symm (e i)))
    refine Eq.trans h ?_
    rw [e.symm_apply_apply]
  · intro a ha
    funext v
    obtain ⟨i, rfl⟩ := hb.2 v
    exact (InfinitePlace.Completion.extensionEmbedding _).injective ((ha i).trans (map_zero _).symm)

end General

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix GlobalTheory.FockCompare GlobalTheory.IndefiniteRowSideFullHecke.FockOrthogonalDecomposition
open scoped TensorProduct ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem exists_real_chart : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → (Function.Bijective fun τ : D.what₂.Tau => NumberField.InfinitePlace.mk ((tauE D τ).comp (algebraMap D.host.F D.host.E))) → ∃ ρ : (D.what₂.Tau → ℝ) →+ Ainf D.host.F, Continuous ρ ∧ (∀ x τ, θ τ (ρ x ⊗ₜ[D.host.F] (1 : D.host.E)) = (x τ : ℂ)) ∧ ∀ a : Ainf D.host.F, (∀ τ, θ τ (a ⊗ₜ[D.host.F] (1 : D.host.E)) = 0) → a = 0 := by
  intro D θ hθ hb
  haveI := D.sp.cm.totReal
  obtain ⟨ρ, h1, h2, h3⟩ := exists_real_chart_general (F := D.host.F)
    (fun τ : D.what₂.Tau => (tauE D τ).comp (algebraMap D.host.F D.host.E)) hb
  have key : ∀ τ (a : Ainf D.host.F), θ τ (a ⊗ₜ[D.host.F] (1 : D.host.E)) =
      GlobalTheory.InfAdeleCM.ext ((tauE D τ).comp (algebraMap D.host.F D.host.E)) a := fun τ a => by
    have := GlobalTheory.InfAdeleCM.hom_tmul (tauE D τ) (θ τ) (hθ τ).1 (hθ τ).2 a 1
    rw [RingHom.map_one, mul_one] at this
    exact this
  exact ⟨ρ, h1, fun x τ => (key τ _).trans (h2 x τ), fun a ha => h3 a fun τ => (key τ a).symm.trans (ha τ)⟩

end GlobalTheory.FockCompare

end
