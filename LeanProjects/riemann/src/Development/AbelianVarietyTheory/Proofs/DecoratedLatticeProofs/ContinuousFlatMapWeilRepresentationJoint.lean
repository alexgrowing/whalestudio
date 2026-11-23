import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.GinfCSecondCountable
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsQuasiFam
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RealSizeNonneg
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.UnifModGrowthOfIsUnifModerate
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaAbsoluteSum
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilDatumExistence
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatThetaIntegrandLocallyUniformMajorantStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilMixedCoordinatesContinuousBoundedSupNormStatement

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
open scoped ComplexOrder ENNReal NNReal ContDiff

namespace GlobalTheory.FlatCont

theorem flatAt_om_continuous : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (V V₀ W W₀ : HSp D) (ρ σ : ℕ) (dV : HypDec V V₀ ρ) (dW : HypDec W W₀ σ) (vS : VolM D W.rank ρ) (vT : VolM D σ V₀.rank) (χV χW : (AE D)ˣ →* Circle) (om : Om V W), IsWeilDatumO ψ V W χV χW om → ∀ (vU : VolU D ρ) (x : Matrix (Fin W.rank) (Fin ρ) D.host.E), LinearIndependent D.host.E x.transpose → ∀ Φ, IsThetaFunO ψ V W Φ → Continuous fun q : (GA D V × GA D W) × Mx D V₀.rank σ × WO V₀ W₀ => flatAt ψ dV dW vS.μ vS.𝓕 vT.μ vT.𝓕 vU.ν (rat x) q.2.1 (om q.1 Φ) q.2.2 := by
  intro D ψ V V₀ W W₀ ρ σ dV dW vS vT χV χW om hom vU x hx Φ hΦ
  have hmaj := GlobalTheory.T.flatThetaIntegrand_locallyUniform_majorant D ψ V V₀ W W₀ ρ σ dV dW vS vT χV χW om hom vU x hx Φ hΦ
  have hmix := (GlobalTheory.T.weilMixedCoordinates_continuous_bounded_supNorm D ψ V V₀ W W₀ ρ σ dV dW vS vT χV χW om hom Φ hΦ).2
  have hψ : Continuous ψ := hom.std.1.1
  have htr : Continuous (Algebra.trace (AF D.host.F) (AE D)) :=
    IsModuleTopology.continuous_of_linearMap (Algebra.trace (AF D.host.F) (AE D))

  have hval : Continuous fun u : UX D ρ => (u.1.1 : Mx D ρ ρ) :=
    Units.continuous_val.comp continuous_subtype_val
  have hup : Continuous fun T : Mx D ρ ρ => upSum T := by
    unfold upSum
    refine continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ => ?_
    exact continuous_if_const _ (fun _ => (continuous_apply j).comp (continuous_apply i)) fun _ => continuous_const
  have hpsi : Continuous fun u : UX D ρ => psiUni ψ u.1 :=
    hψ.comp (htr.comp (hup.comp hval))
  have hxu : Continuous fun u : UX D ρ => (rat x : Mx D W.rank ρ) ⬝ u.1.1 :=
    continuous_const.matrix_mul hval

  have hcq : ∀ u : UX D ρ, Continuous fun q : (GA D V × GA D W) × Mx D V₀.rank σ × WO V₀ W₀ =>
      flatFun ψ dV dW vS.μ vS.𝓕 vT.μ vT.𝓕 (rat x) q.2.1 (om q.1 Φ) q.2.2 u := by
    intro u
    unfold flatFun
    refine continuous_const.mul ?_
    have hf : Continuous fun q : (GA D V × GA D W) × Mx D V₀.rank σ × WO V₀ W₀ =>
        ((q.1, ((rat x : Mx D W.rank ρ) ⬝ u.1.1, q.2.1, q.2.2)) :
          (GA D V × GA D W) × Mx D W.rank ρ × Mx D V₀.rank σ × WO V₀ W₀) := by fun_prop
    have h2 := hmix.comp hf
    simp only [Function.comp_def] at h2
    exact h2

  have hcu : ∀ q : (GA D V × GA D W) × Mx D V₀.rank σ × WO V₀ W₀, Continuous fun u : UX D ρ =>
      flatFun ψ dV dW vS.μ vS.𝓕 vT.μ vT.𝓕 (rat x) q.2.1 (om q.1 Φ) q.2.2 u := by
    intro q
    unfold flatFun
    refine (continuous_star.comp hpsi).mul ?_
    have hf : Continuous fun u : UX D ρ =>
        ((q.1, ((rat x : Mx D W.rank ρ) ⬝ u.1.1, q.2.1, q.2.2)) :
          (GA D V × GA D W) × Mx D W.rank ρ × Mx D V₀.rank σ × WO V₀ W₀) :=
      continuous_const.prodMk (hxu.prodMk continuous_const)
    have h2 := hmix.comp hf
    simp only [Function.comp_def] at h2
    exact h2
  haveI : SecondCountableTopology (AE D) := (Formalism.IndefR.Eqv.ae_facts D).2.2.2.1
  haveI : ∀ m n : ℕ, SecondCountableTopology (Mx D m n) := fun m n =>
    inferInstanceAs (SecondCountableTopology (Fin m → Fin n → AE D))
  haveI : ∀ m n : ℕ, FirstCountableTopology (Mx D m n) := fun m n =>
    TopologicalSpace.SecondCountableTopology.to_firstCountableTopology _
  haveI : ∀ S : HSp D, SecondCountableTopology (GA D S) := fun S => (Formalism.IndefR.Eqv.ga_facts D S).2.2.2.1
  haveI : BorelSpace (UX D ρ) := ⟨rfl⟩
  rw [continuous_iff_continuousAt]
  intro q₀
  obtain ⟨K, hK, hKn⟩ := exists_compact_mem_nhds q₀.1
  obtain ⟨M, hMi, hM⟩ := hmaj K hK
  have hev : ∀ᶠ q in nhds q₀, q.1 ∈ K := continuous_fst.continuousAt.preimage_mem_nhds hKn
  have key : ContinuousAt (fun q : (GA D V × GA D W) × Mx D V₀.rank σ × WO V₀ W₀ =>
      ∫ u, flatFun ψ dV dW vS.μ vS.𝓕 vT.μ vT.𝓕 (rat x) q.2.1 (om q.1 Φ) q.2.2 u ∂vU.ν) q₀ := by
    refine continuousAt_of_dominated (bound := M) ?_ ?_ hMi ?_
    · exact Filter.Eventually.of_forall fun q => (hcu q).aestronglyMeasurable
    · exact hev.mono fun q hq => Filter.Eventually.of_forall fun u => hM q.1 hq q.2.1 q.2.2 u
    · exact Filter.Eventually.of_forall fun u => (hcq u).continuousAt
  exact key

end GlobalTheory.FlatCont
