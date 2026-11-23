import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsQuasiFam
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilOperatorCommutesSuperpositionSlicesSourceStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsThetaFunctionSuperpositionOrthogonalSlicesStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsThetaFunSuperpositionTargetOrthSummandStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousIsotropicSandwichMeanTranslation
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ContinuousResTSymm
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaAbsoluteSum
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilDatumExistence
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

noncomputable section

namespace GlobalTheory.ContrTheta

theorem continuous_linkKappa {D : D7} {ρ : ℕ} {B : BesLev D ρ} {L' : HSp D} {ζ' : Fin L'.rank → D.host.E}
    (l : Link B L' ζ') (S : HSp D) : Continuous (l.κ S) := by
  unfold Link.κ GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.ofAdj
  have h : Continuous fun w : WO S L' => giA S ⬝ (adj (rat l.τ ⬝ w) ⬝ gA B.L) :=
    Continuous.matrix_mul continuous_const (Continuous.matrix_mul
      (GlobalTheory.MixModel.continuous_adj.comp (continuous_const.matrix_mul continuous_id)) continuous_const)
  exact h.const_smul ((incA D) (-D.host.xi0⁻¹))

theorem integrable_restrict_of_bdd {X : Type} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    (μ : Measure X) (s : Set X) (hs : μ s = 1) (f : X → ℂ) (hf : Continuous f) (C : ℝ) (hC : ∀ x, ‖f x‖ ≤ C) :
    Integrable f (μ.restrict s) := by
  haveI : IsFiniteMeasure (μ.restrict s) := ⟨by rw [Measure.restrict_apply_univ, hs]; exact ENNReal.one_lt_top⟩
  exact (integrable_const C).mono' hf.aestronglyMeasurable (ae_of_all _ fun x => by simpa using hC x)

theorem contr_isTheta : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (σ : ℕ) (B : BesLev D (σ + 1)) (J : JacLev D (σ + 1)) (B' : BesLev D σ) (s₁ : StepBF ψ B J) (s₂ : StepFB ψ J B') (l : Link B B'.L B'.ζ) (vL : VolM D B'.L.rank J.W₀.rank) (χA χA' χz : ((AE D)ˣ →* Circle)) (oma : Om B.A J.W₀) (omz : Om B.L J.W₀) (omb : Om J.W₀ B'.A) (omz' : Om J.W₀ B'.L), s₁.χV = χA * χz → s₂.χW = χA' * χz → IsWeilDatumO ψ B.A J.W₀ χA s₁.χW oma → IsWeilDatumO ψ B.L J.W₀ χz s₁.χW omz → IsWeilDatumO ψ J.W₀ B'.A s₂.χV χA' omb → IsWeilDatumO ψ J.W₀ B'.L s₂.χV χz omz' → ∀ (Ξ₁ : WO B.V₀ J.W₀ → ℂ) (Ξ₂ : WO J.W₀ B'.V₀ → ℂ), IsThetaFunO ψ B.V₀ J.W₀ Ξ₁ → IsThetaFunO ψ J.W₀ B'.V₀ Ξ₂ → (∀ v, IsThetaFunO ψ B.A J.W₀ fun u => contr l J.W₀ vL Ξ₁ Ξ₂ u v) ∧ ∀ p, (IsThetaFunO ψ J.W₀ B'.A fun v => oma p (fun u => contr l J.W₀ vL Ξ₁ Ξ₂ u v) 0) ∧ ∀ v, oma p (fun u => contr l J.W₀ vL Ξ₁ Ξ₂ u v) 0 = ∫ w in vL.𝓕, Ξ₂ ((B'.o.resT J.W₀).symm (v, w)) * oma p (fun u => Ξ₁ ((B.o.resS J.W₀).symm (u, l.κ J.W₀ w))) 0 ∂vL.μ := by
  intro D ψ σ B J B' s₁ s₂ l vL χA χA' χz oma omz omb omz' _ _ hoa _ _ _ Ξ₁ Ξ₂ hΞ₁ hΞ₂
  have hstd : IsStdChar D ψ (-1) := hoa.std
  haveI hbor : ∀ m n, BorelSpace (Mx D m n) := fun _ _ => ⟨rfl⟩
  have hκ : Continuous (l.κ J.W₀) := continuous_linkKappa l J.W₀
  have hκm : Measurable (l.κ J.W₀) := hκ.measurable
  have hvol : vL.μ vL.𝓕 = 1 := vL.covol.2.2
  have ha : ∀ v, Integrable (fun w => Ξ₂ ((B'.o.resT J.W₀).symm (v, w))) (vL.μ.restrict vL.𝓕) := by
    intro v
    obtain ⟨C, hC⟩ := GlobalTheory.IsoMean.isThetaFunO_bounded _ _ ψ hstd Ξ₂ hΞ₂
    exact integrable_restrict_of_bdd _ _ hvol _ (hΞ₂.cont.comp ((OrthDec.continuous_resT_symm _ _).comp
      (Continuous.prodMk continuous_const continuous_id))) C (fun w => hC _)
  have hG : ∀ p, IsThetaFunO ψ B.V₀ J.W₀ (fun x => oma p (fun u => Ξ₁ ((B.o.resS J.W₀).symm (u, (B.o.resS J.W₀ x).2)))
      (B.o.resS J.W₀ x).1) := fun p =>
    (GlobalTheory.T.weil_operator_commutes_superposition_slices_source D ψ B.V₀ B.A B.L J.W₀ B.o χA s₁.χW oma hoa Ξ₁ hΞ₁ _ (vL.μ.restrict vL.𝓕) (l.κ J.W₀) _ hκm (ha 0) p).1
  have hb : ∀ p, Integrable (fun w => oma p (fun u => Ξ₁ ((B.o.resS J.W₀).symm (u, l.κ J.W₀ w))) 0)
      (vL.μ.restrict vL.𝓕) := by
    intro p
    obtain ⟨C, hC⟩ := GlobalTheory.IsoMean.isThetaFunO_bounded _ _ ψ hstd _ (hG p)
    have heq : (fun w => oma p (fun u => Ξ₁ ((B.o.resS J.W₀).symm (u, l.κ J.W₀ w))) 0) = fun w =>
        (fun x => oma p (fun u => Ξ₁ ((B.o.resS J.W₀).symm (u, (B.o.resS J.W₀ x).2))) (B.o.resS J.W₀ x).1)
          ((B.o.resS J.W₀).symm (0, l.κ J.W₀ w)) := by
      funext w; simp only [AddEquiv.apply_symm_apply]
    rw [heq]
    exact integrable_restrict_of_bdd _ _ hvol _ ((hG p).cont.comp ((OrthDec.continuous_resS_symm _ _).comp
      (Continuous.prodMk continuous_const hκ))) C (fun w => hC _)
  have hcom : ∀ p v, oma p (fun u => contr l J.W₀ vL Ξ₁ Ξ₂ u v) 0 = ∫ w in vL.𝓕, Ξ₂ ((B'.o.resT J.W₀).symm (v, w)) *
      oma p (fun u => Ξ₁ ((B.o.resS J.W₀).symm (u, l.κ J.W₀ w))) 0 ∂vL.μ := fun p v =>
    (GlobalTheory.T.weil_operator_commutes_superposition_slices_source D ψ B.V₀ B.A B.L J.W₀ B.o χA s₁.χW oma hoa Ξ₁ hΞ₁ _ (vL.μ.restrict vL.𝓕) (l.κ J.W₀) _ hκm (ha v) p).2 0
  refine ⟨fun v => ?_, fun p => ⟨?_, hcom p⟩⟩
  · exact GlobalTheory.T.isThetaFunction_superposition_orthogonalSlices D ψ hstd B.V₀ B.A B.L J.W₀ B.o Ξ₁ hΞ₁ _ (vL.μ.restrict vL.𝓕) (l.κ J.W₀) _ hκm (ha v)
  · have h := GlobalTheory.T.isThetaFun_superposition_target_orthSummand D ψ hstd B'.V₀ B'.A B'.L J.W₀ B'.o Ξ₂ hΞ₂ _ (vL.μ.restrict vL.𝓕) id _ measurable_id (hb p)
    have heq : (fun v => oma p (fun u => contr l J.W₀ vL Ξ₁ Ξ₂ u v) 0) = fun v =>
        ∫ w, oma p (fun u => Ξ₁ ((B.o.resS J.W₀).symm (u, l.κ J.W₀ w))) 0 * Ξ₂ ((B'.o.resT J.W₀).symm (v, id w))
          ∂(vL.μ.restrict vL.𝓕) := by
      funext v; rw [hcom]; congr 1; funext w; rw [mul_comm]; rfl
    rw [heq]; exact h

end GlobalTheory.ContrTheta

end
