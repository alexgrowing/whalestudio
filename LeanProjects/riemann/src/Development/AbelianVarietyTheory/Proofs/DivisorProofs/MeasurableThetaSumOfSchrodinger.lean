import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUSplittingInl
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ImportsBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemRatPairIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemRatVecIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzSpaceTranslateMem

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField MeasureTheory
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix Formalism.IndefR.Datum
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ThetaTransformMeas

open Filter Topology
open scoped Classical

section

variable (F : Type) [Field F] [NumberField F]

theorem continuous_mixed : Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace F) := by
  change Continuous fun x : InfiniteAdeleRing F =>
    ((fun (v : {w : InfinitePlace F // w.IsReal}) => InfinitePlace.Completion.extensionEmbeddingOfIsReal v.2 (x v)),
     (fun (v : {w : InfinitePlace F // w.IsComplex}) => InfinitePlace.Completion.extensionEmbedding v.1 (x v)))
  refine Continuous.prodMk (continuous_pi fun v => ?_) (continuous_pi fun v => ?_)
  · exact (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal v.2).continuous.comp (continuous_apply _)
  · exact (InfinitePlace.Completion.isometry_extensionEmbedding v.1).continuous.comp (continuous_apply _)

theorem continuous_pureA {κ : Type} [Fintype κ] (f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ)
    {g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ} (hg : g ∈ GlobalTheory.WeilM.SB (κ → FiniteAdeleRing (𝓞 F) F)) :
    Continuous (GlobalTheory.WeilM.pureA F f g) := by
  have h1 : Continuous fun x : κ → AdeleRing (𝓞 F) F => fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1 :=
    continuous_pi fun i => (continuous_mixed F).comp (continuous_fst.comp (continuous_apply i))
  have h2 : Continuous fun x : κ → AdeleRing (𝓞 F) F => fun i => (x i).2 :=
    continuous_pi fun i => continuous_snd.comp (continuous_apply i)
  exact (f.continuous.comp h1).mul (hg.1.continuous.comp h2)

theorem continuous_of_mem_schA {κ : Type} [Fintype κ] {Φ : (κ → AdeleRing (𝓞 F) F) → ℂ}
    (hΦ : Φ ∈ GlobalTheory.WeilM.schA F κ) : Continuous Φ := by
  induction hΦ using Submodule.span_induction with
  | mem Φ h =>
    obtain ⟨f, g, hg, rfl⟩ := h
    exact continuous_pureA F f hg
  | zero => exact continuous_const
  | add _ _ _ _ h1 h2 => exact h1.add h2
  | smul c _ _ h => exact h.const_smul c

theorem countable_field : Countable F :=
  (Module.finBasis ℚ F).equivFun.injective.countable

end

theorem main : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsCharAF F ψ → ∀ (κ : Type) [Fintype κ], ∀ Φ ∈ GlobalTheory.WeilM.schA F κ,
    @Measurable _ _ (borel _) _ (fun w : (κ → AF F) × (κ → AF F) => GlobalTheory.WeilM.thetaSum F (GlobalTheory.WeilM.schr ψ w Φ)) := by
  intro F _ _ ψ hψ κ _ Φ hΦ
  letI : MeasurableSpace ((κ → AF F) × (κ → AF F)) := borel _
  haveI : BorelSpace ((κ → AF F) × (κ → AF F)) := ⟨rfl⟩
  haveI := countable_field F
  have hc := continuous_of_mem_schA F hΦ
  let T : (κ → F) → (κ → AF F) × (κ → AF F) → ℂ := fun ξ w =>
    GlobalTheory.WeilM.schr ψ w Φ (fun i => algebraMap F (AF F) (ξ i))
  have hT : ∀ ξ, Continuous (T ξ) := by
    intro ξ
    simp only [T, GlobalTheory.WeilM.schr]
    refine (hψ.1.comp ?_).mul (hc.comp ?_)
    · fun_prop
    · fun_prop
  have hs : ∀ w, Summable fun ξ => T ξ w := by
    intro w
    have h := GlobalTheory.WeilM.summable_of_mem_schA F (GlobalTheory.SchwartzTranslate.schA_translate F w.1 hΦ)
    refine Summable.of_norm_bounded h.norm fun ξ => ?_
    simp only [T, GlobalTheory.WeilM.schr, norm_mul, hψ.2.1, one_mul]
    exact le_rfl
  change Measurable fun w => ∑' ξ, T ξ w
  exact measurable_of_tendsto_metrizable' (atTop : Filter (Finset (κ → F)))
    (f := fun s w => ∑ ξ ∈ s, T ξ w) (fun s => Finset.measurable_sum s fun ξ _ => (hT ξ).measurable)
    (tendsto_pi_nhds.2 fun w => (hs w).hasSum)

end GlobalTheory.ThetaTransformMeas

end
