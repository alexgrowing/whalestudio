import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousIteratedFDerivApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IteratedFDerivIntegralSchwartzStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzIntegralEqOfDerivsStatement
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open Classical

namespace GlobalTheory.SchwInt

theorem clm_iterated_integral : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {α β : Type} [TopologicalSpace α] [MeasurableSpace α] [BorelSpace α] [SecondCountableTopology α]
    [TopologicalSpace β] [MeasurableSpace β] [BorelSpace β] [SecondCountableTopology β]
    (μa : Measure α) (μb : Measure β) [IsFiniteMeasureOnCompacts μa] [IsFiniteMeasureOnCompacts μb] [SFinite μa] [SFinite μb]
    (g : α → β → SchwartzMap V ℂ) (hg : Continuous (Function.uncurry g))
    (C : Set (α × β)) (hC : IsCompact C) (h0 : ∀ p ∉ C, g p.1 p.2 = 0)
    (S : SchwartzMap V ℂ) (hS : ∀ y, S y = ∫ a, ∫ b, g a b y ∂μb ∂μa) (l : SchwartzMap V ℂ →L[ℂ] ℂ),
    l S = ∫ a, ∫ b, l (g a b) ∂μb ∂μa := by
  intro V _ _ α β _ _ _ _ _ _ _ _ μa μb _ _ _ _ g hg C hC h0 S hS l
  have h0' : ∀ p ∉ C, Function.uncurry g p = 0 := fun p hp => h0 p hp
  have hev : ∀ y, S y = ∫ p, Function.uncurry g p y ∂(μa.prod μb) := by
    intro y
    rw [hS y, integral_prod]
    · rfl
    · exact integrable_of_zero_outside _ (continuous_apply hg y) hC
        (fun p hp => by simp [h0' p hp])
  have hSn : ∀ (n : ℕ) (x : V), iteratedFDeriv ℝ n S x =
      ∫ p, iteratedFDeriv ℝ n ⇑(Function.uncurry g p : SchwartzMap V ℂ) x ∂(μa.prod μb) := by
    intro n x
    have hfun : (⇑S) = fun y => ∫ p, (Function.uncurry g p : SchwartzMap V ℂ) y ∂(μa.prod μb) := funext hev
    rw [hfun]
    exact GlobalTheory.T.iteratedFDeriv_integral_schwartz (μa.prod μb) _ hg C hC h0' n x
  rw [GlobalTheory.T.schwartz_integral_eq_of_derivs (μa.prod μb) _ hg C hC h0' S hSn l, integral_prod]
  · rfl
  · exact integrable_of_zero_outside _ (l.continuous.comp hg) hC (fun p hp => by simp [h0' p hp])

end GlobalTheory.SchwInt
