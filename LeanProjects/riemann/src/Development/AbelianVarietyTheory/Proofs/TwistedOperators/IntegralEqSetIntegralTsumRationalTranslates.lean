import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.AdjointIsotropicDecomposition
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Twist.Periodize

theorem integral_eq_setIntegral_tsum (D : D7) (m n : ℕ) (μ : Measure (Mx D m n)) (𝓕 : Set (Mx D m n))
    (hμ : μ.IsAddHaarMeasure) (hF : IsAddFundamentalDomain (ratMx D m n) 𝓕 μ) (c : Mx D m n → ℂ)
    (hc : Integrable c μ) :
    (∀ᵐ y ∂(μ.restrict 𝓕), Summable fun a : Matrix (Fin m) (Fin n) D.host.E => ‖c (y + a.map (incA D))‖) ∧
      ∫ y, c y ∂μ = ∫ y in 𝓕, ∑' a : Matrix (Fin m) (Fin n) D.host.E, c (y + a.map (incA D)) ∂μ := by
  obtain ⟨i1, i2, i3, i4, i5, -⟩ := GlobalTheory.MixModel.lattice_Mx D m n
  haveI : BorelSpace (Mx D m n) := ⟨rfl⟩
  haveI : DiscreteTopology (ratMx D m n) := i5
  haveI : Countable (ratMx D m n) := TopologicalSpace.separableSpace_iff_countable.1 inferInstance

  let e : Matrix (Fin m) (Fin n) D.host.E ≃ ratMx D m n :=
    Equiv.ofBijective (fun a => ⟨a.map (incA D), a, rfl⟩)
      ⟨fun a b h => Matrix.map_injective GlobalTheory.MixModel.incA_injective (congrArg Subtype.val h),
        fun γ => by obtain ⟨a, ha⟩ := γ.2; exact ⟨a, Subtype.ext ha⟩⟩
  have he : ∀ a, ((e a : ratMx D m n) : Mx D m n) = a.map (incA D) := fun _ => rfl

  have hm : ∀ γ : ratMx D m n, AEStronglyMeasurable (fun y => c (y + γ)) (μ.restrict 𝓕) := by
    intro γ
    have := hc.1.comp_quasiMeasurePreserving (measurePreserving_add_right μ (γ : Mx D m n)).quasiMeasurePreserving
    exact this.restrict

  have hl : ∑' γ : ratMx D m n, ∫⁻ y in 𝓕, ‖c (y + γ)‖ₑ ∂μ = ∫⁻ y, ‖c y‖ₑ ∂μ := by
    rw [hF.lintegral_eq_tsum'' (fun y => ‖c y‖ₑ)]
    refine tsum_congr fun γ => ?_
    simp only [AddSubgroup.vadd_def, vadd_eq_add, add_comm (γ : Mx D m n)]
  have hfin : ∑' γ : ratMx D m n, ∫⁻ y in 𝓕, ‖c (y + γ)‖ₑ ∂μ ≠ ⊤ := by
    rw [hl]; exact hc.2.ne

  have hae : ∀ᵐ y ∂(μ.restrict 𝓕), Summable fun γ : ratMx D m n => ‖c (y + γ)‖ := by
    have h1 : ∫⁻ y in 𝓕, ∑' γ : ratMx D m n, ‖c (y + γ)‖ₑ ∂μ ≠ ⊤ := by
      rw [lintegral_tsum fun γ => (hm γ).enorm]; exact hfin
    have h2 : AEMeasurable (fun y => ∑' γ : ratMx D m n, ‖c (y + γ)‖ₑ) (μ.restrict 𝓕) :=
      AEMeasurable.ennreal_tsum fun γ => (hm γ).enorm
    filter_upwards [ae_lt_top' h2 h1] with y hy
    have : ∑' γ : ratMx D m n, (‖c (y + γ)‖₊ : ENNReal) ≠ ⊤ := by
      simpa only [enorm_eq_nnnorm] using hy.ne
    exact (NNReal.summable_coe.2 (ENNReal.tsum_coe_ne_top_iff_summable.1 this)).congr fun _ => rfl
  refine ⟨?_, ?_⟩
  · filter_upwards [hae] with y hy
    exact (e.summable_iff.2 hy).congr fun a => by rw [Function.comp_apply, he]
  · have h3 : ∫ y in 𝓕, ∑' γ : ratMx D m n, c (y + γ) ∂μ = ∑' γ : ratMx D m n, ∫ y in 𝓕, c (y + γ) ∂μ :=
      integral_tsum hm hfin
    have h4 : ∫ y, c y ∂μ = ∑' γ : ratMx D m n, ∫ y in 𝓕, c (y + γ) ∂μ := by
      rw [hF.integral_eq_tsum' c hc, ← (Equiv.neg (ratMx D m n)).tsum_eq]
      refine tsum_congr fun γ => ?_
      simp only [Equiv.neg_apply, neg_neg, AddSubgroup.vadd_def, vadd_eq_add, add_comm (γ : Mx D m n)]
    rw [h4, ← h3]
    congr 1
    funext y
    rw [← e.tsum_eq]
    rfl

end GlobalTheory.Twist.Periodize
