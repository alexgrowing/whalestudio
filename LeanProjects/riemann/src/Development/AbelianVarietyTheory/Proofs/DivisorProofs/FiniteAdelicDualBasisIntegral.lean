import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUSplittingInl
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ImportsBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledUnitaryPartnerDiagStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsContOnOfLocal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdeleJoinZero

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical

noncomputable section

namespace GlobalTheory.WeilL2Words

open MeasureTheory

theorem enorm_sum_mul_sq_le {m : ℕ} (a b : Fin m → ℂ) :
    ‖∑ i, a i * b i‖ₑ ^ 2 ≤ (∑ i, ‖b i‖ₑ ^ 2) * ∑ i, ‖a i‖ₑ ^ 2 := by
  have h1 : ‖∑ i, a i * b i‖₊ ≤ ∑ i, ‖b i‖₊ * ‖a i‖₊ := by
    refine (nnnorm_sum_le _ _).trans (le_of_eq ?_)
    simp [nnnorm_mul, mul_comm]
  have h2 : ‖∑ i, a i * b i‖₊ ^ 2 ≤ (∑ i, ‖b i‖₊ ^ 2) * ∑ i, ‖a i‖₊ ^ 2 :=
    (pow_le_pow_left₀ (by positivity) h1 2).trans (Finset.sum_mul_sq_le_sq_mul_sq _ _ _)
  simp only [enorm_eq_nnnorm]
  exact_mod_cast h2

theorem slice_le_l2A (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (m : ℕ)
    (g : Fin m → (κ → FiniteAdeleRing (𝓞 F) F) → ℂ) (yy : Fin m → (κ → FiniteAdeleRing (𝓞 F) F))
    (hg : ∀ i, g i ∈ GlobalTheory.WeilM.SB (κ → FiniteAdeleRing (𝓞 F) F)) (hyy : ∀ i j, g i (yy j) = if i = j then 1 else 0)
    (μ : @MeasureTheory.Measure (κ → FiniteAdeleRing (𝓞 F) F) (borel _))
    (hμ : @MeasureTheory.Measure.IsAddHaarMeasure _ _ _ (borel _) μ)
    (y : κ → FiniteAdeleRing (𝓞 F) F) : ∃ C : ENNReal, C ≠ ⊤ ∧
      ∀ f : Fin m → SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ,
      ∫⁻ x, ‖(∑ i, GlobalTheory.WeilM.pureA F (f i) (g i)) (GlobalTheory.WeilCont.adeleJoin F x y)‖ₑ ^ 2 ≤
        C * GlobalTheory.WeilL2Words.l2A F μ (∑ i, GlobalTheory.WeilM.pureA F (f i) (g i)) := by
  have hmeas : ∀ f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ, Measurable fun x => ‖f x‖ₑ ^ 2 :=
    fun f => by
      haveI : OpensMeasurableSpace (κ → mixedEmbedding.mixedSpace F) := inferInstance
      exact (f.continuous.measurable.enorm).pow_const 2
  letI : MeasurableSpace (κ → FiniteAdeleRing (𝓞 F) F) := borel _
  haveI : BorelSpace (κ → FiniteAdeleRing (𝓞 F) F) := ⟨rfl⟩
  haveI := hμ
  have hev : ∀ (f : Fin m → SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ) x y',
      (∑ i, GlobalTheory.WeilM.pureA F (f i) (g i)) (GlobalTheory.WeilCont.adeleJoin F x y') = ∑ i, f i x * g i y' := by
    intro f x y'
    rw [Finset.sum_apply]
    exact Finset.sum_congr rfl fun i _ => GlobalTheory.WeilCont.pureA_adeleJoin F _ _ x y'

  let U : Fin m → Set (κ → FiniteAdeleRing (𝓞 F) F) := fun j => ⋂ i, {y' | g i y' = g i (yy j)}
  have hUo : ∀ j, IsOpen (U j) := fun j => isOpen_iInter_of_finite fun i => (hg i).1.isOpen_fiber _
  have hUm : ∀ j, yy j ∈ U j := fun j => Set.mem_iInter.2 fun i => rfl
  have hUv : ∀ j, ∀ y' ∈ U j, ∀ i, g i y' = if i = j then 1 else 0 := fun j y' hy' i => by
    rw [← hyy]; exact Set.mem_iInter.1 hy' i
  have hU0 : ∀ j, μ (U j) ≠ 0 := fun j => (hUo j).measure_ne_zero μ ⟨_, hUm j⟩
  have hUt : ∀ j, μ (U j) ≠ ⊤ := by
    intro j
    refine ne_top_of_le_ne_top ((hg j).2.isCompact.measure_lt_top).ne (measure_mono ?_)
    intro y' hy'
    apply subset_tsupport
    rw [Function.mem_support, hUv j y' hy' j, if_pos rfl]
    exact one_ne_zero
  have hB : (∑ i, ‖g i y‖ₑ ^ 2) ≠ ⊤ := ENNReal.sum_ne_top.2 fun i _ => ENNReal.pow_ne_top enorm_ne_top
  refine ⟨(∑ i, ‖g i y‖ₑ ^ 2) * ∑ j, (μ (U j))⁻¹, ENNReal.mul_ne_top hB
    (ENNReal.sum_ne_top.2 fun j _ => ENNReal.inv_ne_top.2 (hU0 j)), ?_⟩
  intro f
  have hA : ∀ j, ∫⁻ x, ‖f j x‖ₑ ^ 2 ≤ (μ (U j))⁻¹ * GlobalTheory.WeilL2Words.l2A F μ (∑ i, GlobalTheory.WeilM.pureA F (f i) (g i)) := by
    intro j
    rw [← ENNReal.div_eq_inv_mul, ENNReal.le_div_iff_mul_le (Or.inl (hU0 j)) (Or.inl (hUt j))]
    have e : ∫⁻ y' in U j, (∫⁻ x, ‖(∑ i, GlobalTheory.WeilM.pureA F (f i) (g i)) (GlobalTheory.WeilCont.adeleJoin F x y')‖ₑ ^ 2) ∂μ
        = ∫⁻ y' in U j, (∫⁻ x, ‖f j x‖ₑ ^ 2) ∂μ := by
      refine setLIntegral_congr_fun (hUo j).measurableSet (fun y' hy' => ?_)
      refine lintegral_congr fun x => ?_
      rw [hev, Finset.sum_eq_single j]
      · rw [hUv j y' hy' j, if_pos rfl, mul_one]
      · intro i _ hij
        rw [hUv j y' hy' i, if_neg hij, mul_zero]
      · intro h
        exact absurd (Finset.mem_univ j) h
    rw [setLIntegral_const] at e
    rw [← e]
    exact setLIntegral_le_lintegral _ _
  calc ∫⁻ x, ‖(∑ i, GlobalTheory.WeilM.pureA F (f i) (g i)) (GlobalTheory.WeilCont.adeleJoin F x y)‖ₑ ^ 2
      ≤ ∫⁻ x, (∑ i, ‖g i y‖ₑ ^ 2) * ∑ i, ‖f i x‖ₑ ^ 2 := by
        refine lintegral_mono fun x => ?_
        rw [hev]
        exact enorm_sum_mul_sq_le _ _
    _ = (∑ i, ‖g i y‖ₑ ^ 2) * ∑ i, ∫⁻ x, ‖f i x‖ₑ ^ 2 := by
        rw [lintegral_const_mul' _ _ hB, lintegral_finset_sum]
        intro i _
        exact hmeas (f i)
    _ ≤ (∑ i, ‖g i y‖ₑ ^ 2) * ∑ j, (μ (U j))⁻¹ * GlobalTheory.WeilL2Words.l2A F μ (∑ i, GlobalTheory.WeilM.pureA F (f i) (g i)) := by
        gcongr with j
        exact hA j
    _ = _ := by rw [← Finset.sum_mul, mul_assoc]

end GlobalTheory.WeilL2Words

end
