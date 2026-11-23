import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.BoundaryPolynomialFunctions
import Development.AbelianVarietyTheory.Definitions.Divisors.FirstChernLeviEqConstant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContDiffAtLogNorm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionPullbackHolomorphic

open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GlobalTheory.IndefiniteRowSideFullHecke.BoundaryPolynomialFunctions
open scoped ContDiff

noncomputable section

namespace GlobalTheory.ProdSecPot

variable {n : ℕ} {Y : Type} [TopologicalSpace Y]

def sumPot {m : ℕ} (Q : Fin m → LocPot Y) : LocPot Y where
  U y := ⋂ i, (Q i).U y
  isOpen_U y := isOpen_iInter_of_finite fun i => (Q i).isOpen_U y
  mem_U y := Set.mem_iInter.2 fun i => (Q i).mem_U y
  φ y z := ∑ i, (Q i).φ y z

theorem isPotential_sumPot (B : FinHolAtlas n Y) {m : ℕ} (Q : Fin m → LocPot Y)
    (hQ : ∀ i, IsPotential B (Q i)) : IsPotential B (sumPot Q) := by
  refine ⟨fun x j => ?_, fun x x' y hy => ?_⟩
  · show ContDiffOn ℝ ∞ (fun t => ∑ i, ((Q i).φ x ∘ (B.chart j).symm) t) _
    exact ContDiffOn.sum fun i _ => ((hQ i).1 x j).mono
      (Set.inter_subset_inter_right _ (Set.preimage_mono (Set.iInter_subset _ i)))
  · have hy' : ∀ i, y ∈ (Q i).U x ∩ (Q i).U x' :=
      fun i => ⟨Set.mem_iInter.1 hy.1 i, Set.mem_iInter.1 hy.2 i⟩
    choose W hWo hyW G hG hEq using fun i => (hQ i).2 x x' y (hy' i)
    refine ⟨⋂ i, W i, isOpen_iInter_of_finite hWo, Set.mem_iInter.2 hyW, fun z => ∑ i, G i z,
      fun j => ?_, fun z hz => ?_⟩
    · have h : ∀ i ∈ (Finset.univ : Finset (Fin m)), AnalyticOnNhd ℂ (G i ∘ (B.chart j).symm)
          ((B.chart j).target ∩ (B.chart j).symm ⁻¹' ⋂ i, W i) := fun i _ => (hG i j).mono
        (Set.inter_subset_inter_right _ (Set.preimage_mono (Set.iInter_subset _ i)))
      convert Finset.analyticOnNhd_sum Finset.univ h using 1
      ext t
      simp [Finset.sum_apply]
    · obtain ⟨⟨hzW, hzU⟩, hzU'⟩ := hz
      show ∑ i, (Q i).φ x z - ∑ i, (Q i).φ x' z = (∑ i, G i z).re
      rw [Complex.re_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ => hEq i z
        ⟨⟨Set.mem_iInter.1 hzW i, Set.mem_iInter.1 hzU i⟩, Set.mem_iInter.1 hzU' i⟩

theorem isSection_sumPot (B : FinHolAtlas n Y) {m : ℕ} (Q : Fin m → LocPot Y)
    (τ : Fin m → Y → Y → ℂ) (hτ : ∀ i, IsSection B (Q i) (τ i)) :
    IsSection B (sumPot Q) (fun y z => ∏ i, τ i y z) := by
  refine ⟨fun x j => ?_, fun x x' y hy => ?_⟩
  · have h : ∀ i ∈ (Finset.univ : Finset (Fin m)), AnalyticOnNhd ℂ (τ i x ∘ (B.chart j).symm)
        ((B.chart j).target ∩ (B.chart j).symm ⁻¹' (sumPot Q).U x) := fun i _ => ((hτ i).1 x j).mono
      (Set.inter_subset_inter_right _ (Set.preimage_mono (Set.iInter_subset (fun i => (Q i).U x) i)))
    exact Finset.analyticOnNhd_fun_prod Finset.univ h
  · have key : ∀ x'' : Y, ‖∏ i, τ i x'' y‖ * Real.exp (-(sumPot Q).φ x'' y) =
        ∏ i, (‖τ i x'' y‖ * Real.exp (-(Q i).φ x'' y)) := by
      intro x''
      simp only [sumPot, norm_prod, ← Finset.sum_neg_distrib, Real.exp_sum, Finset.prod_mul_distrib]
    show ‖∏ i, τ i x y‖ * Real.exp (-(sumPot Q).φ x y) = ‖∏ i, τ i x' y‖ * Real.exp (-(sumPot Q).φ x' y)
    rw [key x, key x']
    exact Finset.prod_congr rfl fun i _ =>
      (hτ i).2 x x' y ⟨Set.mem_iInter.1 hy.1 i, Set.mem_iInter.1 hy.2 i⟩

end GlobalTheory.ProdSecPot

namespace GlobalTheory

open GlobalTheory.ProdSecPot

theorem isBd_pullback_boundary : ∀ (d : ℕ) (X : Type) [TopologicalSpace X] (A : FinHolAtlas d X) (m : ℕ) (Λ : Fin m → LocPot X) (σ : Fin m → X → X → ℂ), (∀ i, IsPotential A (Λ i) ∧ IsSection A (Λ i) (σ i) ∧ ∀ y, normSec (Λ i) (σ i) y ≤ 1) → ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [CompactSpace Y] [T2Space Y] (B : FinHolAtlas n Y) (μ : Y → X), HoloMap B A μ → (∀ i, interior {y | σ i (μ y) (μ y) = 0} = ∅) → ∀ Om : LocPot Y, IsPotential B Om → IsPosPot B Om → GlobalTheory.Mean4O.IsBd B (μ ⁻¹' boundary σ) (fun y => Real.exp 1 - 2 * ∑ i, logNormSec (Λ i) (σ i) (μ y)) Om := by
  intro d X _ A m Λ σ hΛ n Y _ _ _ B μ hμ hint Om hO hPos
  let Q : Fin m → LocPot Y := fun i => (Λ i).pullback μ hμ.1
  let τ : Fin m → Y → Y → ℂ := fun i y z => σ i (μ y) (μ z)
  have hQp : ∀ i, IsPotential B (Q i) := fun i => isPotentialPullback A B μ hμ (Λ i) (hΛ i).1
  have hτ : ∀ i, IsSection B (Q i) (τ i) :=
    fun i => isSection_pullback_holoMap d n X Y A B μ hμ (Λ i) (σ i) (hΛ i).2.1
  let L := sumPot Q
  let t : Y → Y → ℂ := fun y z => ∏ i, τ i y z
  have hL : IsPotential B L := isPotential_sumPot B Q hQp
  have hS : IsSection B L t := isSection_sumPot B Q τ hτ
  have hZ : μ ⁻¹' boundary σ = ReciprocityTheory.AnForm.P.bdry t := by
    ext y
    simp [boundary, ReciprocityTheory.AnForm.P.bdry, t, τ, Finset.prod_eq_zero_iff]
  have hle : ∀ i x, logNormSec (Λ i) (σ i) x ≤ 0 := fun i x =>
    Real.log_nonpos (mul_nonneg (norm_nonneg _) (Real.exp_pos _).le) ((hΛ i).2.2 x)
  have hr : ∀ y, y ∉ ReciprocityTheory.AnForm.P.bdry t →
      (fun y => Real.exp 1 - 2 * ∑ i, logNormSec (Λ i) (σ i) (μ y)) y = ReciprocityTheory.AnForm.P.rW L t y := by
    intro y hy
    have hy' : ∀ i, σ i (μ y) (μ y) ≠ 0 := by
      intro i h
      exact hy (Finset.prod_eq_zero (Finset.mem_univ i) h)
    show _ = Real.exp 1 - 2 * Real.log (‖∏ i, σ i (μ y) (μ y)‖ * Real.exp (-∑ i, (Λ i).φ (μ y) (μ y)))
    rw [norm_prod, ← Finset.sum_neg_distrib, Real.exp_sum, ← Finset.prod_mul_distrib,
      Real.log_prod (fun i _ => mul_ne_zero (norm_ne_zero_iff.2 (hy' i)) (Real.exp_pos _).ne')]
    rfl
  have hi : interior (ReciprocityTheory.AnForm.P.bdry t) = ∅ := by
    rw [interior_eq_empty_iff_dense_compl]
    have hc : (ReciprocityTheory.AnForm.P.bdry t)ᶜ = ⋂ i, {y | σ i (μ y) (μ y) = 0}ᶜ := by
      ext y
      simp [ReciprocityTheory.AnForm.P.bdry, t, τ, Finset.prod_eq_zero_iff]
    rw [hc]
    refine dense_iInter_of_isOpen (fun i => ?_) (fun i => ?_)
    · exact (ReciprocityTheory.AnForm.P.LeviFormBoundaryTopology.isClosed_bdry (hτ i)).isOpen_compl
    · exact interior_eq_empty_iff_dense_compl.1 (hint i)
  have he : ∀ y, Real.exp 1 ≤ Real.exp 1 - 2 * ∑ i, logNormSec (Λ i) (σ i) (μ y) := fun y => by
    have := Finset.sum_nonpos fun i (_ : i ∈ Finset.univ) => hle i (μ y)
    linarith
  rw [hZ]
  exact ⟨ReciprocityTheory.AnForm.P.LeviFormBoundaryTopology.isClosed_bdry hS, GlobalTheory.Mean4O.BdSec.bdry_null_chart hS hi, hO, hPos,
    GlobalTheory.Mean4O.BdSec.smoothOn hL hS hr, fun y _ => he y, GlobalTheory.Mean4O.BdSec.toBot hL hS hr,
    GlobalTheory.Mean4O.BdSec.mIntegrable hL hS hr hi fun _ => hO, GlobalTheory.Mean4O.BdSec.exists_pshOff hO hPos hL hS hr⟩

end GlobalTheory
