import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StokesOffDiscriminantWindow
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets StokesOffDiscriminant
open scoped ContDiff Manifold

noncomputable section

theorem StokesOffDiscriminant.proof : StokesOffDiscriminant.Statement := by
  intro n d J A P _ _ _ _ hsheet F G φ hF hG hφ hFc ⟨U, hUo, hPU, hFU⟩
  set K := closure {x | x ∈ zeroSet J ∧ F x ≠ 0} with hKdef
  have hKZ : K ⊆ zeroSet J :=
    closure_minimal (fun x hx => hx.1) (SheetSumMeasurable.isClosed_zeroSet J)
  have hKU : K ⊆ Uᶜ :=
    closure_minimal (fun x hx hxU => hx.2 (hFU x ⟨hxU, hx.1⟩)) hUo.isClosed_compl
  have hKc : IsCompact K := hFc.of_isClosed_subset isClosed_closure (closure_mono fun x hx => hx.2)
  have hwin : ∀ x : K, ∃ (s : (Fin (d + 1) → ℂ) → Fin n → ℂ) (V : Set (Fin (d + 1) → ℂ))
      (W : Set (Fin n → ℂ)), IsOpen V ∧ IsOpen W ∧ (x : Fin n → ℂ) ∈ W ∧ DifferentiableOn ℂ s V ∧
        (∀ y ∈ V, A *ᵥ s y = y ∧ s y ∈ zeroSet J) ∧
        ∀ x' ∈ zeroSet J ∩ W, A *ᵥ x' ∈ V ∧ IsSheetAt J A x' s := by
    rintro ⟨x, hx⟩
    obtain ⟨s, hs⟩ := hsheet x (hKZ hx) fun h => hKU hx (hPU h)
    exact ⟨s, window_of_sheet hs⟩
  choose s V W hVo hWo hxW hsd hsec hWs using hwin
  obtain ⟨t, ht⟩ := hKc.elim_finite_subcover W hWo fun x hx => Set.mem_iUnion.2 ⟨⟨x, hx⟩, hxW _⟩
  obtain ⟨ρ, hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate 𝓘(ℝ, Fin n → ℂ) isClosed_closure
    (fun i : t => W i.1) (fun i => hWo i.1) fun x hx => by
      obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.1 (ht hx)
      exact Set.mem_iUnion.2 ⟨⟨i, hi⟩, hxi⟩
  have hρs : ∀ i, ContDiff ℝ ∞ (ρ i) := fun i => contMDiff_iff_contDiff.1 (ρ i).contMDiff
  set f : t → (Fin n → ℂ) → ℝ := fun i x => ρ i x * F x with hfdef
  have hsum : ∀ x ∈ zeroSet J, F x = ∑ i, f i x := by
    intro x hxZ
    by_cases hK : x ∈ K
    · have h1 := ρ.sum_eq_one hK
      rw [finsum_eq_sum_of_fintype] at h1
      simp only [hfdef, ← Finset.sum_mul, h1, one_mul]
    · have hF0 : F x = 0 := by_contra fun h => hK (subset_closure ⟨hxZ, h⟩)
      simp [hfdef, hF0]
  have hfs : ∀ i, SmoothNear (zeroSet J) (f i) := by
    obtain ⟨O, hO, hZO, hFO⟩ := hF
    exact fun i => ⟨O, hO, hZO, (hρs i).contDiffOn.mul hFO⟩
  have hfW : ∀ i, tsupport (f i) ⊆ W i.1 := fun i => tsupport_mul_subset_left.trans (hρ i)
  have hpiece := fun i : t => window_stokes (hVo i.1) (hsd i.1) (hsec i.1) (hWs i.1) (f i) G φ
    (hfs i) hG hφ hFc.mul_left (hfW i)
  have hL : ∀ y, chartDens J A F (vecCons G φ) y = ∑ i, chartDens J A (f i) (vecCons G φ) y := by
    intro y
    unfold chartDens
    refine sheetSum_finset_sum Finset.univ _
      (fun i x s' => f i x * ReciprocityTheory.AnForm.maDens (fun k => vecCons G φ k ∘ s') y) ?_
      fun i _ => finite_support_sheetTerm_window
        (sheetTerm_weight_window (hsec i.1) (hWs i.1) (f i) (hfW i) _ y)
    intro x hx s' _
    rw [hsum x hx.1, Finset.sum_mul]
  have hR : ∀ y, chartDens J A G (vecCons F φ) y = ∑ i, chartDens J A G (vecCons (f i) φ) y := by
    intro y
    unfold chartDens
    refine sheetSum_finset_sum Finset.univ _
      (fun i x s' => G x * ReciprocityTheory.AnForm.maDens (fun k => vecCons (f i) φ k ∘ s') y) ?_
      fun i _ => finite_support_sheetTerm_window
        (sheetTerm_cons_window (hVo i.1) (hsd i.1) (hsec i.1) (hWs i.1) (f i) G (hfW i) φ y)
    rintro x ⟨-, rfl⟩ s' hs'
    rw [maDens_sheet_finset_sum Finset.univ F f φ hs' hsum fun i _ => hfs i, Finset.mul_sum]
  unfold chartInt
  simp only [hL, hR]
  rw [integral_finsetSum _ fun i _ => (hpiece i).2.1, integral_finsetSum _ fun i _ => (hpiece i).2.2]
  exact Finset.sum_congr rfl fun i _ => (hpiece i).1

end

end GroundTheory.Heights₂.Heights
