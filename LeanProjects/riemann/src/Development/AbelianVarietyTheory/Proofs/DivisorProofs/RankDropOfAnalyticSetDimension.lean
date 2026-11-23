import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasHoloImmOfFiniteClosedCover
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PointDimensionLtProjectiveLine

namespace GlobalTheory.LogResInt
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GlobalTheory.IndefiniteRowSideFullHecke.BoundaryPolynomialFunctions

noncomputable section

theorem rankDrop_of_analyticSetDimension (hP : GlobalTheory.Published.AnalyticSetDimension) :
    ∀ (d : ℕ) (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (A : FinHolAtlas d X) (m : ℕ) (Λ : Fin m → LocPot X) (σ : Fin m → X → X → ℂ),
    (∀ i, IsPotential A (Λ i) ∧ IsSection A (Λ i) (σ i)) →
    ∀ (Z : Set X) (n : ℕ), IsIrreducibleAnalytic A Z → (regularLocus A Z n).Nonempty →
    ¬ Z ⊆ boundary σ →
    ∀ (L : LocPot X) (s : X → X → ℂ), IsPotential A L → IsSection A L s → (∃ y ∈ Z, s y y ≠ 0) →
    (∀ C, IsIrreducibleComponent A (Z ∩ boundary σ) C → ∃ y ∈ C, s y y ≠ 0) →
    ∀ (Y : Type) [TopologicalSpace Y] [CompactSpace Y] [T2Space Y] (B : FinHolAtlas n Y) (μ : Y → X),
    HoloMap B A μ → Set.range μ = Z → ∀ (r : ℕ) (W : Fin r → Set Y) (e : Fin (m + 1) → Fin r → ℕ),
    IsJointSNC B μ (Fin.cons L Λ) (Fin.cons s σ) W e →
    ∀ k, 1 ≤ e 0 k → (∃ i : Fin m, 1 ≤ e i.succ k) → RankDropAlong A μ B (W k) := by
  intro d X _ _ _ A m Λ σ hΛ Z n hZ hreg hZbd L s hL hs hsZ hcomp Y _ _ _ B μ hμ hrange r W e hsnc
    k hk0 hki w hw χ a hχ hwχ hWχ
  by_contra hlt
  rw [not_lt] at hlt
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by have := a.2; omega⟩
  obtain ⟨i, hi⟩ := hki
  have hσ : ∀ i, IsSection A (Λ i) (σ i) := fun i => (hΛ i).2
  have hVT : ∀ w' ∈ W k, μ w' ∈ Z ∩ boundary σ ∩ {y | s y y = 0} := by
    intro w' hw'
    have h0 := jointSNC_vanish hsnc (i := 0) hk0 hw'
    have h1 := jointSNC_vanish hsnc (i := i.succ) hi hw'
    simp only [Fin.cons_zero, Fin.cons_succ] at h0 h1
    exact ⟨⟨hrange ▸ ⟨w', rfl⟩, i, h1⟩, h0⟩
  have hpiece := hasHoloImm_of_rank A B μ hμ (W k) _ hVT w χ a hχ hw hwχ hWχ (by simpa using hlt)
  obtain ⟨hP1, hP2, hP3⟩ := GlobalTheory.AnDim.immersedPieces hP d X A
  have hbd := isAnalyticSubset_boundary hσ
  have hZB := isAnalyticSubset_inter hZ.1 hbd
  obtain ⟨hfin, hunion⟩ := hP3 _ hZB
  rw [hunion] at hpiece
  obtain ⟨C, hC, hCp⟩ := hasHoloImm_of_finite_closed_cover hfin
    (fun C hC => isClosed_of_isAnalyticSubset hC.1.1.1) hpiece
  have hCs : ¬ C ⊆ {y | s y y = 0} := by
    obtain ⟨y, hyC, hy⟩ := hcomp C hC
    exact fun h => hy (h hyC)
  have hCn := hP2 C _ n' hC.1.1 (isAnalyticSubset_zero hs) hCs hCp
  have hZn := hP2 Z (boundary σ) (n' + 1) hZ hbd hZbd (hCn.mono hC.1.2)
  exact hP1 Z (n' + 1) hZ hreg hZn

end

end GlobalTheory.LogResInt
