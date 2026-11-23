import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TotalEqCurve
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjacentPullPull
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernOneEqNegDdcLogDet
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernDensDetWeightEqNegLeviLog
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetBlockChangeOfBasisViaTwoFamiliesImplicit
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.ArakelovInstances.LminorMapConj
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Points GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.ArInt GlobalTheory.MixDens GlobalTheory.CovTest
open GlobalTheory.FlagFibre (Low uni dens)
open ReciprocityTheory.L2DbarEstimates (V cHess)
open scoped ContDiff ComplexOrder Classical

namespace GlobalTheory.FlagFibre

theorem det_eq_prod_diag_of_strict {α R : Type*} [Fintype α] [DecidableEq α] [CommRing R]
    (M : Matrix α α R) (f : α → ℕ) (h : ∀ s t, M s t ≠ 0 → s ≠ t → f s < f t) :
    M.det = ∏ s, M s s := by
  rw [det_apply, Finset.sum_eq_single 1]
  · simp
  · intro σ _ hσ
    have : ∃ i, M (σ i) i = 0 := by
      by_contra hne
      push_neg at hne
      have hle : ∀ i, f (σ i) ≤ f i := fun i => by
        by_cases hi : σ i = i
        · rw [hi]
        · exact (h _ _ (hne i) hi).le
      have hsum : ∑ i, f (σ i) = ∑ i, f i := Equiv.sum_comp σ f
      have heq := (Finset.sum_eq_sum_iff_of_le (fun i _ => hle i)).1 hsum
      apply hσ
      refine Equiv.ext fun i => ?_
      rw [Equiv.Perm.one_apply]
      by_contra hi
      exact absurd (heq i (Finset.mem_univ _)) (h _ _ (hne i) hi).ne
    obtain ⟨i, hi⟩ := this
    rw [Finset.prod_eq_zero (f := fun j => M (σ j) j) (Finset.mem_univ i) hi, smul_zero]
  · simp

theorem diag_mul_of_upper {m : ℕ} (N P : Matrix (Fin m) (Fin m) ℂ)
    (hN : ∀ a c : Fin m, c < a → N a c = 0) (hP : ∀ a c : Fin m, c < a → P a c = 0) (a : Fin m) :
    (N * P) a a = N a a * P a a := by
  rw [mul_apply, Finset.sum_eq_single a]
  · intro c _ hc
    rcases lt_or_gt_of_ne hc with h | h
    · rw [hN a c h, zero_mul]
    · rw [hP c a h, mul_zero]
  · simp

theorem uni_inv_lower {m : ℕ} (n : Low m → ℂ) : ∀ a c : Fin m, a < c → (uni n)⁻¹ a c = 0 := by
  have hU : (uni n).BlockTriangular OrderDual.toDual := by
    intro i j hij
    have h' : i < j := hij
    simp [uni, not_lt_of_gt h', h'.ne]
  letI := (uni n).invertibleOfIsUnitDet (by rw [det_uni]; exact isUnit_one)
  have := blockTriangular_inv_of_blockTriangular hU
  intro a c hac
  exact this (show OrderDual.toDual c < OrderDual.toDual a from hac)

theorem uni_inv_diag {m : ℕ} (n : Low m → ℂ) (a : Fin m) : (uni n)⁻¹ a a = 1 := by
  have h1 : ((uni n)⁻¹ * uni n) a a = 1 := by
    rw [nonsing_inv_mul _ (by rw [det_uni]; exact isUnit_one), one_apply_eq]
  have hU : ∀ a c : Fin m, a < c → uni n a c = 0 := by
    intro i j h'
    simp [uni, not_lt_of_gt h', h'.ne]
  rw [mul_apply, Finset.sum_eq_single a] at h1
  · simpa [uni] using h1
  · intro c _ hc
    rcases lt_or_gt_of_ne hc with h | h
    · rw [hU c a h, mul_zero]
    · rw [uni_inv_lower n a c h, zero_mul]
  · simp

theorem inv_upper {m : ℕ} (T : Matrix (Fin m) (Fin m) ℂ) (hT : ∀ a c : Fin m, c < a → T a c = 0)
    (hdet : IsUnit T.det) : ∀ a c : Fin m, c < a → T⁻¹ a c = 0 := by
  letI := T.invertibleOfIsUnitDet hdet
  have hU : T.BlockTriangular id := fun i j h => hT i j h
  have := blockTriangular_inv_of_blockTriangular hU
  intro a c hac
  exact this hac

theorem inv_diag_mul {m : ℕ} (T : Matrix (Fin m) (Fin m) ℂ) (hT : ∀ a c : Fin m, c < a → T a c = 0)
    (hdet : IsUnit T.det) (a : Fin m) : T⁻¹ a a * T a a = 1 := by
  rw [← diag_mul_of_upper _ _ (inv_upper T hT hdet) hT, nonsing_inv_mul _ hdet, one_apply_eq]

end GlobalTheory.FlagFibre

namespace GlobalTheory.FlagFibre

theorem det_lowConj : ∀ {m : ℕ} (n : Low m → ℂ) (T : Matrix (Fin m) (Fin m) ℂ), (∀ a c : Fin m, c < a → T a c = 0) → IsUnit T.det → (Matrix.of fun s t : Low m => (T⁻¹ * (uni n)⁻¹) s.1.1 t.1.1 * T t.1.2 s.1.2).det = ∏ s : Low m, T s.1.2 s.1.2 / T s.1.1 s.1.1 := by
  intro m n T hT hdet
  let M3 : Matrix (Low m) (Low m) ℂ := Matrix.of fun s u => T⁻¹ s.1.1 u.1.1 * T u.1.2 s.1.2
  let M1 : Matrix (Low m) (Low m) ℂ :=
    Matrix.of fun u t => (uni n)⁻¹ u.1.1 t.1.1 * (if u.1.2 = t.1.2 then 1 else 0)
  have hfac : Matrix.of (fun s t : Low m => (T⁻¹ * (uni n)⁻¹) s.1.1 t.1.1 * T t.1.2 s.1.2) = M3 * M1 := by
    ext s t
    let g : Fin m × Fin m → ℂ := fun u =>
      T⁻¹ s.1.1 u.1 * T u.2 s.1.2 * ((uni n)⁻¹ u.1 t.1.1 * if u.2 = t.1.2 then 1 else 0)
    have hsub : ∑ u : Low m, g u.1 = ∑ u : Fin m × Fin m, g u := by
      rw [← Finset.sum_subtype (Finset.univ.filter fun u : Fin m × Fin m => u.2 < u.1) (by simp) g]
      apply Finset.sum_subset (Finset.subset_univ _)
      intro u _ hu
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at hu
      by_cases h2 : u.2 = t.1.2
      · have : u.1 < t.1.1 := lt_of_le_of_lt hu (h2 ▸ t.2)
        simp [g, uni_inv_lower n _ _ this]
      · simp [g, h2]
    have hM : (M3 * M1) s t = ∑ u : Low m, g u.1 := by
      simp only [M3, M1, g, mul_apply, of_apply]
    rw [hM, hsub, Fintype.sum_prod_type]
    simp only [g, of_apply, mul_apply, Finset.sum_mul, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
    refine Finset.sum_congr rfl fun c _ => ?_
    ring
  have hd3 : M3.det = ∏ s : Low m, T⁻¹ s.1.1 s.1.1 * T s.1.2 s.1.2 := by
    refine det_eq_prod_diag_of_strict M3 (fun s => s.1.1 + (m - s.1.2)) ?_
    intro s u hne hsu
    simp only [M3, of_apply] at hne
    have h1 : ¬ u.1.1 < s.1.1 := fun h => hne (by rw [inv_upper T hT hdet _ _ h, zero_mul])
    have h2 : ¬ s.1.2 < u.1.2 := fun h => hne (by rw [hT _ _ h, mul_zero])
    have hne' : s.1.1 ≠ u.1.1 ∨ s.1.2 ≠ u.1.2 := by
      by_contra hc
      push_neg at hc
      exact hsu (Subtype.ext (Prod.ext hc.1 hc.2))
    simp only [not_lt, Fin.le_def, ne_eq, Fin.ext_iff] at h1 h2 hne'
    have := s.1.2.2
    have := u.1.2.2
    omega
  have hd1 : M1.det = 1 := by
    rw [det_eq_prod_diag_of_strict M1 (fun u => m - u.1.1)]
    · simp [M1, uni_inv_diag]
    · intro u t hne hut
      simp only [M1, of_apply] at hne
      have h2 : u.1.2 = t.1.2 := by
        by_contra h; exact hne (by simp [h])
      have h1 : ¬ u.1.1 < t.1.1 := fun h => hne (by rw [uni_inv_lower n _ _ h, zero_mul])
      have h3 : u.1.1 ≠ t.1.1 := fun h => hut (Subtype.ext (Prod.ext h h2))
      simp only [not_lt, Fin.le_def, ne_eq, Fin.ext_iff] at h1 h3
      have := u.1.1.2
      have := t.1.1.2
      show m - (u.1.1 : ℕ) < m - t.1.1
      omega
  rw [hfac, det_mul, hd3, hd1, mul_one]
  refine Finset.prod_congr rfl fun s _ => ?_
  have hinv := inv_diag_mul T hT hdet s.1.1
  have hne : T s.1.1 s.1.1 ≠ 0 := right_ne_zero_of_mul_eq_one hinv
  rw [eq_inv_of_mul_eq_one_left hinv, div_eq_inv_mul]

end GlobalTheory.FlagFibre
