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

open ReciprocityTheory.ChartRestriction.G.FD (lminor)

noncomputable section

namespace GlobalTheory.TriJacDens

theorem prod_low {m : ℕ} (f : Fin m → Fin m → ℝ) :
    ∏ s : Low m, f s.1.1 s.1.2 = ∏ b : Fin m, ∏ c : Fin m, if c < b then f b c else 1 := by
  rw [← Finset.prod_product', Finset.univ_product_univ, ← Finset.prod_filter]
  exact (Finset.prod_subtype _ (by simp) (fun s : Fin m × Fin m => f s.1 s.2)).symm

theorem prod_low_mul {m : ℕ} (t : Fin m → ℝ) :
    (∏ s : Low m, t s.1.1) * ∏ s : Low m, t s.1.2 = (∏ c, t c) ^ (m - 1) := by
  rw [prod_low (fun b _ => t b), prod_low (fun _ c => t c), Finset.prod_comm (f := fun b c => if c < b then t c else 1),
    ← Finset.prod_mul_distrib, ← Finset.prod_pow]
  refine Finset.prod_congr rfl fun b _ => ?_
  rw [← Finset.prod_mul_distrib]
  have e : ∀ c : Fin m, ((if c < b then t b else 1) * if b < c then t b else 1) = if c ≠ b then t b else 1 := by
    intro c
    rcases lt_trichotomy c b with h | h | h
    · simp [h, h.ne, not_lt_of_gt h]
    · simp [h]
    · simp [h, h.ne', not_lt_of_gt h]
  rw [Finset.prod_congr rfl fun c _ => e c, ← Finset.prod_filter, Finset.prod_const, Finset.filter_ne',
    Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]

theorem prod_castLE {m k : ℕ} (hk : k ≤ m) (t : Fin m → ℝ) :
    ∏ a : Fin k, t (a.castLE hk) = ∏ c : Fin m, if (c : ℕ) < k then t c else 1 := by
  rw [← Finset.prod_filter]
  refine Finset.prod_bij (fun a _ => a.castLE hk) (by simp) (fun a _ b _ h => Fin.castLE_injective hk h) ?_ (fun _ _ => rfl)
  intro c hc
  exact ⟨⟨c, by simpa using hc⟩, Finset.mem_univ _, rfl⟩

theorem lminor_mul_eq_one {m : ℕ} (M T : Matrix (Fin m) (Fin m) ℂ) (hT : ∀ a c : Fin m, c < a → T a c = 0)
    (h : chg T M = 1) (k : Fin (m + 1)) :
    lminor M k * ((∏ c : Fin m, if (c : ℕ) < k then ‖T c c‖ ^ 2 else 1 : ℝ) : ℂ) = 1 := by
  have hU : ∀ a c : Fin m, c < a → Tᴴᵀ a c = 0 := fun a c hc => by simp [hT a c hc]
  have e := ReciprocityTheory.ChartRestriction.G.AR.Inst.CurvPf.lminor_LMU T M Tᴴᵀ hT hU k
  have D : ∀ S : Matrix (Fin m) (Fin m) ℂ, (∀ a c : Fin m, c < a → S a c = 0) → lminor S k =
      ∏ a : Fin k, S (a.castLE (Nat.le_of_lt_succ k.2)) (a.castLE (Nat.le_of_lt_succ k.2)) :=
    fun S hS => det_of_upperTriangular fun _ _ h => hS _ _ h
  change _ = lminor T k * _ * lminor Tᴴᵀ k at e
  rw [show Tᵀ * M * Tᴴᵀ = 1 from h, D T hT, D _ hU] at e
  have e1 : lminor (1 : Matrix (Fin m) (Fin m) ℂ) k = 1 := by
    rw [lminor, submatrix_one _ (Fin.castLE_injective _), det_one]
  rw [← prod_castLE (Nat.le_of_lt_succ k.isLt) (fun c => ‖T c c‖ ^ 2), ← e1, e, mul_right_comm, mul_comm,
    ← Finset.prod_mul_distrib, Complex.ofReal_prod]
  congr 1
  refine Finset.prod_congr rfl fun a _ => ?_
  simp [Complex.mul_conj, Complex.normSq_eq_norm_sq]

theorem prod_diag_eq_jacDens : ∀ {m : ℕ} (G : Matrix (Fin m) (Fin m) ℂ), G.PosDef → ∀ (n : Low m → ℂ) (T : Matrix (Fin m) (Fin m) ℂ), (∀ a c : Fin m, c < a → T a c = 0) → chg T (chg (uni n) G) = 1 → ∏ s : Low m, ‖T s.1.2 s.1.2 / T s.1.1 s.1.1‖ ^ 2 = jacDens G n := by
  intro m G _ n T hT h
  set M := chg (uni n) G with hM
  set t : Fin m → ℝ := fun c => ‖T c c‖ ^ 2 with ht
  have key := lminor_mul_eq_one M T hT h
  have hlast : lminor M (Fin.last m) = G.det := by
    have : lminor M (Fin.last m) = M.det := by
      rw [lminor]; congr 1
    rw [this, hM, det_chg, FlagFibre.det_uni]; simp
  have hdet : G.det * ((∏ c, t c : ℝ) : ℂ) = 1 := by
    have := key (Fin.last m)
    rw [hlast] at this
    simpa [ht] using this
  have hre : G.det.re * ∏ c, t c = 1 := by
    have := congrArg Complex.re hdet
    rwa [Complex.re_mul_ofReal, Complex.one_re] at this
  have hP : ∏ c, t c ≠ 0 := right_ne_zero_of_mul_eq_one hre
  have htne : ∀ c, t c ≠ 0 := fun c => Finset.prod_ne_zero_iff.1 hP c (Finset.mem_univ _)
  have htr : (uni n)ᴴ * Gᵀ * uni n = Mᵀ := by
    simp only [hM, chg, transpose_mul, transpose_transpose, Matrix.mul_assoc]
  have hdens : dens Gᵀ n = (∏ s : Low m, t s.1.2) ^ 2 := by
    rw [dens, prod_low (fun _ c => t c), ← Finset.prod_pow]
    refine Finset.prod_congr rfl fun b _ => ?_
    have e : lminor Mᵀ b.castSucc = lminor M b.castSucc := by
      rw [lminor, lminor, ← transpose_submatrix, det_transpose]
    have e2 := congrArg norm (key b.castSucc)
    rw [norm_mul, norm_one, Complex.norm_real, Real.norm_eq_abs] at e2
    rw [htr, e, eq_inv_of_mul_eq_one_left e2, _root_.inv_zpow', neg_neg, zpow_ofNat, sq_abs]
    rfl
  have hB : ∏ s : Low m, t s.1.1 ≠ 0 := Finset.prod_ne_zero_iff.2 fun s _ => htne _
  have hA : ∏ s : Low m, t s.1.2 ≠ 0 := Finset.prod_ne_zero_iff.2 fun s _ => htne _
  have hL : ∏ s : Low m, ‖T s.1.2 s.1.2 / T s.1.1 s.1.1‖ ^ 2 = (∏ s : Low m, t s.1.2) / ∏ s : Low m, t s.1.1 := by
    rw [← Finset.prod_div_distrib]
    refine Finset.prod_congr rfl fun s _ => ?_
    rw [norm_div, div_pow]
  rw [hL, jacDens, hdens, eq_inv_of_mul_eq_one_left hre, inv_pow, ← prod_low_mul]
  field_simp

end GlobalTheory.TriJacDens
