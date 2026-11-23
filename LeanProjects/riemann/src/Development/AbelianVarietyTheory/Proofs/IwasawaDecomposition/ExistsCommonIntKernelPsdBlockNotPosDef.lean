import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLieBase
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.HodgePeriodGram
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeChartBoundsOfSchurLemW
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PerValNeZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsExponentialChartAtPoint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsExponentialOfSemiAbelianFibreLinearChange
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open Matrix
open scoped ComplexOrder Topology
open GlobalTheory.ShFam.Hor GlobalTheory.CxPts
open MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.ShFam.Hor.LogCh
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem intPsd_common_kernel_of_sum_not_posDef : ∀ (a g rk : ℕ) (B : Fin a → Matrix (Fin g) (Fin g) ℤ), (∀ k, ((B k).map (Int.cast : ℤ → ℝ)).PosSemidef) → (∀ k (j l : Fin g), (rk ≤ j.val ∨ rk ≤ l.val) → B k j l = 0) → ¬ (((∑ k, B k).map (Int.cast : ℤ → ℝ)).submatrix (Subtype.val : {j : Fin g // j.val < rk} → Fin g) Subtype.val).PosDef → ∃ v : Fin g → ℤ, v ≠ 0 ∧ (∀ j : Fin g, rk ≤ j.val → v j = 0) ∧ ∀ k, (B k).mulVec v = 0 := by
  intro a g rk B hpsd hsupp hnot
  set S : Matrix (Fin g) (Fin g) ℤ := ∑ k, B k with hS
  let e : {j : Fin g // j.val < rk} → Fin g := Subtype.val
  have hcast : ∀ (M : Matrix (Fin g) (Fin g) ℤ) (u : Fin g → ℤ) (i : Fin g),
      ((M.map (Int.cast : ℤ → ℝ)) *ᵥ (fun j => (u j : ℝ))) i = (((M *ᵥ u) i : ℤ) : ℝ) := by
    intro M u i
    simp [mulVec, dotProduct]
  have hSmap : S.map (Int.cast : ℤ → ℝ) = ∑ k, (B k).map (Int.cast : ℤ → ℝ) := by
    ext i j; simp [hS, Matrix.sum_apply]
  have hSR : ((S.map (Int.cast : ℤ → ℝ)).submatrix e e).PosSemidef := by
    rw [hSmap]
    exact (posSemidef_sum _ (fun k _ => hpsd k)).submatrix e
  have hdetR : ((S.map (Int.cast : ℤ → ℝ)).submatrix e e).det = 0 := by
    by_contra hdet
    apply hnot
    rw [posDef_iff_dotProduct_mulVec]
    refine ⟨hSR.isHermitian, fun x hx => ?_⟩
    have hnn := (posSemidef_iff_dotProduct_mulVec.1 hSR).2 x
    rcases hnn.lt_or_eq with h | h
    · exact h
    · exfalso
      have hk := (hSR.dotProduct_mulVec_zero_iff x).1 h.symm
      exact hdet (exists_mulVec_eq_zero_iff.1 ⟨x, hx, hk⟩)
  have hdetZ : (S.submatrix e e).det = 0 := by
    have h := (Int.castRingHom ℝ).map_det (S.submatrix e e)
    have h2 : (Int.castRingHom ℝ).mapMatrix (S.submatrix e e)
        = (S.map (Int.cast : ℤ → ℝ)).submatrix e e := rfl
    rw [h2, hdetR, eq_intCast] at h
    exact_mod_cast h
  obtain ⟨w, hw0, hw⟩ := exists_mulVec_eq_zero_iff.2 hdetZ
  let v : Fin g → ℤ := fun j => if h : j.val < rk then w ⟨j, h⟩ else 0
  have hSi : ∀ i j : Fin g, rk ≤ i.val → S i j = 0 := by
    intro i j hi
    simp [hS, Matrix.sum_apply, hsupp _ i j (Or.inl hi)]
  have hsplit : ∀ i : Fin g, (S *ᵥ v) i = ∑ j : {j : Fin g // j.val < rk}, S i j * w j := by
    intro i
    simp only [mulVec, dotProduct]
    rw [← Fintype.sum_subtype_add_sum_subtype (fun j : Fin g => j.val < rk)]
    have h2 : ∑ j : {j : Fin g // ¬ j.val < rk}, S i j * v j = 0 := by
      refine Finset.sum_eq_zero fun j _ => ?_
      simp [v, j.2]
    rw [h2, add_zero]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp [v, j.2]
  have hSv : S *ᵥ v = 0 := by
    funext i
    rw [hsplit]
    by_cases hi : i.val < rk
    · have := congrFun hw ⟨i, hi⟩
      simpa [mulVec, dotProduct, e] using this
    · push_neg at hi
      simp [hSi i _ hi]
  refine ⟨v, ?_, ?_, ?_⟩
  · intro hv
    apply hw0
    funext j
    have := congrFun hv j.val
    simpa [v, j.2] using this
  · intro j hj
    simp [v, not_lt.2 hj]
  · intro k
    let vR : Fin g → ℝ := fun j => (v j : ℝ)
    have hQnn : ∀ k, 0 ≤ star vR ⬝ᵥ (((B k).map (Int.cast : ℤ → ℝ)) *ᵥ vR) := fun k =>
      (posSemidef_iff_dotProduct_mulVec.1 (hpsd k)).2 vR
    have hsum : ∑ k, star vR ⬝ᵥ (((B k).map (Int.cast : ℤ → ℝ)) *ᵥ vR) = 0 := by
      rw [← dotProduct_sum, ← sum_mulVec, ← hSmap]
      have : (S.map (Int.cast : ℤ → ℝ)) *ᵥ vR = 0 := by
        funext i; rw [hcast, hSv]; simp
      rw [this, dotProduct_zero]
    have hk0 := (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => hQnn k)).1 hsum k (Finset.mem_univ _)
    have hker := ((hpsd k).dotProduct_mulVec_zero_iff vR).1 hk0
    funext i
    have := congrFun hker i
    rw [hcast] at this
    simpa using this

end GlobalTheory
