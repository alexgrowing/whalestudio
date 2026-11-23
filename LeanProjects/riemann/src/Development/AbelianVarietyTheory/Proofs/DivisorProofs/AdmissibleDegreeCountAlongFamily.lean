import Mathlib
import Formalism.SharpRestriction.Divisibility.WeightDegreeSizes
import Formalism.SharpRestriction.SmoothDesignExistence.DGamSmooth
import Formalism.SharpRestriction.GlobalSchurBounds.ProductFirstZerothParts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NuAbsPlaceFine
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LossBoundNonneg
open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions NumberField Classical

noncomputable section

namespace GlobalTheory.AdmissibleDegree

open Formalism.MainNotions.G GlobalTheory.IndefiniteRowSideFullHecke.LevelLossDegreeBounds

theorem admissibleDegree_count_at_parameter_const {D : D7} (L : SizeData₂ D) (h : SizesAt L) (P : ParameterChoice' D L) (hK : KapDef D) (hx : 2 ≤ L.sc.x) :
    Formalism.MainNotions.WeightDegreeSizes.DegreeCountBound D L 40 := by
  intro u j hj
  obtain ⟨j1, j2⟩ := Finset.mem_Icc.1 hj
  have hf := GlobalTheory.FockDegreeFine.degree_fine L h P hK hx u j hj
  have w0 : ∀ τ, 0 ≤ wj D j τ := fun τ => (GlobalTheory.HCEntries.wj_bounds h hx j j1 j2 τ).1
  have s0 : 0 ≤ sizeOffTops D j := by
    unfold sizeOffTops; exact Finset.sum_nonneg fun τ _ => w0 τ
  have s1 : sizeOffTops D j ≤ ∑ τ : D.what₂.Tau, wj D j τ := by
    unfold sizeOffTops
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun τ _ _ => w0 τ
  have hc := GlobalTheory.LossItemsCompare.cube_le_eta P
  have hm : (1 : ℝ) ≤ D.R.m := by exact_mod_cast (by have := D.R.two_le_m; omega : 1 ≤ D.R.m)
  have ht : (1 : ℝ) ≤ D.R.t := GlobalTheory.HCEntries.one_le_letterBlockLength D
  have hk : (1 : ℝ) ≤ D.R.k := GlobalTheory.HCEntries.one_le_k D
  have he := L.etaSz_pos
  have hS := L.Sc_pos
  have hN0 : (0 : ℝ) ≤ D.R.N D.R.m := Nat.cast_nonneg _
  have hNm : Nm D = (D.R.N D.R.m : ℝ) := rfl
  have hN2 : (D.R.N D.R.m : ℝ) ^ 2 ≤ (D.R.m : ℝ) * D.R.t * L.etaSz := by
    have a1 : (D.R.N D.R.m : ℝ) ^ 2 ≤ 4 * (D.R.N D.R.m : ℝ) ^ 3 + 6 := by
      rcases le_total (D.R.N D.R.m : ℝ) 1 with hN1 | hN1
      · nlinarith [pow_nonneg hN0 3]
      · nlinarith [pow_nonneg hN0 2]
    have a2 : L.etaSz ≤ (D.R.m : ℝ) * D.R.t * L.etaSz := by
      have : (1 : ℝ) ≤ (D.R.m : ℝ) * D.R.t := by nlinarith
      nlinarith
    linarith
  have hf0 : (0 : ℝ) ≤ D.R.f := Nat.cast_nonneg _
  have hc0 : 0 ≤ (D.host.TT.card : ℝ) * L.sc.b' / L.sc.x :=
    div_nonneg (mul_nonneg (Nat.cast_nonneg _) (GlobalTheory.HCEntries.b'_pos L).le) (by linarith)
  have hkN : 0 ≤ (D.R.k : ℝ) * Nm D := by rw [hNm]; positivity
  have hdeg : degErr L ≤ 2 * ((D.R.f : ℝ) * ((D.R.k : ℝ) * L.Sc + (D.R.m : ℝ) * D.R.t * L.etaSz + (D.R.k : ℝ) * Nm D) +
      (D.host.TT.card : ℝ) * L.sc.b' / L.sc.x) := by
    unfold degErr
    have : (D.R.f : ℝ) * ((D.R.k : ℝ) * L.Sc + Nm D ^ 2 + (D.R.m : ℝ) * (D.R.t : ℝ) * L.etaSz) ≤
        2 * ((D.R.f : ℝ) * ((D.R.k : ℝ) * L.Sc + (D.R.m : ℝ) * D.R.t * L.etaSz + (D.R.k : ℝ) * Nm D)) := by
      rw [hNm] at hkN ⊢
      have hkS : 0 ≤ (D.R.k : ℝ) * L.Sc := by positivity
      have := mul_le_mul_of_nonneg_left (show (D.R.k : ℝ) * L.Sc + (D.R.N D.R.m : ℝ) ^ 2 + (D.R.m : ℝ) * D.R.t * L.etaSz ≤
        2 * ((D.R.k : ℝ) * L.Sc + (D.R.m : ℝ) * D.R.t * L.etaSz + (D.R.k : ℝ) * (D.R.N D.R.m : ℝ)) by linarith) hf0
      linarith
    linarith
  unfold Formalism.MainNotions.WeightDegreeSizes.DegreeCountBound Formalism.MainNotions.WeightDegreeSizes.errG Formalism.MainNotions.WeightDegreeSizes.sumA at *
  change |degPi D u j - (fockDeg D j : ℝ) - topSum L| ≤ _
  rw [abs_le] at hf ⊢
  constructor <;> nlinarith [hf.1, hf.2]

theorem admissibleDegreeCount_along_family : ∀ {eps : ℝ} (Fm : FamP eps), 0 < eps → eps < 1 / 52 → ∃ C x0 : ℝ, 0 ≤ C ∧ ∀ x, x0 ≤ x →
    ∀ hx : Fm.x1 < x, ∀ i : Fm.Ix x, Formalism.MainNotions.WeightDegreeSizes.DegreeCountBound (Fm.D x i) (Fm.L x i) C := by
  intro eps Fm _ _
  refine ⟨40, 2, by norm_num, fun x hx2 hx i => ?_⟩
  have y := hx2
  rw [← Fm.L_x x i hx] at y
  exact admissibleDegree_count_at_parameter_const (Fm.L x i) (Fm.sizes x hx i) (Fm.params x hx i) (Fm.ex x hx i).kap_def y

end GlobalTheory.AdmissibleDegree
