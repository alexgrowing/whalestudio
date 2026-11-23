import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.SecondCountableTopologyArchUnitary

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField Module

theorem WeightedIndexBound.proof (E : Type*) [Field E] [NumberField E] [IsTotallyComplex E]
    (h₁ : CoeffLatticeBasis.Statement E) (h₂ : IndexLeDet.Statement E)
    (h₃ : WeightedNormSq.Statement E) (h₄ : WeightedSpaceDim.Statement E)
    (h₅ : ∀ [Fact (finrank ℝ (EuclideanSpace ℝ (InfinitePlace E × Fin 2)) = finrank ℚ E)],
      MinkowskiVolumeForm.Statement (EuclideanSpace ℝ (InfinitePlace E × Fin 2)) (finrank ℚ E))
    (h₆ : ∀ [Fact (finrank ℝ (EuclideanSpace ℝ (InfinitePlace E × Fin 2)) = finrank ℚ E)],
      VolumeFormIntComb.Statement (EuclideanSpace ℝ (InfinitePlace E × Fin 2)) (finrank ℚ E)) :
    WeightedIndexBound.Statement E := by
  intro c hc A hOA hFG hmin r ⟨a, ha, hr⟩
  have : Fact (finrank ℝ (EuclideanSpace ℝ (InfinitePlace E × Fin 2)) = finrank ℚ E) := ⟨h₄⟩
  obtain ⟨e⟩ := h₁ A hOA hFG
  have hmem : ∀ i, (a i : E) ∈ A := fun i => hOA ⟨a i, rfl⟩
  set T : Matrix (Fin (finrank ℚ E)) (Fin (finrank ℚ E)) ℤ := fun i j => e.repr ⟨(a i : E), hmem i⟩ j with hT
  have hcoe : ∀ z : Fin (finrank ℚ E) → ℤ, ((∑ j, z j • e j : A) : E) = ∑ j, z j • (e j : E) := by
    intro z
    change A.subtype _ = _
    rw [map_sum]
    simp only [map_zsmul]
    rfl
  have haT : ∀ i, (a i : E) = ∑ j, T i j • (e j : E) := by
    intro i
    rw [← hcoe]
    exact (congrArg Subtype.val (e.sum_repr ⟨(a i : E), hmem i⟩)).symm
  have hidx := h₂ A hOA e a T ha haT

  set Φ := weightedEmbed c with hΦ
  have hc0 : ∀ w, 0 ≤ c w := fun w => (hc w).le
  have hS : 0 < ∑ w, c w := Finset.sum_pos (fun w _ => hc w) Finset.univ_nonempty
  set lam := Real.sqrt (∑ w, c w) with hlam
  have hlam0 : 0 < lam := Real.sqrt_pos.2 hS
  have hlam2 : lam ^ 2 = ∑ w, c w := Real.sq_sqrt hS.le
  have hdpos : 0 < finrank ℚ E := Module.finrank_pos
  have hsd : 0 < Real.sqrt (finrank ℚ E) := Real.sqrt_pos.2 (by exact_mod_cast hdpos)
  set o : Orientation ℝ (EuclideanSpace ℝ (InfinitePlace E × Fin 2)) (Fin (finrank ℚ E)) :=
    (Module.finBasisOfFinrankEq ℝ _ h₄).orientation
  set b : Fin (finrank ℚ E) → EuclideanSpace ℝ (InfinitePlace E × Fin 2) := fun i => Φ (e i : E)

  have hmink : (lam / Real.sqrt (finrank ℚ E)) ^ finrank ℚ E ≤ |o.volumeForm b| := by
    refine h₅ o b lam hlam0 fun z hz => ?_
    have hsum : ∑ i, (z i : ℝ) • b i = Φ ((∑ i, z i • e i : A) : E) := by
      rw [hcoe, map_sum]
      simp only [map_zsmul, b, Int.cast_smul_eq_zsmul]
    rw [hsum]
    set x : A := ∑ i, z i • e i
    have hx : (x : E) ≠ 0 := by
      intro h0
      have hx0 : x = 0 := Subtype.ext h0
      obtain ⟨i, hi⟩ := Function.ne_iff.1 hz
      exact hi (Fintype.linearIndependent_iff.1 e.linearIndependent z hx0 i)
    have hq := hmin x x.2 hx
    rw [hlam, ← Real.sqrt_sq (norm_nonneg (Φ x)), h₃ c hc0]
    exact Real.sqrt_le_sqrt hq

  have hab : (fun i => Φ (a i : E)) = fun i => ∑ j, (T i j : ℝ) • b j := by
    funext i
    rw [haT i, map_sum]
    simp only [map_zsmul, b, Int.cast_smul_eq_zsmul]
  have hvol : o.volumeForm (fun i => Φ (a i : E)) = (T.det : ℝ) * o.volumeForm b := by
    rw [hab]; exact h₆ o b T

  have hr0 : 0 ≤ r := by
    obtain ⟨w⟩ : Nonempty (InfinitePlace E) := inferInstance
    exact (norm_nonneg _).trans (hr ⟨0, hdpos⟩ w.embedding)
  have hnorm : ∀ i, ‖Φ (a i : E)‖ ≤ r * lam := by
    intro i
    have h2 : ‖Φ (a i : E)‖ ^ 2 ≤ (r * lam) ^ 2 := by
      rw [h₃ c hc0, mul_pow, hlam2, Finset.mul_sum]
      refine Finset.sum_le_sum fun w _ => ?_
      have := pow_le_pow_left₀ (norm_nonneg _) (hr i w.embedding) 2
      nlinarith [hc0 w]
    nlinarith [norm_nonneg (Φ (a i : E)), mul_nonneg hr0 hlam0.le]
  have hhad : |o.volumeForm (fun i => Φ (a i : E))| ≤ (r * lam) ^ finrank ℚ E := by
    refine (o.abs_volumeForm_apply_le _).trans ?_
    calc ∏ i, ‖Φ (a i : E)‖ ≤ ∏ _i : Fin (finrank ℚ E), r * lam :=
          Finset.prod_le_prod (fun i _ => norm_nonneg _) (fun i _ => hnorm i)
      _ = (r * lam) ^ finrank ℚ E := by simp

  have hpos : 0 < (lam / Real.sqrt (finrank ℚ E)) ^ finrank ℚ E := pow_pos (div_pos hlam0 hsd) _
  have hkey : |(T.det : ℝ)| * (lam / Real.sqrt (finrank ℚ E)) ^ finrank ℚ E ≤
      (r * Real.sqrt (finrank ℚ E)) ^ finrank ℚ E * (lam / Real.sqrt (finrank ℚ E)) ^ finrank ℚ E := by
    calc |(T.det : ℝ)| * (lam / Real.sqrt (finrank ℚ E)) ^ finrank ℚ E
        ≤ |(T.det : ℝ)| * |o.volumeForm b| :=
          mul_le_mul_of_nonneg_left hmink (abs_nonneg _)
      _ = |o.volumeForm (fun i => Φ (a i : E))| := by rw [hvol, abs_mul]
      _ ≤ (r * lam) ^ finrank ℚ E := hhad
      _ = (r * Real.sqrt (finrank ℚ E)) ^ finrank ℚ E * (lam / Real.sqrt (finrank ℚ E)) ^ finrank ℚ E := by
          rw [← mul_pow]; congr 1; field_simp
  exact hidx.trans (le_of_mul_le_mul_right hkey hpos)

end GroundTheory.Heights₂.Heights.FiniteCovolume
