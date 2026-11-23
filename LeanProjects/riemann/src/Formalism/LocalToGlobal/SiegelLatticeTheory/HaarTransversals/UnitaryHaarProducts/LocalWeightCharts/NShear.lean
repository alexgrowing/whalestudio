import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LocalWeightCharts.NilpotentChartRightInverse
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LowerShearHaar.MeasurePreservingOfCard

open Matrix Formalism.QuantumDeterminants MeasureTheory

noncomputable section

namespace WlocSk.NB

variable {k r : ℕ}

def rk : CI k r → ℕ
  | Sum.inl p => r - p.1.1.val
  | Sum.inr (Sum.inl q) => r - q.1.val
  | Sum.inr (Sum.inr _) => r + 1

def dlt (m₀ : Mx k r) (x : CI k r → ℂ) : Matrix (Fin r) (Fin r) ℂ :=
  (cF x)ᴴ * ((bF m₀)ᴴ * (bB m₀ * cE x + bC m₀ * cF x))

def shG (m₀ : Mx k r) (x : CI k r → ℂ) : CI k r → ℂ
  | Sum.inl p => ∑ c, if p.1.1 < c then bA m₀ p.1.1 c * cA x c p.1.2 else 0
  | Sum.inr (Sum.inl q) => (∑ c, if q.1 < c then bA m₀ q.1 c * cB x c q.2 else 0) + bB m₀ q.1 q.2
  | Sum.inr (Sum.inr p) => (dlt m₀ x p.1.1 p.1.2 - star (dlt m₀ x p.1.2 p.1.1)) / 2

def shH (m₀ : Mx k r) (x : CI k r → ℂ) : Fin r → ℝ := fun a => (dlt m₀ x a a).im

theorem split_low {A : Matrix (Fin r) (Fin r) ℂ} (hA : LowId A) (v : Fin r → ℂ) (a : Fin r) :
    ∑ c, A a c * v c = v a + ∑ c, if a < c then A a c * v c else 0 := by
  have : ∀ c, A a c * v c = (if a = c then v c else 0) + (if a < c then A a c * v c else 0) := by
    intro c
    rcases lt_trichotomy a c with h | rfl | h
    · rw [if_neg (ne_of_lt h), if_pos h, zero_add]
    · rw [if_pos rfl, if_neg (lt_irrefl a), add_zero, hA a a le_rfl, if_pos rfl, one_mul]
    · rw [if_neg (ne_of_gt h), if_neg (not_lt.2 h.le), add_zero, hA a c h.le, if_neg (ne_of_gt h),
        zero_mul]
  rw [Finset.sum_congr rfl fun c _ => this c, Finset.sum_add_distrib, Finset.sum_ite_eq,
    if_pos (Finset.mem_univ _)]

theorem lowId_bA {g : Mx k r} (hc : ColB g) : LowId (bA g) := fun a b h => hc.aa a b h

theorem mof_mul {m₀ g : Mx k r} (h0 : m₀ ∈ Nset k r) (hg : g ∈ Nset k r) :
    mof (m₀ * g) = mof g + (bF g)ᴴ * ((bF m₀)ᴴ * (bB m₀ * bE g + bC m₀ * bF g)) := by
  have hc0 := colB_of_mem h0
  have hF0 := rel_F hc0 h0.1
  rw [mof, mof, bF_mul hc0, bC_mul, conjTranspose_mul]
  rw [add_assoc, Matrix.mul_add, Matrix.mul_add, Matrix.mul_add]
  have : (bF g)ᴴ * (bF m₀)ᴴ * (bA m₀ * bC g) = (bF g)ᴴ * bC g := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc (bF m₀)ᴴ, hF0, Matrix.one_mul]
  rw [this]
  simp only [Matrix.mul_assoc, Matrix.mul_add]

theorem lmul_coord {m₀ : Mx k r} (h0 : m₀ ∈ Nset k r) (x : CI k r → ℂ) (s : Fin r → ℝ) :
    psiC (m₀ * phi0 x s) = x + shG m₀ x ∧ psiR (m₀ * phi0 x s) = s + shH m₀ x := by
  have hg := test_vector_mem_schwartz_bruhat x s
  have hcg := colB_of_mem hg
  have hc0 := colB_of_mem h0
  have hps := nilpotent_chart_right_inverse x s
  have hM : mof (m₀ * phi0 x s) = mof (phi0 x s) + dlt m₀ x := by
    rw [mof_mul h0 hg, dlt, phi0, bF_mk, bE_mk]
  constructor
  · funext i
    rcases i with ⟨⟨a, b⟩, h⟩ | ⟨a, j⟩ | ⟨⟨a, b⟩, h⟩
    · show bA (m₀ * phi0 x s) a b = _
      rw [bA_mul hcg, Matrix.mul_apply, phi0, bA_mk, split_low (lowId_bA hc0)]
      simp only [Pi.add_apply, shG, cA, dif_pos h]
    · show bB (m₀ * phi0 x s) a j = _
      rw [bB_mul hcg, Matrix.add_apply, Matrix.mul_apply, phi0, bB_mk, split_low (lowId_bA hc0)]
      simp only [Pi.add_apply, shG, cB]
      ring
    · show kof (m₀ * phi0 x s) a b = _
      have e1 : kof (phi0 x s) a b = x (Sum.inr (Sum.inr ⟨(a, b), h⟩)) :=
        congrFun hps.1 (Sum.inr (Sum.inr ⟨(a, b), h⟩))
      simp only [kof, hM, Matrix.add_apply, Pi.add_apply, shG, star_add] at e1 ⊢
      rw [← e1]
      ring
  · funext a
    have e1 : (mof (phi0 x s) a a).im = s a := congrFun hps.2 a
    show (mof (m₀ * phi0 x s) a a).im = _
    rw [hM, Matrix.add_apply, Complex.add_im, e1]
    rfl

theorem shG_dep (m₀ : Mx k r) (i : CI k r) (x y : CI k r → ℂ)
    (hxy : ∀ j, rk j < rk i → x j = y j) : shG m₀ x i = shG m₀ y i := by
  have hAB : (∀ j, rk j ≤ r → x j = y j) → cA x = cA y ∧ cB x = cB y := by
    intro h
    refine ⟨?_, ?_⟩
    · ext a b; unfold cA; split_ifs with h1
      · exact h _ (by simp only [rk]; omega)
      · rfl
      · rfl
    · ext a j; exact h _ (by simp only [rk]; omega)
  rcases i with ⟨⟨a, b⟩, h⟩ | ⟨a, j⟩ | ⟨⟨a, b⟩, h⟩
  · simp only [shG]
    refine Finset.sum_congr rfl fun c _ => ?_
    split_ifs with hac
    · congr 1
      unfold cA
      split_ifs with hcb
      · exact hxy _ (by simp only [rk]; have := c.isLt; have : a.val < c.val := hac; omega)
      · rfl
      · rfl
    · rfl
  · simp only [shG]
    congr 1
    refine Finset.sum_congr rfl fun c _ => ?_
    split_ifs with hac
    · congr 1
      exact hxy _ (by simp only [rk]; have := c.isLt; have : a.val < c.val := hac; omega)
    · rfl
  · obtain ⟨hA, hB⟩ := hAB fun j hj => hxy j (by show rk j < r + 1; omega)
    simp only [shG, dlt, cF, cE, hA, hB]

theorem continuous_dlt (m₀ : Mx k r) : Continuous (dlt m₀) :=
  continuous_cF.matrix_conjTranspose.matrix_mul (continuous_const.matrix_mul
    ((continuous_const.matrix_mul continuous_cE).add (continuous_const.matrix_mul continuous_cF)))

theorem continuous_shG (m₀ : Mx k r) (i : CI k r) : Continuous fun x => shG m₀ x i := by
  rcases i with ⟨⟨a, b⟩, h⟩ | ⟨a, j⟩ | ⟨⟨a, b⟩, h⟩
  · simp only [shG]
    refine continuous_finsetSum _ fun c _ => ?_
    split_ifs
    · exact continuous_const.mul (continuous_cA.matrix_elem _ _)
    · exact continuous_const
  · simp only [shG]
    refine (continuous_finsetSum _ fun c _ => ?_).add continuous_const
    split_ifs
    · exact continuous_const.mul (continuous_cB.matrix_elem _ _)
    · exact continuous_const
  · simp only [shG]
    exact (((continuous_dlt m₀).matrix_elem _ _).sub ((continuous_dlt m₀).matrix_elem _ _).star).div_const _

theorem continuous_shH (m₀ : Mx k r) : Continuous (shH m₀) :=
  continuous_pi fun a => Complex.continuous_im.comp ((continuous_dlt m₀).matrix_elem a a)

theorem shear_mp {ι : Type} [Fintype ι] [DecidableEq ι] {d : ℕ} (rkf : ι → ℕ) (G : (ι → ℂ) → ι → ℂ)
    (H : (ι → ℂ) → Fin d → ℝ) (hG : ∀ i, Measurable fun x => G x i)
    (hdep : ∀ i (x y : ι → ℂ), (∀ j, rkf j < rkf i → x j = y j) → G x i = G y i)
    (hH : Measurable H) :
    MeasurePreserving (fun t : (ι → ℂ) × (Fin d → ℝ) => (t.1 + G t.1, t.2 + H t.1)) volume volume := by
  have h1 : MeasurePreserving (fun x : ι → ℂ => fun i => x i + G x i) volume volume :=
    PI.LowSplitHaarW.triShear ι rkf (fun i x => G x i) hG hdep
  have h2 := h1.skew_product (μc := (volume : Measure (Fin d → ℝ))) (μd := volume)
    (g := fun x s => s + H x) (measurable_snd.add (hH.comp measurable_fst))
    (Filter.Eventually.of_forall fun x => map_add_right_eq_self volume (H x))
  exact h2

end WlocSk.NB
