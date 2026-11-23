import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.ScaleInt
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.HeisenbergDualBaseVectorFormulaAlt

noncomputable section

open Matrix MeasureTheory
open scoped ENNReal

namespace ReciprocityTheory.ChartRestriction.DS.Xi.RankOneLeviIdentities

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

theorem pt_bound {N a u v p q : ℝ} (ha : 0 < a) (hu : 0 ≤ u) (hv : 0 ≤ v) (hp : 0 ≤ p) (hq : 0 ≤ q)
    (h1 : a ≤ N) (h2 : u ≤ N) (h3 : v ≤ N) :
    N ^ (-(p + q)) ≤ 2 ^ (p + q) * ((a + u) ^ (-p) * (a + v) ^ (-q)) := by
  have hN : 0 < N := lt_of_lt_of_le ha h1
  have hau : 0 < a + u := by linarith
  have hav : 0 < a + v := by linarith
  have hmono : ∀ {x e : ℝ}, 0 < x → x ≤ 2 * N → 0 ≤ e → (2 * N) ^ (-e) ≤ x ^ (-e) := by
    intro x e hx hxN he
    rw [Real.rpow_neg (by linarith), Real.rpow_neg hx.le]
    exact inv_anti₀ (Real.rpow_pos_of_pos hx e) (Real.rpow_le_rpow hx.le hxN he)
  have e1 : (2 * N) ^ (-p) ≤ (a + u) ^ (-p) := hmono hau (by linarith) hp
  have e2 : (2 * N) ^ (-q) ≤ (a + v) ^ (-q) := hmono hav (by linarith) hq
  have key : 2 ^ (p + q) * ((2 * N) ^ (-p) * (2 * N) ^ (-q)) = N ^ (-(p + q)) := by
    rw [← Real.rpow_add (by positivity : (0:ℝ) < 2 * N), Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) hN.le,
      ← mul_assoc, ← Real.rpow_add (by norm_num : (0:ℝ) < 2), show p + q + (-p + -q) = (0:ℝ) by ring,
      Real.rpow_zero, one_mul, neg_add]
  rw [← key]
  exact mul_le_mul_of_nonneg_left (mul_le_mul e1 e2 (by positivity) (by positivity)) (by positivity)

theorem liftVec_cont (k r' : ℕ) : Continuous fun y : Fin (2 * r' + k + 1) → ℂ => liftVec k 1 r' y := by
  apply continuous_pi
  intro p
  simp only [liftVec]
  split_ifs
  · exact continuous_apply _
  · exact continuous_const

def heisM (k r' : ℕ) : HPar k r' → Mt k (1 + r') := fun x => heis0 k r' x

theorem heisenberg_map_continuous (k r' : ℕ) : Continuous (heisM k r') := by
  have hl := liftVec_cont k r'
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  simp only [heisM, heis0, heisG, hb, herm, Matrix.add_apply, Matrix.sub_apply, Matrix.vecMulVec_apply,
    Pi.add_apply, Pi.smul_apply, smul_eq_mul, dotProduct, Matrix.mulVec, Pi.star_apply]
  fun_prop

theorem heisenberg_at_zero (k r' : ℕ) : heis0 k r' (0, 0) = 1 := by
  have hz : liftVec k 1 r' 0 = 0 := by
    funext p
    simp only [liftVec, Pi.zero_apply]
    split_ifs <;> rfl
  ext i j
  simp [heis0, heisG, hb, herm, hz, Matrix.vecMulVec]

theorem ιLev_inv_mul (hCL : HeisConjLev) (k r' : ℕ) (g : Mat k r') (hg : g ∈ GV k r') :
    (ιLev k 1 r' g)⁻¹ * ιLev k 1 r' g = 1 := by
  have h := hCL k r' g hg (0, 0)
  simp only [heisenberg_at_zero, mul_one, Matrix.mulVec_zero] at h
  first
  | exact Matrix.nonsing_inv_mul _ (Matrix.isUnit_det_of_right_inverse h)
  | exact mul_eq_one_comm.mp h
  | exact (Matrix.mul_eq_one_comm).1 h

theorem gN_cont (k n : ℕ) : Continuous fun M : Mat k n => gN M := by
  simp only [gN]
  exact Real.continuous_sqrt.comp (continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ =>
    Complex.continuous_normSq.comp ((continuous_apply j).comp (continuous_apply i)))

theorem int_conj (hCL : HeisConjLev) (hCM : HeisConjLevMeas) (k r' : ℕ) (A : ℝ) (c : ℂ) (g : Mat k r')
    (hg : g ∈ GV k r') :
    ∫⁻ x : HPar k r', ENNReal.ofReal (gN (w0 k r' c * ιLev k 1 r' g * heis0 k r' x) ^ (-A)) =
      ∫⁻ x : HPar k r', ENNReal.ofReal (gN (w0 k r' c * heis0 k r' x * ιLev k 1 r' g) ^ (-A)) := by
  have hinv : (ιLev k 1 r' g)⁻¹ * ιLev k 1 r' g = 1 := ιLev_inv_mul hCL k r' g hg
  have hgN := gN_cont k (1 + r')
  have hcm : Continuous fun M : Mt k (1 + r') => w0 k r' c * Matrix.of M * ιLev k 1 r' g :=
    (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
  have hH : Measurable fun M : Mt k (1 + r') =>
      ENNReal.ofReal (gN (w0 k r' c * Matrix.of M * ιLev k 1 r' g) ^ (-A)) :=
    ((hgN.comp hcm).measurable.pow_const _).ennreal_ofReal
  have hcc : Continuous (conjM (ιLev k 1 r' g) : Mt k (1 + r') → Mt k (1 + r')) :=
    (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
  have hconj : Measurable (conjM (ιLev k 1 r' g) : Mt k (1 + r') → Mt k (1 + r')) := hcc.measurable
  have hheis : Measurable (heisM k r') := (heisenberg_map_continuous k r').measurable
  have hL : ∀ x : HPar k r', ENNReal.ofReal (gN (w0 k r' c * ιLev k 1 r' g * heis0 k r' x) ^ (-A)) =
      (fun M : Mt k (1 + r') => ENNReal.ofReal (gN (w0 k r' c * Matrix.of M * ιLev k 1 r' g) ^ (-A)))
        (conjM (ιLev k 1 r' g) (heis0 k r' x)) := by
    intro x
    have e : w0 k r' c * Matrix.of (conjM (ιLev k 1 r' g) (heis0 k r' x)) * ιLev k 1 r' g =
        w0 k r' c * ιLev k 1 r' g * heis0 k r' x := by
      change w0 k r' c * (ιLev k 1 r' g * heis0 k r' x * (ιLev k 1 r' g)⁻¹) * ιLev k 1 r' g =
        w0 k r' c * ιLev k 1 r' g * heis0 k r' x
      simp only [mul_assoc, hinv, mul_one]
    simp only [e]
  calc ∫⁻ x : HPar k r', ENNReal.ofReal (gN (w0 k r' c * ιLev k 1 r' g * heis0 k r' x) ^ (-A))
      = ∫⁻ x : HPar k r', (fun M : Mt k (1 + r') =>
          ENNReal.ofReal (gN (w0 k r' c * Matrix.of M * ιLev k 1 r' g) ^ (-A)))
            (conjM (ιLev k 1 r' g) (heis0 k r' x)) := lintegral_congr fun x => hL x
    _ = ∫⁻ M, (fun M : Mt k (1 + r') =>
          ENNReal.ofReal (gN (w0 k r' c * Matrix.of M * ιLev k 1 r' g) ^ (-A)))
            (conjM (ιLev k 1 r' g) M) ∂(μHeis k r') := (lintegral_map (hH.comp hconj) hheis).symm
    _ = ∫⁻ M, ENNReal.ofReal (gN (w0 k r' c * Matrix.of M * ιLev k 1 r' g) ^ (-A))
          ∂((μHeis k r').map (conjM (ιLev k 1 r' g))) := (lintegral_map hH hconj).symm
    _ = ∫⁻ M, ENNReal.ofReal (gN (w0 k r' c * Matrix.of M * ιLev k 1 r' g) ^ (-A)) ∂(μHeis k r') := by
          rw [hCM k r' g hg]
    _ = ∫⁻ x : HPar k r', ENNReal.ofReal (gN (w0 k r' c * Matrix.of (heis0 k r' x : Mt k (1 + r')) * ιLev k 1 r' g) ^ (-A)) :=
          lintegral_map hH hheis
    _ = _ := rfl

theorem int_prod (k r' : ℕ) {A p q K₁ K₂ e₁ e₂ : ℝ} (hK₁0 : 0 ≤ K₁) (hK₂0 : 0 ≤ K₂)
    (hK₁ : ∀ a b : ℝ, 0 < a → 0 < b → ∫⁻ y : Fin (2 * r' + k + 1) → ℂ, ENNReal.ofReal ((a + b * ‖y‖) ^ (-p)) ≤
      ENNReal.ofReal (K₁ * a ^ (-p) * (a / b) ^ e₁))
    (hK₂ : ∀ a b : ℝ, 0 < a → 0 < b → ∫⁻ s : ℝ, ENNReal.ofReal ((a + b * ‖s‖) ^ (-q)) ≤
      ENNReal.ofReal (K₂ * a ^ (-q) * (a / b) ^ e₂))
    (F : HPar k r' → ℝ≥0∞) {a b₁ b₂ : ℝ} (ha : 0 < a) (hb₁ : 0 < b₁) (hb₂ : 0 < b₂)
    (hF : ∀ x : HPar k r', F x ≤
      ENNReal.ofReal (2 ^ A * ((a + b₁ * ‖x.1‖) ^ (-p) * (a + b₂ * ‖x.2‖) ^ (-q)))) :
    ∫⁻ x, F x ≤ ENNReal.ofReal (2 ^ A * (K₁ * a ^ (-p) * (a / b₁) ^ e₁) * (K₂ * a ^ (-q) * (a / b₂) ^ e₂)) := by
  have hf₁ : Measurable fun y : Fin (2 * r' + k + 1) → ℂ => ENNReal.ofReal ((a + b₁ * ‖y‖) ^ (-p)) :=
    ((measurable_const.add (measurable_const.mul measurable_norm)).pow_const _).ennreal_ofReal
  have hf₂ : Measurable fun s : ℝ => ENNReal.ofReal ((a + b₂ * ‖s‖) ^ (-q)) :=
    ((measurable_const.add (measurable_const.mul measurable_norm)).pow_const _).ennreal_ofReal
  have hX : 0 ≤ K₁ * a ^ (-p) * (a / b₁) ^ e₁ :=
    mul_nonneg (mul_nonneg hK₁0 (Real.rpow_nonneg ha.le _)) (Real.rpow_nonneg (div_pos ha hb₁).le _)
  have h2A : (0 : ℝ) ≤ 2 ^ A := by positivity
  calc ∫⁻ x, F x ≤ ∫⁻ x : HPar k r', ENNReal.ofReal (2 ^ A) *
        (ENNReal.ofReal ((a + b₁ * ‖x.1‖) ^ (-p)) * ENNReal.ofReal ((a + b₂ * ‖x.2‖) ^ (-q))) := by
        refine lintegral_mono fun x => (hF x).trans (le_of_eq ?_)
        rw [ENNReal.ofReal_mul h2A, ENNReal.ofReal_mul (Real.rpow_nonneg
          (add_nonneg ha.le (mul_nonneg hb₁.le (norm_nonneg _))) _)]
    _ = ENNReal.ofReal (2 ^ A) * ((∫⁻ y : Fin (2 * r' + k + 1) → ℂ, ENNReal.ofReal ((a + b₁ * ‖y‖) ^ (-p))) *
          ∫⁻ s : ℝ, ENNReal.ofReal ((a + b₂ * ‖s‖) ^ (-q))) := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        congr 1
        exact lintegral_prod_mul (μ := (volume : Measure (Fin (2 * r' + k + 1) → ℂ)))
          (ν := (volume : Measure ℝ)) hf₁.aemeasurable hf₂.aemeasurable
    _ ≤ ENNReal.ofReal (2 ^ A) * (ENNReal.ofReal (K₁ * a ^ (-p) * (a / b₁) ^ e₁) *
          ENNReal.ofReal (K₂ * a ^ (-q) * (a / b₂) ^ e₂)) := by
        gcongr
        · exact hK₁ a b₁ ha hb₁
        · exact hK₂ a b₂ ha hb₂
    _ = _ := by
        rw [← ENNReal.ofReal_mul hX, ← ENNReal.ofReal_mul h2A]
        congr 1
        ring

theorem eInt_bound' (hGL : GNLower) (hHA : HeisAct) (hCL : HeisConjLev) (hCM : HeisConjLevMeas)
    (k r' : ℕ) (A : ℝ) (hA : ((4 * r' + 2 * k + 3 : ℕ) : ℝ) < A) :
    ∃ C : ℝ, ∀ c : ℂ, c ≠ 0 → ∀ g ∈ GV k r',
      ∫⁻ x : HPar k r', ENNReal.ofReal (gN (w0 k r' c * ιLev k 1 r' g * heis0 k r' x) ^ (-A)) ≤
        ENNReal.ofReal (C * min (‖c‖ ^ (-((4 * r' + 2 * k + 3 : ℕ) : ℝ))) ‖c‖⁻¹ *
          gN g ^ (((4 * r' + 2 * k + 3 : ℕ) : ℝ) - A)) := by
  obtain ⟨d, hd⟩ : ∃ d : ℝ, d = ((4 * r' + 2 * k + 3 : ℕ) : ℝ) := ⟨_, rfl⟩
  rw [← hd] at hA ⊢
  have hd3 : (3 : ℝ) ≤ d := by rw [hd]; norm_cast; omega
  have hE : (Module.finrank ℝ (Fin (2 * r' + k + 1) → ℂ) : ℝ) = d - 1 := by
    rw [Module.finrank_pi_fintype]
    simp only [Complex.finrank_real_complex, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      smul_eq_mul]
    rw [hd]; push_cast; ring
  obtain ⟨p, hp⟩ : ∃ p : ℝ, p = d - 1 + (A - d) / 2 := ⟨_, rfl⟩
  obtain ⟨q, hq⟩ : ∃ q : ℝ, q = 1 + (A - d) / 2 := ⟨_, rfl⟩
  have hpq : p + q = A := by rw [hp, hq]; ring
  have hp0 : 0 ≤ p := by rw [hp]; linarith
  have hq0 : 0 ≤ q := by rw [hq]; linarith
  obtain ⟨K₁, hK₁0, hK₁⟩ := scale_int (volume : Measure (Fin (2 * r' + k + 1) → ℂ)) (r := p)
    (by rw [hE, hp]; linarith)
  obtain ⟨K₂, hK₂0, hK₂⟩ := scale_int (volume : Measure ℝ) (r := q)
    (by simp only [Module.finrank_self, Nat.cast_one]; rw [hq]; linarith)
  rw [hE] at hK₁
  simp only [Module.finrank_self, Nat.cast_one] at hK₂
  refine ⟨2 ^ A * K₁ * K₂, fun c hc g hg => ?_⟩
  have ha : 0 < gN g := lt_of_lt_of_le zero_lt_one (hGL k r' g hg)
  have hc0 : 0 < ‖c‖ := norm_pos_iff.2 hc
  have B1 := int_prod k r' hK₁0 hK₂0 hK₁ hK₂
    (fun x => ENNReal.ofReal (gN (w0 k r' c * ιLev k 1 r' g * heis0 k r' x) ^ (-A))) ha hc0 hc0
    (fun x => by
      obtain ⟨h1, h2, h3⟩ := pt_un k r' c g x hHA
      rw [← Real.norm_eq_abs] at h3
      have := pt_bound ha (mul_nonneg hc0.le (norm_nonneg _)) (mul_nonneg hc0.le (norm_nonneg _))
        hp0 hq0 h1 h2 h3
      rw [hpq] at this
      exact ENNReal.ofReal_le_ofReal this)
  have B2 := int_prod k r' hK₁0 hK₂0 hK₁ hK₂
    (fun x => ENNReal.ofReal (gN (w0 k r' c * heis0 k r' x * ιLev k 1 r' g) ^ (-A))) ha one_pos hc0
    (fun x => by
      obtain ⟨h1, h2, h3⟩ := pt_conj k r' c g x hHA
      rw [← Real.norm_eq_abs] at h3
      rw [← one_mul ‖x.1‖] at h2
      have := pt_bound ha (by positivity) (mul_nonneg hc0.le (norm_nonneg _)) hp0 hq0 h1 h2 h3
      rw [hpq] at this
      exact ENNReal.ofReal_le_ofReal this)
  rw [← int_conj hCL hCM k r' A c g hg] at B2
  have ea : gN g ^ (d - A) = gN g ^ (-p) * gN g ^ (d - 1) * gN g ^ (-q) * gN g ^ (1 : ℝ) := by
    rw [← Real.rpow_add ha, ← Real.rpow_add ha, ← Real.rpow_add ha]
    congr 1
    linarith
  have E1 : 2 ^ A * (K₁ * gN g ^ (-p) * (gN g / ‖c‖) ^ (d - 1)) * (K₂ * gN g ^ (-q) * (gN g / ‖c‖) ^ (1 : ℝ)) =
      2 ^ A * K₁ * K₂ * ‖c‖ ^ (-d) * gN g ^ (d - A) := by
    have ec : ‖c‖ ^ (-d) = ‖c‖ ^ (-(d - 1)) * ‖c‖ ^ (-(1 : ℝ)) := by
      rw [← Real.rpow_add hc0]; congr 1; ring
    rw [Real.div_rpow ha.le hc0.le, Real.div_rpow ha.le hc0.le, ea, ec, Real.rpow_neg hc0.le,
      Real.rpow_neg hc0.le]
    ring
  have E2 : 2 ^ A * (K₁ * gN g ^ (-p) * (gN g / 1) ^ (d - 1)) * (K₂ * gN g ^ (-q) * (gN g / ‖c‖) ^ (1 : ℝ)) =
      2 ^ A * K₁ * K₂ * ‖c‖⁻¹ * gN g ^ (d - A) := by
    rw [div_one, Real.div_rpow ha.le hc0.le, ea, Real.rpow_one, Real.rpow_one]
    ring
  rcases le_total (‖c‖ ^ (-d)) ‖c‖⁻¹ with h | h
  · rw [min_eq_left h, ← E1]; exact B1
  · rw [min_eq_right h, ← E2]; exact B2

end ReciprocityTheory.ChartRestriction.DS.Xi.RankOneLeviIdentities
