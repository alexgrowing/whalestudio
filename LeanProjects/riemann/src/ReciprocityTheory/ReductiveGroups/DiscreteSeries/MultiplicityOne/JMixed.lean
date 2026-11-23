import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JMixedA
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JSchurG

noncomputable section

open Matrix MeasureTheory
open scoped ENNReal ComplexConjugate InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.Mult1

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 ConjugateNormInequalities MixedNormBounds

theorem stMixed (h : UnitaryGroupStructuralFacts) : StMixed := by
  obtain ⟨hB2, -, -, -, hUWb, -⟩ := h
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, hInt, hLow, -, -, -, hCG, -⟩ := hB2
  intro k r Wp _ _ _ D X hD hSq γ hγ haM C hC u hu
  have hG := hCG k r
  have hEG : embWb k r γ ∈ GV k r := by
    have hmem : embWb k r γ ∈ UWb k r := by rw [(hUWb k r).1]; exact ⟨γ, hγ.1, rfl⟩
    exact hmem.1
  have hE := hG.unit _ hEG
  obtain ⟨d, hd⟩ := stSchurG k r Wp D X hD hSq
  obtain ⟨C₁, hC₁⟩ := hu
  have hn1 : (1 : ℝ) ≤ nR k r := by simp only [nR]; exact_mod_cast Nat.succ_le_succ (Nat.zero_le _)
  have ha0 : 0 ≤ X.a := le_trans (by simp only [aM]; positivity) haM
  set b := AG k r + 1 with hb
  have hb0 : 0 ≤ b := by simp only [hb, AG]; positivity
  have hab : b ≤ X.a := by
    refine le_trans ?_ haM
    simp only [hb, AG, aM]
    nlinarith [mul_le_mul hn1 hn1 zero_le_one (by linarith), sq_nonneg (nR k r)]
  have hCw : C X.w ≠ 0 := by
    intro h0
    have h1 := C.norm_map X.w
    rw [h0, norm_zero, X.w_norm] at h1
    exact zero_ne_one h1
  obtain ⟨g₂, hg₂, hc₀⟩ := exists_inner_ne X hG (C X.w) hCw
  have hg2i : g₂⁻¹ ∈ GV k r := hG.inv_mem _ hg₂

  set K : ℝ := (gN (embWb k r γ) * gN (embWb k r γ)⁻¹) ^ 2 with hK
  have hK0 : 0 < K := by
    have h1 := hLow k r _ hEG
    have h2 := hLow k r _ (hG.inv_mem _ hEG)
    have : 1 ≤ gN (embWb k r γ) * gN (embWb k r γ)⁻¹ := by nlinarith
    simp only [hK]; positivity
  set c : ℝ := max (gN (Hpk k r) ^ 2) 1 with hc
  have hc0 : 0 < c := lt_of_lt_of_le one_pos (le_max_right _ _)
  set Lc : ℝ := c * gN g₂⁻¹ with hLc
  have hL0 : 0 < Lc := mul_pos hc0 (by linarith [hLow k r _ hg2i])
  set K₁ : ℝ := max C₁ 0 * K ^ X.a with hK₁
  set K₂ : ℝ := max X.Cw 0 * Lc ^ X.a with hK₂
  have hK₁0 : 0 ≤ K₁ := mul_nonneg (le_max_right _ _) (Real.rpow_nonneg hK0.le _)
  have hK₂0 : 0 ≤ K₂ := mul_nonneg (le_max_right _ _) (Real.rpow_nonneg hL0.le _)

  have f1 : ∀ y ∈ GV k r, ‖⟪C X.w, X.σ y (C u)⟫_ℂ‖ ≤ K₁ * gN y ^ (-X.a) := by
    intro y hy
    have hgb := InvGrp.gbar_mem_GV hG hEG y hy
    have e : ⟪C X.w, X.σ y (C u)⟫_ℂ = ⟪X.σ (gbar k r γ y) u, X.w⟫_ℂ := by
      rw [← hC y hy X.w u, inner_sig_left X hG hgb]
      rfl
    rw [e, norm_inner_symm]
    have hb1 : ‖⟪X.w, X.σ (gbar k r γ y) u⟫_ℂ‖ ≤ C₁ * gN (gbar k r γ y) ^ (-X.a) := hC₁ _ hgb
    have hy1 := hLow k r y hy
    have hrb := rpow_bound (by linarith) hK0 ha0 (gN_le_gbar hE y)
    calc ‖⟪X.w, X.σ (gbar k r γ y) u⟫_ℂ‖ ≤ C₁ * gN (gbar k r γ y) ^ (-X.a) := hb1
      _ ≤ max C₁ 0 * gN (gbar k r γ y) ^ (-X.a) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg (gN_nonneg _) _)
      _ ≤ max C₁ 0 * (K ^ X.a * gN y ^ (-X.a)) := mul_le_mul_of_nonneg_left hrb (le_max_right _ _)
      _ = K₁ * gN y ^ (-X.a) := by rw [hK₁]; ring
  have f2 : ∀ g ∈ GV k r, ‖⟪X.σ g₂ X.w, X.σ g X.w⟫_ℂ‖ ≤ K₂ * gN g ^ (-X.a) := by
    intro g hg
    have hm := hG.mul_mem _ hg2i _ hg
    have e : ⟪X.σ g₂ X.w, X.σ g X.w⟫_ℂ = ⟪X.w, X.σ (g₂⁻¹ * g) X.w⟫_ℂ := by
      rw [inner_sig_left X hG hg₂, X.rep.1.2 _ hg2i _ hg]
      rfl
    rw [e]
    have hb1 := X.dec _ hm
    have hle : gN g ≤ Lc * gN (g₂⁻¹ * g) := by
      calc gN g ≤ gN (Hpk k r) ^ 2 * (gN g₂⁻¹ * gN (g₂⁻¹ * g)) := gN_le_mul hg2i g
        _ ≤ c * (gN g₂⁻¹ * gN (g₂⁻¹ * g)) :=
            mul_le_mul_of_nonneg_right (le_max_left _ _) (mul_nonneg (gN_nonneg _) (gN_nonneg _))
        _ = Lc * gN (g₂⁻¹ * g) := by rw [hLc]; ring
    have hrb := rpow_bound (by linarith [hLow k r g hg]) hL0 ha0 hle
    calc ‖⟪X.w, X.σ (g₂⁻¹ * g) X.w⟫_ℂ‖ ≤ X.Cw * gN (g₂⁻¹ * g) ^ (-X.a) := hb1
      _ ≤ max X.Cw 0 * gN (g₂⁻¹ * g) ^ (-X.a) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg (gN_nonneg _) _)
      _ ≤ max X.Cw 0 * (Lc ^ X.a * gN g ^ (-X.a)) := mul_le_mul_of_nonneg_left hrb (le_max_right _ _)
      _ = K₂ * gN g ^ (-X.a) := by rw [hK₂]; ring

  set c₀ : ℂ := ⟪C X.w, X.σ g₂ X.w⟫_ℂ with hc₀def
  set I : ℝ≥0∞ := ∫⁻ g : Mt k r, ENNReal.ofReal (gN (Matrix.of g) ^ (-b)) ∂D.μG with hI
  have hIfin : I < ∞ := hInt k r D.μG b D.haarG (AB_le_AG k r)
  refine ⟨d / ‖c₀‖ * (K₁ * K₂ * c⁻¹ ^ (-(X.a - b)) * I.toReal), fun x hx => ?_⟩
  have hexp : -(X.a - AG k r - 1) = -(X.a - b) := by rw [hb]; ring
  rw [hexp]
  have hX1 : 1 ≤ gN x := hLow k r x hx
  have hd0 : (d : ℂ) ≠ 0 := by exact_mod_cast hd.1.ne'
  obtain ⟨-, hEq⟩ := hd.2 (X.σ x (C u)) (C X.w) X.w (X.σ g₂ X.w)
  have hmc : mc X (C u) X.w x = (d : ℂ) / c₀ *
      ∫ g : Mt k r, mc X (X.σ x (C u)) (C X.w) (Matrix.of g) * star (mc X X.w (X.σ g₂ X.w) (Matrix.of g)) ∂D.μG := by
    rw [hEq]
    simp only [mc, ← hc₀def]
    field_simp
  have hae : ∀ᵐ g ∂D.μG, Matrix.of g ∈ GV k r := by
    rw [ae_iff]; exact measure_mono_null (fun g hg => hg) D.haarG.conc
  have hpt : ∀ᵐ g ∂D.μG,
      ENNReal.ofReal ‖mc X (X.σ x (C u)) (C X.w) (Matrix.of g) * star (mc X X.w (X.σ g₂ X.w) (Matrix.of g))‖ ≤
        ENNReal.ofReal (K₁ * K₂ * (gN x * c⁻¹) ^ (-(X.a - b))) * ENNReal.ofReal (gN (Matrix.of g) ^ (-b)) := by
    filter_upwards [hae] with g hg
    rw [← ENNReal.ofReal_mul (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    set G : Mat k r := Matrix.of g
    have hGx : G * x ∈ GV k r := hG.mul_mem _ hg _ hx
    have hA := hLow k r _ hGx
    have hB := hLow k r _ hg
    have e1 : mc X (X.σ x (C u)) (C X.w) G = ⟪C X.w, X.σ (G * x) (C u)⟫_ℂ := by
      unfold mc; rw [X.rep.1.2 G hg x hx]; rfl
    have hXle : gN x ≤ c * (gN G * gN (G * x)) :=
      (gN_le_mul hg x).trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
        (mul_nonneg (gN_nonneg _) (gN_nonneg _)))
    have key := real_key hA hB (by linarith) hc0 hb0 hab hXle
    rw [e1, norm_mul, norm_star]
    calc ‖⟪C X.w, X.σ (G * x) (C u)⟫_ℂ‖ * ‖mc X X.w (X.σ g₂ X.w) G‖
        ≤ (K₁ * gN (G * x) ^ (-X.a)) * (K₂ * gN G ^ (-X.a)) :=
          mul_le_mul (f1 _ hGx) (f2 _ hg) (norm_nonneg _) (mul_nonneg hK₁0 (Real.rpow_nonneg (by linarith) _))
      _ = K₁ * K₂ * (gN (G * x) ^ (-X.a) * gN G ^ (-X.a)) := by ring
      _ ≤ K₁ * K₂ * ((gN x * c⁻¹) ^ (-(X.a - b)) * gN G ^ (-b)) :=
          mul_le_mul_of_nonneg_left key (mul_nonneg hK₁0 hK₂0)
      _ = K₁ * K₂ * (gN x * c⁻¹) ^ (-(X.a - b)) * gN G ^ (-b) := by ring
  have hnorm : ‖∫ g : Mt k r, mc X (X.σ x (C u)) (C X.w) (Matrix.of g) *
      star (mc X X.w (X.σ g₂ X.w) (Matrix.of g)) ∂D.μG‖ ≤
      (ENNReal.ofReal (K₁ * K₂ * (gN x * c⁻¹) ^ (-(X.a - b))) * I).toReal :=
    (norm_integral_le_lintegral_norm _).trans (ENNReal.toReal_mono
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hIfin.ne)
      ((lintegral_mono_ae hpt).trans_eq (lintegral_const_mul' _ _ ENNReal.ofReal_ne_top)))
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)] at hnorm
  have hc₀n : 0 < ‖c₀‖ := norm_pos_iff.2 hc₀
  calc ‖mc X (C u) X.w x‖
      = d / ‖c₀‖ * ‖∫ g : Mt k r, mc X (X.σ x (C u)) (C X.w) (Matrix.of g) *
          star (mc X X.w (X.σ g₂ X.w) (Matrix.of g)) ∂D.μG‖ := by
        rw [hmc, norm_mul, norm_div, Complex.norm_real, Real.norm_of_nonneg hd.1.le]
    _ ≤ d / ‖c₀‖ * (K₁ * K₂ * (gN x * c⁻¹) ^ (-(X.a - b)) * I.toReal) :=
        mul_le_mul_of_nonneg_left hnorm (div_nonneg hd.1.le hc₀n.le)
    _ = d / ‖c₀‖ * (K₁ * K₂ * c⁻¹ ^ (-(X.a - b)) * I.toReal) * gN x ^ (-(X.a - b)) := by
        rw [Real.mul_rpow (gN_nonneg x) (inv_nonneg.2 hc0.le)]; ring

end ReciprocityTheory.ChartRestriction.DS.Mult1
