import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpolationModelInequalities
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.BasePsiLeviLowerBound
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.ArakelovInstances.CurvatureStatementHolds

set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.AR.Up

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Inst.CurvPf ReciprocityTheory.L2DbarEstimates Matrix

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def coefR {r : ℕ} (X : Data E r) (v : X.Ψ → Fin r → ℝ) (τ : X.Ψ) (a j : Fin r) : ℝ :=
  Dsg X j / Dsg X a * (v τ a - v τ j)

theorem coefR_nonneg {r : ℕ} (X : Data E r) (v : X.Ψ → Fin r → ℝ) (hv : IsDominantR X v) (τ : X.Ψ)
    (a j : Fin r) (h : (a : ℕ) < j) : 0 ≤ coefR X v τ a j := by
  obtain ⟨h1, h2, h3⟩ := hv τ
  have hle : a ≤ j := Fin.le_iff_val_le_val.mpr h.le
  have f1 := fun (hj : (j : ℕ) < X.p0) => h1 a j hle hj
  have f2 := fun (ha : X.p0 ≤ (a : ℕ)) => h2 a j ha hle
  have f3 := fun (ha : (a : ℕ) < X.p0) (hj : X.p0 ≤ (j : ℕ)) => h3 a j ha hj
  unfold coefR Dsg sgn
  split_ifs <;> first
    | (exfalso; omega)
    | (norm_num <;> (first | linarith [f1 (by omega)] | linarith [f2 (by omega)] | linarith [f3 (by omega) (by omega)]))

theorem affine_nonneg (α β t t1 : ℝ) (h0 : 0 ≤ α) (h1 : 0 ≤ α + β * t1) (ht : 0 ≤ t) (ht1 : t ≤ t1) :
    0 ≤ α + β * t := by
  rcases le_total 0 β with hb | hb
  · nlinarith [mul_nonneg hb ht]
  · nlinarith [mul_le_mul_of_nonpos_left ht1 hb]

theorem curvNumStatement_holds : CurvNumStatement (E := E) := by
  intro r X L de Fp T rr η hη hrr hT hL hLde hdom
  refine ⟨fun x0 _ z hz ξ hξ => (curvature_statement_holds r X L x0 z hz).2 hL ξ hξ,
    fun x0 _ z hz ξ hξ => (curvature_statement_holds r X (2 • L - de) x0 z hz).2 hLde ξ hξ, ?_⟩
  intro t ht htT x0 _ z hz ξ
  obtain ⟨b, hb, hgr⟩ := MajorantNormalForms.exists_normal_frame X hz
  have hgram : ∀ τ, gram τ.1 X.Gm (mat (rmul (cpt X x0 z) b) τ) =
      diagonal fun a : Fin r => ((sgn X.p0 (a : ℕ) : ℝ) : ℂ) := fun τ => (hgr τ).1
  set v : X.Ψ → Fin r → ℝ := fun τ a =>
    ((Fp - kapW X - nd X • L) τ a : ℝ) - t * (rr / 2) * (de τ a : ℝ) - 2 * η * (L τ a : ℝ) with hv

  have ht1 : t ≤ 2 * T / rr := by rw [le_div_iff₀ hrr]; linarith
  have hv0 := hdom 0 (by simp)
  have hv1 := hdom (2 * T / rr) (by simp)
  have hvt : IsDominantR X v := by
    intro τ
    obtain ⟨a0, b0, c0⟩ := hv0 τ
    obtain ⟨a1, b1, c1⟩ := hv1 τ
    have gen : ∀ i j : Fin r,
        (fun τ a => ((Fp - kapW X - nd X • L) τ a : ℝ) - 0 * (rr / 2) * (de τ a : ℝ) - 2 * η * (L τ a : ℝ)) τ j ≤
          (fun τ a => ((Fp - kapW X - nd X • L) τ a : ℝ) - 0 * (rr / 2) * (de τ a : ℝ) - 2 * η * (L τ a : ℝ)) τ i →
        (fun τ a => ((Fp - kapW X - nd X • L) τ a : ℝ) - 2 * T / rr * (rr / 2) * (de τ a : ℝ) -
          2 * η * (L τ a : ℝ)) τ j ≤
          (fun τ a => ((Fp - kapW X - nd X • L) τ a : ℝ) - 2 * T / rr * (rr / 2) * (de τ a : ℝ) -
            2 * η * (L τ a : ℝ)) τ i → v τ j ≤ v τ i := by
      intro i j e0 e1
      simp only at e0 e1
      simp only [hv]
      have h := affine_nonneg
        ((((Fp - kapW X - nd X • L) τ i : ℝ) - 2 * η * (L τ i : ℝ)) -
          (((Fp - kapW X - nd X • L) τ j : ℝ) - 2 * η * (L τ j : ℝ)))
        (-(rr / 2) * ((de τ i : ℝ) - de τ j)) t (2 * T / rr) (by linarith) (by linarith) ht ht1
      linarith
    exact ⟨fun i j hij hj => gen i j (a0 i j hij hj) (a1 i j hij hj),
      fun i j hi hij => gen i j (b0 i j hi hij) (b1 i j hi hij),
      fun i j hi hj => gen j i (c0 i j hi hj) (c1 i j hi hj)⟩
  unfold leviM phla
  rw [levi_formula X L x0 z hz b hb hgram ξ, levi_formula X (Fp - kapW X - nd X • L) x0 z hz b hb hgram ξ,
    levi_formula X de x0 z hz b hb hgram ξ]
  rw [← sub_nonneg]
  have key : (∑ τ, ∑ a : Fin r, ∑ j : Fin r, if (a : ℕ) < j then
        coef X (Fp - kapW X - nd X • L) τ a j * ‖Yd X b z (WithLp.toLp 2 ξ) τ j a‖ ^ 2 else 0) -
      t * (rr / 2) * (∑ τ, ∑ a : Fin r, ∑ j : Fin r, if (a : ℕ) < j then
        coef X de τ a j * ‖Yd X b z (WithLp.toLp 2 ξ) τ j a‖ ^ 2 else 0) -
      2 * η * (∑ τ, ∑ a : Fin r, ∑ j : Fin r, if (a : ℕ) < j then
        coef X L τ a j * ‖Yd X b z (WithLp.toLp 2 ξ) τ j a‖ ^ 2 else 0) =
      ∑ τ, ∑ a : Fin r, ∑ j : Fin r, if (a : ℕ) < j then
        coefR X v τ a j * ‖Yd X b z (WithLp.toLp 2 ξ) τ j a‖ ^ 2 else 0 := by
    simp only [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun j _ => ?_
    split_ifs
    · unfold coef coefR; simp only [hv]; ring
    · ring
  have hnn : 0 ≤ ∑ τ, ∑ a : Fin r, ∑ j : Fin r, if (a : ℕ) < j then
      coefR X v τ a j * ‖Yd X b z (WithLp.toLp 2 ξ) τ j a‖ ^ 2 else 0 :=
    Finset.sum_nonneg fun τ _ => Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun j _ => by
      split_ifs with h
      · exact mul_nonneg (coefR_nonneg X v hvt τ a j h) (sq_nonneg _)
      · exact le_rfl
  linarith

end ReciprocityTheory.ChartRestriction.G.AR.Up
