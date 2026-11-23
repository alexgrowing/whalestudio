import Formalism.HermitianCurvature.LatticeHerglotzBound

open Finset

noncomputable section

namespace Formalism.FourierDecayAlt.P.BaseGramNonnegativity

open Formalism.FourierDecayAlt.crystallineComparison Formalism.FourierDecayAlt.TB

theorem sum_re_nonneg {α : Type} (Y : Finset α) (κ G : α → α → ℂ) (hκ : PSDOn Y κ) (hG : PSDOn Y G) :
    0 ≤ (∑ h ∈ Y, ∑ h' ∈ Y, κ h h' * G h h').re := by
  have H := (Matrix.PosSemidef.hadamard hκ hG).re_dotProduct_nonneg (fun _ => (1 : ℂ))
  simp only [dotProduct, Matrix.mulVec, Matrix.hadamard_apply, Matrix.of_apply, Pi.star_apply,
    star_one, one_mul, mul_one, RCLike.re_to_complex] at H
  convert H using 2
  rw [← Finset.sum_coe_sort Y]
  refine Finset.sum_congr rfl (fun h _ => ?_)
  rw [← Finset.sum_coe_sort Y]

variable {E W : Type} [Field E] (D : Data E W)

theorem baseGram_sub (ε : ℝ) (k : ℕ) (w : W) (Y : Finset (Pt E)) (κ κ' : Pt E → Pt E → ℂ) :
    D.N0 ε k w Y (fun h h' => κ' h h' - κ h h') = D.N0 ε k w Y κ' - D.N0 ε k w Y κ := by
  simp only [Data.N0, sub_mul, Finset.sum_sub_distrib, Complex.sub_re, sub_div]

theorem baseGram_smul (ε : ℝ) (k : ℕ) (w : W) (Y : Finset (Pt E)) (r : ℝ) (κ : Pt E → Pt E → ℂ) :
    D.N0 ε k w Y (fun h h' => (r : ℂ) * κ h h') = r * D.N0 ε k w Y κ := by
  simp only [Data.N0, mul_assoc, ← Finset.mul_sum, Complex.re_ofReal_mul, mul_div_assoc]

theorem baseGram_sum (ε : ℝ) (k : ℕ) (w : W) (Y : Finset (Pt E)) {ι : Type} (T : Finset ι)
    (κ : ι → Pt E → Pt E → ℂ) :
    D.N0 ε k w Y (fun h h' => ∑ t ∈ T, κ t h h') = ∑ t ∈ T, D.N0 ε k w Y (κ t) := by
  simp only [Data.N0, Finset.sum_mul, ← Finset.sum_div, ← Complex.re_sum]
  congr 2
  calc _ = ∑ h ∈ Y, ∑ t ∈ T, ∑ h' ∈ Y, κ t h h' * D.gram ε k w h h' :=
        Finset.sum_congr rfl (fun h _ => Finset.sum_comm)
    _ = _ := Finset.sum_comm

theorem baseGram_nonneg (hG : D.GramPSD) (hW : D.WordsPos) {ε : ℝ} (hε : 0 < ε) (k : ℕ) (w : W)
    (Y : Finset (Pt E)) (κ : Pt E → Pt E → ℂ) (hκ : PSDOn Y κ) : 0 ≤ D.N0 ε k w Y κ :=
  div_nonneg (sum_re_nonneg Y κ _ hκ (hG ε hε k w Y)) (hW w).le

theorem baseGramMonotone' : BaseGramMonotone := by
  intro E W _ D hG hW ε hε k w Y κ κ' hκ hκκ'
  refine ⟨baseGram_nonneg D hG hW hε k w Y κ hκ, ?_⟩
  have := baseGram_nonneg D hG hW hε k w Y _ hκκ'
  rw [baseGram_sub] at this
  linarith

theorem corT_ok : CorT := by
  intro E W _ D hG hW ε hε k Y T0 Th KK e Ws θ Mv Bmax Lhs he hMv hθ hTh hsum hL hB
  have key : ∀ w', ∑ t₀ ∈ T0, D.N0 ε k w' Y (Th t₀) ≤ (1 + e) * D.N0 ε k w' Y KK := by
    intro w'
    have h := baseGram_nonneg D hG hW hε k w' Y _ hsum
    have h2 := baseGram_sub D ε k w' Y (fun h h' => ∑ t₀ ∈ T0, Th t₀ h h')
      (fun h h' => ((1 + e : ℝ) : ℂ) * KK h h')
    have h3 : (fun h h' => (1 + (e : ℂ)) * KK h h' - ∑ t₀ ∈ T0, Th t₀ h h') =
        (fun h h' => ((1 + e : ℝ) : ℂ) * KK h h' - ∑ t₀ ∈ T0, Th t₀ h h') := by
      push_cast; rfl
    rw [h3, h2, baseGram_smul, baseGram_sum] at h
    linarith
  have hθ0 := hθ.1
  constructor
  · calc ∑ t₀ ∈ T0, Lhs t₀ ≤ ∑ t₀ ∈ T0, Mv * ∑ w' ∈ Ws, θ w' * D.N0 ε k w' Y (Th t₀) :=
          Finset.sum_le_sum hL
      _ = Mv * ∑ w' ∈ Ws, θ w' * ∑ t₀ ∈ T0, D.N0 ε k w' Y (Th t₀) := by
          rw [← Finset.mul_sum]; congr 1
          rw [Finset.sum_comm]; simp only [Finset.mul_sum]
      _ ≤ Mv * ∑ w' ∈ Ws, θ w' * ((1 + e) * D.N0 ε k w' Y KK) := by
          apply mul_le_mul_of_nonneg_left _ hMv
          exact Finset.sum_le_sum (fun w' _ => mul_le_mul_of_nonneg_left (key w') (hθ0 w'))
      _ = (1 + e) * Mv * ∑ w' ∈ Ws, θ w' * D.N0 ε k w' Y KK := by
          simp only [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun _ _ => by ring)
  · apply mul_le_mul_of_nonneg_left _ (mul_nonneg (by linarith) hMv)
    calc ∑ w' ∈ Ws, θ w' * D.N0 ε k w' Y KK ≤ ∑ w' ∈ Ws, θ w' * Bmax :=
          Finset.sum_le_sum (fun w' hw' => mul_le_mul_of_nonneg_left (hB w' hw') (hθ0 w'))
      _ = Bmax := by rw [← Finset.sum_mul, hθ.2.2, one_mul]

theorem Wb_mono {n m : ℕ} (h : n ≤ m) : D.Wb n ⊆ D.Wb m := by
  intro x hx
  simp only [Data.Wb, Finset.mem_filter] at hx ⊢
  exact ⟨hx.1, hx.2.trans h⟩

theorem estBlockOfSumForm_ok : EstBlockOfSumForm := by
  intro E W _ D C₄ hG hW hSF ε hε i s hs hsi hir w hw hcnt hvol
  obtain ⟨Mv, hMv, θ, hθ, hb⟩ := hSF ε hε i s hs hsi hir w hw hcnt hvol
  have hsub : D.Wb (D.cnt w + s * D.K) ⊆ D.Wb (D.cnt w + (s + 1) * D.K) :=
    Wb_mono D (by nlinarith)
  have hext : ∀ g : W → ℝ, ∑ w' ∈ D.Wb (D.cnt w + (s + 1) * D.K), θ w' * g w' =
      ∑ w' ∈ D.Wb (D.cnt w + s * D.K), θ w' * g w' := by
    intro g
    symm
    refine Finset.sum_subset hsub (fun x _ hx => ?_)
    rw [hθ.2.1 x hx, zero_mul]
  refine ⟨θ, ⟨hθ.1, fun a ha => hθ.2.1 a (fun h => ha (hsub h)), ?_⟩, ?_⟩
  · have := hext (fun _ => 1)
    simp only [mul_one] at this
    rw [this, hθ.2.2]
  · intro Y hY κ hκ t₀ S hS
    have h := hb Y hY κ hκ t₀ S hS
    rw [hext]
    have hX : 0 ≤ ∑ w' ∈ D.Wb (D.cnt w + s * D.K), θ w' * D.N0 ε (i - s) w' Y κ :=
      Finset.sum_nonneg (fun w' _ => mul_nonneg (hθ.1 w') (baseGram_nonneg D hG hW hε _ _ Y κ hκ))
    exact h.trans (mul_le_mul_of_nonneg_right hMv hX)

end Formalism.FourierDecayAlt.P.BaseGramNonnegativity

theorem Formalism.FourierDecayAlt.P.baseGramMonotone : Formalism.FourierDecayAlt.crystallineComparison.BaseGramMonotone := Formalism.FourierDecayAlt.P.BaseGramNonnegativity.baseGramMonotone'
theorem Formalism.FourierDecayAlt.P.cosetSumBound : Formalism.FourierDecayAlt.crystallineComparison.CorT := Formalism.FourierDecayAlt.P.BaseGramNonnegativity.corT_ok
theorem Formalism.FourierDecayAlt.P.blockEstimateOfCosetSum : Formalism.FourierDecayAlt.crystallineComparison.EstBlockOfSumForm :=
  Formalism.FourierDecayAlt.P.BaseGramNonnegativity.estBlockOfSumForm_ok
