import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.MultivariableReproducingFormula

noncomputable section

open MeasureTheory Matrix
open scoped ENNReal NNReal ComplexConjugate

namespace UpperTheory.Esk

namespace KappaPackingLemmas

variable {F I Gf : Type} [Field F] [Group Gf]

theorem kap_smul (hb : B1b) (D : Dat F I Gf) (δ : PG F) (a b : D.Xs) (v : I) :
    kap ((δ • a : D.Xs) v) ((δ • b : D.Xs) v) = kap (a v) (b v) := by
  induction δ using QuotientGroup.induction_on with
  | H g =>
    rw [Dat.mk_smulX, Dat.mk_smulX]
    exact hb.2.2.2.1 (D.r v g) (a v) (b v)

theorem near_sixteenth (hb : B1b) (hc : B1c) (D : Dat F I Gf) (γ₁ γ : PG F) (z w : D.Xs)
    (h₁ : Near (1 / 2) (γ₁ • z : D.Xs) w) (h : Near (1 / 2) (γ • z : D.Xs) w) :
    Near (1 / 16) z ((γ₁⁻¹ * γ) • z : D.Xs) := by
  intro v
  have e : kap (z v) (((γ₁⁻¹ * γ) • z : D.Xs) v) = kap ((γ₁ • z : D.Xs) v) ((γ • z : D.Xs) v) := by
    rw [← kap_smul hb D γ₁ z ((γ₁⁻¹ * γ) • z) v, smul_smul, mul_inv_cancel_left]
  rw [e]
  have a1 := h₁ v
  have a2 := h v
  have s := (hc.1 ((γ • z : D.Xs) v) (w v)).2.2
  have t := hc.2.2.1 ((γ₁ • z : D.Xs) v) (w v) ((γ • z : D.Xs) v)
  rw [← s] at t
  nlinarith

end KappaPackingLemmas

end UpperTheory.Esk

open UpperTheory.Esk UpperTheory.Esk.KappaPackingLemmas in
theorem UpperTheory.Esk.pf_Pack : UpperTheory.Esk.B1b → UpperTheory.Esk.B1c → UpperTheory.Esk.E0a → UpperTheory.Esk.Pack := by
  intro hb hc hE F I Gf _ _ _ D hax
  obtain ⟨hcnt, -, -, -, -, -, -, hnear⟩ := hE F I Gf D hax
  obtain ⟨c, hc0, hcz⟩ := hnear (1 / 2) (by norm_num)
  have := hcnt
  refine ⟨c⁻¹, ?_⟩
  intro y ω' h A hh hA hfin
  set S0 : Set (PG F) := {γ : PG F | γ • y.1 = y.1 ∧ Near (1 / 16) y.2 (γ • y.2 : D.Xs)} with hS0
  set N : ℝ≥0∞ := (S0.ncard : ℝ≥0∞) with hN
  let Sg : {γ : PG F // γ • y.1 = ω'} → Set D.Xs := fun γ => {w | Near (1 / 2) (γ.1 • y.2 : D.Xs) w}
  have hSm : ∀ γ, MeasurableSet (Sg γ) := fun γ => (hcz (γ.1 • y.2)).1

  have one : ∀ γ : {γ : PG F // γ • y.1 = ω'}, (c : ℝ≥0∞) * h (γ.1 • y.2) ≤ A * ∫⁻ w, (Sg γ).indicator h w := by
    intro γ
    have hv : (c : ℝ≥0∞) ≤ volume (Sg γ) := (hcz (γ.1 • y.2)).2
    calc (c : ℝ≥0∞) * h (γ.1 • y.2) ≤ h (γ.1 • y.2) * volume (Sg γ) := by
          rw [mul_comm]; gcongr
      _ = ∫⁻ _ in Sg γ, h (γ.1 • y.2) := (setLIntegral_const _ _).symm
      _ ≤ ∫⁻ w in Sg γ, (A : ℝ≥0∞) * h w := setLIntegral_mono' (hSm γ) fun w hw => hA _ _ hw
      _ = A * ∫⁻ w in Sg γ, h w := lintegral_const_mul _ hh
      _ = A * ∫⁻ w, (Sg γ).indicator h w := by rw [lintegral_indicator (hSm γ)]

  have cnt : ∀ w : D.Xs, ∑' γ : {γ : PG F // γ • y.1 = ω'}, (Sg γ).indicator h w ≤ N * h w := by
    intro w
    by_cases hT : ∃ γ₁ : {γ : PG F // γ • y.1 = ω'}, w ∈ Sg γ₁
    · obtain ⟨γ₁, hγ₁⟩ := hT
      let f : {γ : PG F // γ • y.1 = ω'} → PG F := fun γ => γ₁.1⁻¹ * γ.1
      have finj : Function.Injective f := fun a b hab => Subtype.ext (mul_left_cancel hab)
      let g : PG F → ℝ≥0∞ := S0.indicator fun _ => h w
      have le1 : ∀ γ : {γ : PG F // γ • y.1 = ω'}, (Sg γ).indicator h w ≤ g (f γ) := by
        intro γ
        by_cases hw : w ∈ Sg γ
        · rw [Set.indicator_of_mem hw]
          have hmem : f γ ∈ S0 := by
            refine ⟨?_, near_sixteenth hb hc D γ₁.1 γ.1 y.2 w hγ₁ hw⟩
            change (γ₁.1⁻¹ * γ.1) • y.1 = y.1
            rw [mul_smul, γ.2, inv_smul_eq_iff]; exact γ₁.2.symm
          simp [g, Set.indicator_of_mem hmem]
        · rw [Set.indicator_of_notMem hw]; exact bot_le
      calc ∑' γ : {γ : PG F // γ • y.1 = ω'}, (Sg γ).indicator h w ≤ ∑' γ, g (f γ) := ENNReal.tsum_le_tsum le1
        _ ≤ ∑' x, g x := ENNReal.tsum_comp_le_tsum_of_injective finj g
        _ = ∑' x : S0, h w := (tsum_subtype S0 fun _ => h w).symm
        _ = N * h w := by
          have : Fintype S0 := hfin.fintype
          rw [tsum_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hN, ← Nat.card_coe_set_eq,
            Nat.card_eq_fintype_card]
    · simp only [not_exists] at hT
      have : ∀ γ : {γ : PG F // γ • y.1 = ω'}, (Sg γ).indicator h w = 0 := fun γ => Set.indicator_of_notMem (hT γ) _
      simp [this]

  have key : (c : ℝ≥0∞) * ∑' γ : {γ : PG F // γ • y.1 = ω'}, h (γ.1 • y.2) ≤ A * (N * ∫⁻ w, h w) := by
    rw [← ENNReal.tsum_mul_left]
    calc ∑' γ : {γ : PG F // γ • y.1 = ω'}, (c : ℝ≥0∞) * h (γ.1 • y.2)
        ≤ ∑' γ : {γ : PG F // γ • y.1 = ω'}, (A : ℝ≥0∞) * ∫⁻ w, (Sg γ).indicator h w := ENNReal.tsum_le_tsum one
      _ = A * ∑' γ : {γ : PG F // γ • y.1 = ω'}, ∫⁻ w, (Sg γ).indicator h w := ENNReal.tsum_mul_left
      _ = A * ∫⁻ w, ∑' γ : {γ : PG F // γ • y.1 = ω'}, (Sg γ).indicator h w := by
          rw [lintegral_tsum fun γ => (hh.indicator (hSm γ)).aemeasurable]
      _ ≤ A * ∫⁻ w, N * h w := by gcongr with w; exact cnt w
      _ = A * (N * ∫⁻ w, h w) := by rw [lintegral_const_mul _ hh]
  have hc' : (c : ℝ≥0∞) ≠ 0 := by exact_mod_cast hc0.ne'
  calc ∑' γ : {γ : PG F // γ • y.1 = ω'}, h (γ.1 • y.2)
      = (c : ℝ≥0∞)⁻¹ * ((c : ℝ≥0∞) * ∑' γ : {γ : PG F // γ • y.1 = ω'}, h (γ.1 • y.2)) := by
        rw [ENNReal.inv_mul_cancel_left hc' ENNReal.coe_ne_top]
    _ ≤ (c : ℝ≥0∞)⁻¹ * (A * (N * ∫⁻ w, h w)) := by gcongr
    _ = ((c⁻¹ : ℝ≥0) : ℝ≥0∞) * A * N * ∫⁻ w, h w := by
        rw [ENNReal.coe_inv hc0.ne']; ring
