import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.KernelDiagonalOfDecayThreshold

noncomputable section

namespace Formalism.MainNotions.LeviCoordinates

open MeasureTheory NumberField Set TopologicalSpace
open scoped InnerProductSpace ENNReal
open Formalism.MainNotions.S Formalism.MainNotions.PlaceDegreeData Formalism.MainNotions.BridgeLemma
open Formalism.HermitianLatticeCounting.S7 (decExp)

def DistTri : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (g k : Formalism.REAL.UJ ε), cartanDistance ε (g * k) ≤ cartanDistance ε g + cartanDistance ε k

theorem rrk_decExp_nonneg {h : ℝ} (hh : 0 ≤ h) (q : ℕ) {t : ℝ} (ht : 0 ≤ t) : 0 ≤ decExp h q t := by
  unfold decExp
  positivity

theorem rrk_decExp_half {h : ℝ} (hh : 0 ≤ h) (q : ℕ) {u : ℝ} (hu : 0 ≤ u) :
    2 * decExp (h / 8) q u ≤ decExp h q (u / 2) := by
  unfold decExp
  have hc : 0 ≤ Real.sqrt (2 * (q : ℝ)) := Real.sqrt_nonneg _
  have hm : min (u ^ 2) (u / Real.sqrt (2 * (q : ℝ))) ≤
      4 * min ((u / 2) ^ 2) (u / 2 / Real.sqrt (2 * (q : ℝ))) := by
    rw [mul_min_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 4)]
    apply min_le_min
    · exact le_of_eq (by ring)
    · have h0 : 0 ≤ u / Real.sqrt (2 * (q : ℝ)) := div_nonneg hu hc
      rw [show 4 * (u / 2 / Real.sqrt (2 * (q : ℝ))) = 2 * (u / Real.sqrt (2 * (q : ℝ))) by ring]
      linarith
  have hm1 : 0 ≤ min (u ^ 2) (u / Real.sqrt (2 * (q : ℝ))) := le_min (sq_nonneg u) (div_nonneg hu hc)
  nlinarith [mul_le_mul_of_nonneg_left hm hh]

theorem rrk_decExp_tri {h : ℝ} (hh : 0 ≤ h) (q : ℕ) {s t u : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) (hu : 0 ≤ u) (hle : u ≤ s + t) :
    2 * decExp (h / 8) q u ≤ decExp h q s + decExp h q t := by
  have hmax : s ≤ max s t := le_max_left s t
  have hM : u ≤ 2 * max s t := by
    have := le_max_right s t
    linarith
  have h8 : 0 ≤ h / 8 := div_nonneg hh (by norm_num)
  have h1 : decExp (h / 8) q u ≤ decExp (h / 8) q (2 * max s t) :=
    decay_exponent_monotone h8 q hu hM
  have h2 := rrk_decExp_half hh q (u := 2 * max s t) (by linarith)
  rw [show 2 * max s t / 2 = max s t by ring] at h2
  have hs0 := rrk_decExp_nonneg hh q hs
  have ht0 := rrk_decExp_nonneg hh q ht
  rcases le_total s t with hst | hst
  · rw [max_eq_right hst] at h1 h2
    linarith
  · rw [max_eq_left hst] at h1 h2
    linarith

theorem rrk_amgm {a b k P Q W : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hk : 0 ≤ k) (hW : 0 ≤ W) (hP : 0 ≤ P) (haP : a ≤ k * P)
    (hbQ : b ≤ k * Q) (hPQ : P * Q ≤ W ^ 2) : a * b ≤ k * W * ((a + b) / 2) := by
  have hab : 0 ≤ a * b := mul_nonneg ha hb
  have h1 : a * b ≤ (k * W) ^ 2 := by
    calc a * b ≤ (k * P) * (k * Q) := mul_le_mul haP hbQ hb (mul_nonneg hk hP)
      _ = k ^ 2 * (P * Q) := by ring
      _ ≤ k ^ 2 * W ^ 2 := mul_le_mul_of_nonneg_left hPQ (sq_nonneg k)
      _ = (k * W) ^ 2 := by ring
  have h2 : Real.sqrt (a * b) ≤ k * W := by
    calc Real.sqrt (a * b) ≤ Real.sqrt ((k * W) ^ 2) := Real.sqrt_le_sqrt h1
      _ = k * W := Real.sqrt_sq (mul_nonneg hk hW)
  have h3 : Real.sqrt (a * b) ≤ (a + b) / 2 := by
    have h4 : a * b ≤ ((a + b) / 2) ^ 2 := by nlinarith [sq_nonneg (a - b)]
    calc Real.sqrt (a * b) ≤ Real.sqrt (((a + b) / 2) ^ 2) := Real.sqrt_le_sqrt h4
      _ = (a + b) / 2 := Real.sqrt_sq (by linarith)
  calc a * b = Real.sqrt (a * b) * Real.sqrt (a * b) := (Real.mul_self_sqrt hab).symm
    _ ≤ k * W * ((a + b) / 2) := mul_le_mul h2 h3 (Real.sqrt_nonneg _) (mul_nonneg hk hW)

theorem ConvDecay_of (D : Formalism.BasicNotions.D7) (hdec : DiscreteSeriesDecayBound D) (X : CData) {n₀ : ℕ} {A : ℝ} (hX : X.HypB n₀ A) (h1 : X.GapAboveThreeHalvesPower)
    (hE : X.LowProj) (hh : 0 ≤ X.h) (htri : DistTri) (hφ : PhiIdem X) (hint : Integrable X.φ (X.I.muA X.μf)) :
    ConvDecay X X.qq (X.h / 8) := by
  have hH : X.μf.IsHaarMeasure := hX.2.1.2.2.2.1
  have : (X.I.muA X.μf).IsMulLeftInvariant := rr_muA_left X.I X.μf
  have hp : X.I.IsPosType X.e := hX.1.2.2.2.2.2.2.1.2.2.2.1
  set k0 : ℝ := fdegAll X.I X.σ X.w * (X.e 1).re with hk0
  have hk0n : 0 ≤ k0 := mul_nonneg X.fdegAll_nonneg (X.e_one_nonneg hp)
  set L : ℝ := ∫ g, ‖X.φ g‖ ∂(X.I.muA X.μf) with hL
  have hLn : 0 ≤ L := integral_nonneg fun _ => norm_nonneg _
  have hLe : ∫⁻ g, ‖X.φ g‖ₑ ∂(X.I.muA X.μf) = ENNReal.ofReal L := by
    rw [hL, ofReal_integral_norm_eq_lintegral_enorm hint]
  refine ⟨k0 * L, mul_nonneg hk0n hLn, fun z => ?_⟩
  set W : ℝ := ∏ v, Real.exp (-(decExp (X.h / 8) X.qq (cartanDistance (X.I.ε v) (z.1 v)))) with hW
  have hWn : 0 ≤ W := Finset.prod_nonneg fun v _ => (Real.exp_pos _).le
  have hpt : ∀ g : X.I.GA, ‖X.φ g‖ₑ * ‖X.φ (g⁻¹ * z)‖ₑ ≤
      ENNReal.ofReal (k0 * W / 2) * (‖X.φ g‖ₑ + ‖X.φ (g⁻¹ * z)‖ₑ) := by
    intro g
    have b1 := X.norm_φ_le D hdec hX h1 hE (X.qq_spec hX).1 g
    have b2 := X.norm_φ_le D hdec hX h1 hE (X.qq_spec hX).1 (g⁻¹ * z)
    have hPQ : (∏ v, Real.exp (-(decExp X.h X.qq (cartanDistance (X.I.ε v) (g.1 v))))) *
        (∏ v, Real.exp (-(decExp X.h X.qq (cartanDistance (X.I.ε v) ((g⁻¹ * z).1 v))))) ≤ W ^ 2 := by
      rw [← Finset.prod_mul_distrib, hW, ← Finset.prod_pow]
      refine Finset.prod_le_prod (fun v _ => by positivity) fun v _ => ?_
      rw [← Real.exp_add, ← Real.exp_nat_mul]
      apply Real.exp_le_exp.2
      have ht := htri X.I.n (X.I.ε v) (g.1 v) ((g⁻¹ * z).1 v)
      have ez : g.1 v * (g⁻¹ * z).1 v = z.1 v := by
        show g.1 v * ((g.1 v)⁻¹ * z.1 v) = z.1 v
        group
      rw [ez] at ht
      have := rrk_decExp_tri hh X.qq (cartan_distance_nonneg _ (g.1 v)) (cartan_distance_nonneg _ ((g⁻¹ * z).1 v))
        (cartan_distance_nonneg _ (z.1 v)) ht
      push_cast
      linarith
    have hr := rrk_amgm (norm_nonneg (X.φ g)) (norm_nonneg (X.φ (g⁻¹ * z))) hk0n hWn
      (Finset.prod_nonneg fun v _ => (Real.exp_pos _).le) b1 b2 hPQ
    rw [← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_mul (norm_nonneg _), ← ENNReal.ofReal_add (norm_nonneg _)
      (norm_nonneg _), ← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal (le_trans hr (le_of_eq ?_))
    ring
  have hm1 : Measurable fun g : X.I.GA => ‖X.φ g‖ₑ := hφ.1.enorm
  have hsh : ∫⁻ g, ‖X.φ (g⁻¹ * z)‖ₑ ∂(X.I.muA X.μf) = ENNReal.ofReal L := by
    rw [← hLe, ← lintegral_mul_left_eq_self (fun g => ‖X.φ g‖ₑ) z⁻¹]
    refine lintegral_congr fun g => ?_
    have e : g⁻¹ * z = (z⁻¹ * g)⁻¹ := by group
    rw [e, hφ.2.1, enorm_eq_nnnorm, enorm_eq_nnnorm, nnnorm_star]
  unfold rrk_Psi
  calc ∫⁻ g, ‖X.φ g‖ₑ * ‖X.φ (g⁻¹ * z)‖ₑ ∂(X.I.muA X.μf)
      ≤ ∫⁻ g, ENNReal.ofReal (k0 * W / 2) * (‖X.φ g‖ₑ + ‖X.φ (g⁻¹ * z)‖ₑ) ∂(X.I.muA X.μf) := lintegral_mono hpt
    _ = ENNReal.ofReal (k0 * W / 2) * (ENNReal.ofReal L + ENNReal.ofReal L) := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_add_left hm1, hLe, hsh]
    _ = ENNReal.ofReal (k0 * L * W) := by
        rw [← ENNReal.ofReal_add hLn hLn, ← ENNReal.ofReal_mul (by positivity)]
        congr 1; ring

theorem rrk_phi_int (D : Formalism.BasicNotions.D7) (hloc : LocalProjectorRealPlace D) (X : CData) {n₀ : ℕ} {A : ℝ} (hX : X.HypB n₀ A) (h1 : X.GapAboveThreeHalvesPower) :
    Integrable X.φ (X.I.muA X.μf) := by
  refine φ_integrable X hX (X.phOf_integrable fun v => ?_)
  exact (hloc X.I.n (X.I.ε v) (X.lam v) (hX.1.2.2.2.2.1 v) (X.H v) (X.σ v) (hX.2.1.1 v) (X.w v) (hX.2.1.2.1 v) X.h
    (hX.2.2 v) (h1 v)).1

theorem rrk_h_nonneg (X : CData) (h1 : X.GapAboveThreeHalvesPower) : 0 ≤ X.h := by
  unfold CData.GapAboveThreeHalvesPower at h1
  obtain ⟨v⟩ : Nonempty (InfinitePlace X.I.F) := inferInstance
  exact le_trans (by positivity) (h1 v)

theorem kernel_diagonal_of_triangle_inequality (D : Formalism.BasicNotions.D7) (h2 : adm2 D) (hdec : DiscreteSeriesDecayBound D) (hloc : LocalProjectorRealPlace D) (X : CData) {n₀ : ℕ}
    {A : ℝ} (hX : X.HypB n₀ A) (hn1 : 1 ≤ X.I.n) (h1 : X.GapAboveThreeHalvesPower) (h363 : X.GapAboveSquareRootThreshold 363) (hu : UnimodA X) (htri : DistTri)
    (hn : AllCount X (2 * (X.I.n : ℝ) ^ 2)) : X.KernelDiag :=
  kernel_diagonal_of_decay_threshold D hloc X hX hn1 h1 h363 hu
    (ConvDecay_of D hdec X hX h1 (lowest_K_type_projector_exists D h2 X hX) (rrk_h_nonneg X h1) htri (PhiIdem_of D hloc X hX h1)
      (rrk_phi_int D hloc X hX h1)) hn

end Formalism.MainNotions.LeviCoordinates

end
