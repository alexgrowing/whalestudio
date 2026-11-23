import Mathlib
import Formalism.MeanHeightDescent.AverageDegreeBounds.Assembly
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.SizeMu
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.DiscreteSpanOfLinIndep

open Module NumberField

noncomputable section

namespace Formalism.ExtensionFiltration

theorem log_covolume_slope_mu : LcvMu := by
  intro K _ _ _ _ d hd X hX M hM
  have hfg : M.FG := Submodule.IsLattice.fg (self := hM)
  have hspan : Submodule.span K (M : Set (Fin d → K)) = ⊤ :=
    Submodule.IsLattice.span_eq_top (self := hM)
  have hrk : Formalism.HN.rkK M = d := by
    unfold Formalism.HN.rkK
    rw [hspan]
    simp
  have hne : M ≠ ⊥ := by
    intro h
    have h2 : Formalism.HN.rkK (⊥ : Submodule (𝓞 K) (Fin d → K)) = 0 := by
      unfold Formalism.HN.rkK
      simp
    rw [h, h2] at hrk
    omega
  obtain ⟨-, hmu, -⟩ := Formalism.HN.size_maximal_slope K (Fin d → K) (Fin d) (Pi.basisFun K (Fin d)) X hX M hfg hne
  have hht : 0 < Formalism.HN.ht (Pi.basisFun K (Fin d)) X M :=
    (Formalism.HN.place_lattice_structure K (Fin d → K) (Fin d) (Pi.basisFun K (Fin d)) X hX M hfg).2.2
  have hn : (finrank ℚ K : ℝ) = 2 * (Formalism.HN.nPl K : ℝ) := by
    exact_mod_cast Formalism.HN.sizeMu_finrank_eq K
  have hf : (0 : ℝ) < Formalism.HN.nPl K := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card (InfinitePlace K))
  have hDr : (0 : ℝ) < d := by exact_mod_cast hd
  rw [hmu, Formalism.HN.size, Real.log_rpow hht, hrk, Formalism.DivisionValues.lcv, hn]
  field_simp

set_option maxHeartbeats 800000 in

theorem covolume_assembly_holds : CovolumeEstimateOfSlopeChain := by
  unfold CovolumeEstimateOfSlopeChain
  intro K _ _ _ _ d D hD hdD XW hXW M hM Pl _ w c1 ua muU muA muN muG mmax dA dB dN dg db C1 Cf Cc cfl ε δ Q P Λ G P9 pq q' logOm x eps L b rd Lchi llx LL0 B0 f m k S η h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25 h26 h27 h28 h29 h30 h31 h32 h33 h34 h35 h36 h37 h38 h39 h40 h41 h42 h43 h44 h45 h46 h47 h48 h49 h50
  have hd : 0 < d := by omega
  have hlcv := log_covolume_slope_mu K d hd XW hXW M hM
  have hDpos : (0 : ℝ) < D := by exact_mod_cast hD
  have hdD' : (d : ℝ) = D := by exact_mod_cast hdD
  rw [hlcv, hdD', neg_div, mul_div_cancel_left₀ _ hDpos.ne']
  set Sw := ∑ τ, w τ with hSwdef
  set Su := ∑ τ, ua τ with hSudef
  set X := 2 * (C1 * LL0 * Su + b / 4) with hXdef
  have hQ0 : 0 ≤ Q := le_trans (abs_nonneg _) h10
  have hL1 : 1 ≤ L := by
    rw [h38]
    exact Real.one_le_rpow h36 h37.le
  have hb1 : 1 ≤ b := by
    rw [h39]
    exact Real.one_le_exp (by linarith)
  have hlrd : 0 ≤ Real.log rd := Real.log_nonneg h40
  have hlx : 0 ≤ Real.log x := Real.log_nonneg h36
  have hlogbrd : Real.log (b * rd) = L + Real.log rd := by
    rw [Real.log_mul (by linarith : (0:ℝ) < b).ne' (by linarith : (0:ℝ) < rd).ne', h39, Real.log_exp]
  have hLL0 : LL0 ≤ 4 * L * llx := by
    rw [h46, hlogbrd]
    linarith [mul_nonneg (sub_nonneg.mpr h41) (by linarith : (0:ℝ) ≤ llx),
      mul_nonneg (by linarith : (0:ℝ) ≤ L) (sub_nonneg.mpr h45), h43, h44, h42]
  have hLL0nn : 0 ≤ LL0 := by
    rw [h46, hlogbrd]
    linarith [mul_nonneg (by linarith : (0:ℝ) ≤ L + Real.log rd) (by linarith : (0:ℝ) ≤ llx), h42, hlx]
  have hw0 : ∀ τ, 0 ≤ w τ := fun τ => (h28 τ).1
  have hSw0 : 0 ≤ Sw := Finset.sum_nonneg (fun τ _ => hw0 τ)
  have hSw : Sw ≤ 2 * b * f := by
    have e1 : Sw ≤ ∑ _τ : Pl, 2 * b := Finset.sum_le_sum (fun τ _ => (h28 τ).2)
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at e1
    linarith [mul_le_mul_of_nonneg_right h31 (by linarith : (0:ℝ) ≤ 2 * b)]
  have hSu0 : 0 ≤ Su := by linarith [h27]
  have hSu : Su ≤ 8 * b * f * m := by
    have e1 : Su ≤ ∑ τ, (2 * m * w τ + 4 * b) :=
      Finset.sum_le_sum (fun τ _ => by linarith [(h26 τ).2, h29, h30])
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      ← hSwdef] at e1
    linarith [mul_le_mul_of_nonneg_left hSw (by linarith : (0:ℝ) ≤ 2 * m),
      mul_le_mul_of_nonneg_right h31 (by linarith : (0:ℝ) ≤ 4 * b),
      mul_le_mul_of_nonneg_left h32 (mul_nonneg (by linarith : (0:ℝ) ≤ b) (by linarith : (0:ℝ) ≤ f))]
  have hwc1 : -(pq * logOm / 2 + Cc * q' * (Real.log rd + Lchi)) * Sw ≤ ∑ τ, w τ * c1 τ := by
    rw [hSwdef, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro τ _
    have h := (abs_le.mp (h25 τ)).1
    linarith [mul_le_mul_of_nonneg_left h (hw0 τ), hw0 τ]
  have hpq : ∑ ρ, pq * w ρ * logOm = pq * logOm * Sw := by
    rw [hSwdef, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro ρ _
    ring
  have hδ : δ * dN ≤ (1 / 12) * dN := mul_le_mul_of_nonneg_right h18 h13.le
  have hdg : (3 / 4) * dN ≤ dg := by linarith [h14, h16, hδ]
  have hmuG : muN - 12 * δ * Q ≤ muG := by
    have e1 : db * (-(3 * Q)) ≤ db * (muN - mmax - G) :=
      mul_le_mul_of_nonneg_left (by linarith [(abs_le.mp h20).1, h21, h22]) h15
    have f1 : Q * db ≤ Q * (3 * δ * dN) := mul_le_mul_of_nonneg_left h16 hQ0
    have f2 : (12 * δ * Q) * ((3 / 4) * dN) ≤ (12 * δ * Q) * dg :=
      mul_le_mul_of_nonneg_left hdg (mul_nonneg (mul_nonneg (by norm_num) h17) hQ0)
    have hdgpos : 0 < dg := by linarith
    have h19' : (dg + db) * muN ≤ dg * muG + db * (mmax + G) := by
      rw [← h14]
      exact h19
    have key : 0 ≤ dg * (muG - muN + 12 * δ * Q) := by linarith [h19', e1, f1, f2]
    by_contra hcon
    push_neg at hcon
    have hneg : dg * (muG - muN + 12 * δ * Q) < 0 := mul_neg_of_pos_of_neg hdgpos (by linarith)
    linarith
  have hX0 : 0 ≤ X := by
    rw [hXdef]
    have := mul_nonneg (mul_nonneg h48 hLL0nn) hSu0
    linarith
  have hdBpos : 0 < dB := by linarith
  have hmuN : -X + 2 * cfl - P - b / 2 ≤ muN := by
    have g1 : dA * (-X) ≤ dA * muU := mul_le_mul_of_nonneg_left h1 h4.le
    have g1' : dB * (-X) ≤ dA * (-X) := by
      linarith [mul_nonneg (by linarith : (0:ℝ) ≤ dB - dA) hX0]
    have g2 : (dB - dA) * (2 * cfl) ≤ (dB - dA) * Q :=
      mul_le_mul_of_nonneg_left (le_trans (le_abs_self _) h10) (by linarith)
    have g3 : (dB - dA) * Λ ≤ (dB - dA) * Q := mul_le_mul_of_nonneg_left h11 (by linarith)
    have g4 : (dB - dA) * Q ≤ (ε * dB) * Q := mul_le_mul_of_nonneg_right (by linarith) hQ0
    have g5 : dA * P ≤ dB * P := mul_le_mul_of_nonneg_right h5 h8
    have g6 : dA * (muU + 2 * cfl - P) ≤ dA * (muA - P) := mul_le_mul_of_nonneg_left (by linarith) h4.le
    have g7 : dB * (ε * Q) ≤ dB * (b / 4) := mul_le_mul_of_nonneg_left h12 hdBpos.le
    have key : dB * (-X + 2 * cfl - P - b / 2) ≤ dB * muN := by
      linarith [h9, g1, g1', g2, g3, g4, g5, g6, g7]
    exact le_of_mul_le_mul_left key hdBpos
  have hμlow : -Formalism.HN.muDef (Pi.basisFun K (Fin d)) XW M ≤ X - 2 * cfl + 3 * b / 2 := by
    linarith [h23, hmuG, hmuN, h24]
  have hcfl : -(2 * cfl) ≤ pq * logOm * Sw + 2 * (Cc * q' * (Real.log rd + Lchi)) * Sw +
      2 * Cf * q' * Real.log rd * Sw + 2 * Cf * L := by
    rw [h2]
    linarith [hwc1]
  have hB0 : B0 = f * m * b * L := by rw [h47, ← h38]
  have hfm : 1 ≤ f * m := by
    have := mul_le_mul h33 h32 zero_le_one (by linarith)
    linarith
  have hfmb : 1 ≤ f * m * b := by
    have := mul_le_mul hfm hb1 zero_le_one (by linarith)
    linarith
  have hfmL : 1 ≤ f * m * L := by
    have := mul_le_mul hfm hL1 zero_le_one (by linarith)
    linarith
  have hB0nn : 0 ≤ B0 := by
    rw [hB0]
    exact mul_nonneg (by linarith) (by linarith)
  have hLB : L ≤ B0 := by
    rw [hB0]
    linarith [mul_le_mul_of_nonneg_right hfmb (show (0:ℝ) ≤ L by linarith)]
  have hbB : b ≤ B0 := by
    rw [hB0]
    linarith [mul_le_mul_of_nonneg_left hfmL (show (0:ℝ) ≤ b by linarith)]
  have hBll : B0 ≤ B0 * llx := by linarith [mul_le_mul_of_nonneg_left h45 hB0nn]
  have hT1 : C1 * LL0 * Su ≤ 32 * (C1 * (B0 * llx)) := by
    have e1 : LL0 * Su ≤ (4 * L * llx) * (8 * b * f * m) :=
      mul_le_mul hLL0 hSu hSu0 (mul_nonneg (mul_nonneg (by norm_num) (by linarith)) (by linarith))
    have e2 := mul_le_mul_of_nonneg_left e1 h48
    have e5 : C1 * ((4 * L * llx) * (8 * b * f * m)) = 32 * (C1 * (B0 * llx)) := by
      rw [hB0]
      ring
    linarith [e2, e5]
  have hT2 : Cc * q' * (Real.log rd + Lchi) * Sw ≤ 4 * (Cc * (B0 * llx)) := by
    have e1 : q' * (Real.log rd + Lchi) ≤ m * (2 * L) :=
      mul_le_mul h35 (by linarith) (by linarith) (by linarith)
    have e2 : q' * (Real.log rd + Lchi) * Sw ≤ m * (2 * L) * (2 * b * f) :=
      mul_le_mul e1 hSw hSw0 (mul_nonneg (by linarith) (by linarith))
    have e3 := mul_le_mul_of_nonneg_left e2 h50
    have e4 : Cc * B0 ≤ Cc * (B0 * llx) := mul_le_mul_of_nonneg_left hBll h50
    have e5 : Cc * (m * (2 * L) * (2 * b * f)) = 4 * (Cc * B0) := by
      rw [hB0]
      ring
    linarith [e3, e4, e5]
  have hT3 : Cf * q' * Real.log rd * Sw + Cf * L ≤ 3 * (Cf * (B0 * llx)) := by
    have e1 : q' * Real.log rd ≤ m * L := mul_le_mul h35 h41 hlrd (by linarith)
    have e2 : q' * Real.log rd * Sw ≤ m * L * (2 * b * f) := mul_le_mul e1 hSw hSw0 (mul_nonneg (by linarith) (by linarith))
    have e3 := mul_le_mul_of_nonneg_left e2 h49
    have e4 : Cf * L ≤ Cf * B0 := mul_le_mul_of_nonneg_left hLB h49
    have e5 : Cf * (m * L * (2 * b * f)) = 2 * (Cf * B0) := by
      rw [hB0]
      ring
    have e6 : Cf * B0 ≤ Cf * (B0 * llx) := mul_le_mul_of_nonneg_left hBll h49
    linarith [e3, e4, e5, e6]
  have hT4 : b ≤ B0 * llx := le_trans hbB hBll
  have hpos : 0 ≤ Cf * (B0 * llx) := mul_nonneg h49 (mul_nonneg hB0nn (by linarith))
  rw [hpq]
  linarith [hμlow, hcfl, hT1, hT2, hT3, hT4, hXdef, hpos]

end Formalism.ExtensionFiltration
