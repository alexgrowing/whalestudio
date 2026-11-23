import Mathlib
import GroundTheory.HeightsAndTheta.Heights.MultinomialWeights.StatementsEnd
import GroundTheory.HeightsAndTheta.Heights.MultinomialWeights.StatementsHomDecomp
import GroundTheory.HeightsAndTheta.Heights.StabilizerCovolume.RecordEigenInputs
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.TheoremB

open MvPolynomial Finset Filter Topology

theorem lineF_isHomogeneous {d : IndexData} (u : Idx d → ℚ) :
    (lineF d u).IsHomogeneous (d.D + 1) := by
  have h1 : (lineClass d u).IsHomogeneous 1 := by
    unfold lineClass lamDotX
    refine IsHomogeneous.neg ?_
    exact IsHomogeneous.sum _ _ _ (fun p _ => isHomogeneous_C_mul_X (u p) p)
  have := h1.pow (d.D + 1)
  simpa [lineF] using this

theorem spread_pos {d : IndexData} {u : Weight d} (hu : IsRegular d u) (τ : Fin d.f) :
    0 < spread d u τ := by
  have h2 := d.two_le_N
  let a : Fin d.N := ⟨0, by omega⟩
  let b : Fin d.N := ⟨1, by omega⟩
  have hab : 0 < u (τ, a) - u (τ, b) := hu τ a b rfl
  have h1 : u (τ, a) ≤ univ.sup' (finN_nonempty d) (fun i => u (τ, i)) :=
    le_sup' (fun i => u (τ, i)) (mem_univ a)
  have h3 : univ.inf' (finN_nonempty d) (fun i => u (τ, i)) ≤ u (τ, b) :=
    inf'_le (fun i => u (τ, i)) (mem_univ b)
  unfold spread
  linarith

theorem TheoremTUpper.proof (hLim : LimitsExist.Statement) (hEv : HeightEvaluation.Statement)
    (hCB : CBounds.Statement) (hNU : NormUbar.Statement) (hTA : TermA.Statement)
    (hTB : TermB.Statement) (hTC : TermC.Statement) (hTD : TermD.Statement)
    (hPL : NineStatements.PrimeLogSum.Statement) (hF3 : HomDecompExists.Statement) :
    TheoremTUpper.Statement := by
  intro C7 hC7
  obtain ⟨CD, hCD⟩ := hTD C7 hC7
  obtain ⟨C5, hC5⟩ := hPL
  refine ⟨max CD 0 * (1 + max C5 0) + 6, ?_⟩
  intro d S u g B0 hT hB0 hcard h82 hI9 hP1 hPF h7 hM5
  set M : ℝ := max CD 0 * (1 + max C5 0) with hMdef
  have hM : 0 ≤ M := mul_nonneg (le_max_right _ _) (by linarith [le_max_right C5 0])
  obtain ⟨A0, b0, hA0, hb0⟩ := hLim d S h82 B0
  obtain ⟨Q, hQ⟩ := hF3 d (lineF d u) (lineF_isHomogeneous u)
  have hdom : IsDominant d (uR d u) := fun τ a b h => (hT.1 τ a b h).le
  have hEq := (hEv d S h82 B0 A0 b0 hA0 hb0 u Q hQ).2
  have ha := hTA d S hI9 u hdom
  have hb := hTB d S u g B0 hT hB0 hM5 Q hQ
  have hc := hTC d S h82 hP1 B0 A0 b0 hA0 hb0 hPF

  have hf : (1 : ℝ) ≤ d.f := by exact_mod_cast S.f_pos
  have hN : (2 : ℝ) ≤ d.N := by exact_mod_cast d.two_le_N
  have hrd := S.one_le_rd
  set bz := bZero d (uR d u) g with hbz
  have hHn : 0 ≤ ‖uR d u‖ / g := div_nonneg (norm_nonneg _) hT.2.1.le
  have hbz16 : 16 ≤ bz := by
    have hfN : 4 ≤ (d.f : ℝ) * (d.N : ℝ) ^ 2 := by nlinarith
    rw [hbz, bZero]; nlinarith
  have hB0_16 : 16 ≤ B0 := by
    rw [hB0]; exact Nat.le_floor (by push_cast; linarith)
  have hB0le : (B0 : ℝ) ≤ bz := by rw [hB0]; exact Nat.floor_le (by linarith)
  have hB0ge : (16 : ℝ) ≤ B0 := by exact_mod_cast hB0_16
  have hcardB0 : S.level.primeFactors.card ≤ B0 := by rw [hB0]; exact Nat.le_floor hcard

  set Λ := Real.log (bz * S.rd) + |S.lval| with hΛdef
  have hlogB0 : Real.log B0 ≤ Real.log (bz * S.rd) :=
    Real.log_le_log (by linarith) (by nlinarith)
  have hlogB0rd : Real.log (B0 * S.rd) ≤ Real.log (bz * S.rd) :=
    Real.log_le_log (by positivity) (mul_le_mul_of_nonneg_right hB0le (by linarith))
  have hlogB0nn : 0 ≤ Real.log B0 := Real.log_nonneg (by linarith)
  have hΛ0 : 0 ≤ Λ := by linarith [abs_nonneg S.lval]
  have hlogΛ : Real.log B0 ≤ Λ := by linarith [abs_nonneg S.lval]

  have hsum0 : 0 ≤ ∑ p ∈ S.level.primeFactors, Real.log p / (p : ℝ) :=
    sum_nonneg fun p _ => div_nonneg (Real.log_natCast_nonneg p) (Nat.cast_nonneg p)
  have hsum : ∑ p ∈ S.level.primeFactors, Real.log p / (p : ℝ) ≤ max C5 0 * Real.log B0 := by
    calc ∑ p ∈ S.level.primeFactors, Real.log p / (p : ℝ)
        ≤ ∑ p ∈ S.level.primeFactors, Real.log p / ((p : ℝ) - 1) := by
          refine sum_le_sum fun p hp => ?_
          have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
          exact div_le_div_of_nonneg_left (Real.log_natCast_nonneg p) (by linarith) (by linarith)
      _ ≤ C5 * Real.log B0 :=
          hC5 B0 (by omega) _ (fun p hp => Nat.prime_of_mem_primeFactors hp) hcardB0
      _ ≤ max C5 0 * Real.log B0 := mul_le_mul_of_nonneg_right (le_max_left _ _) hlogB0nn
  have hA0low : -(M * Λ) ≤ A0 := by
    have hd := hCD d S B0 A0 (by omega) h7 hA0
    have e1 : CD * Real.log B0 ≤ max CD 0 * Real.log B0 :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) hlogB0nn
    have e2 : CD * ∑ p ∈ S.level.primeFactors, Real.log p / (p : ℝ) ≤
        max CD 0 * (max C5 0 * Real.log B0) :=
      (mul_le_mul_of_nonneg_right (le_max_left _ _) hsum0).trans
        (mul_le_mul_of_nonneg_left hsum (le_max_right _ _))
    have e3 : M * Real.log B0 ≤ M * Λ := mul_le_mul_of_nonneg_left hlogΛ hM
    have e4 : M * Real.log B0 = max CD 0 * Real.log B0 + max CD 0 * (max C5 0 * Real.log B0) := by
      rw [hMdef]; ring
    linarith

  have hτ : ∀ τ : Fin d.f, -((M + 4) * Λ * ∑ i : Fin d.N, |uR d u (τ, i)|) ≤
      A0 * cTau d (uR d u) τ + ((d.j : ℝ) * A0 + (d.N : ℝ) * b0) * ubar d (uR d u) τ := by
    intro τ
    obtain ⟨hc0, hc1⟩ := hCB d (uR d u) hdom τ
    have hn := hNU d (uR d u) τ
    set s := ∑ i : Fin d.N, |uR d u (τ, i)|
    have hs : 0 ≤ s := sum_nonneg fun i _ => abs_nonneg _
    have hMΛ : 0 ≤ M * Λ := mul_nonneg hM hΛ0
    have p1 : -(M * Λ) * s ≤ A0 * cTau d (uR d u) τ := by
      rcases le_total 0 A0 with h | h
      · nlinarith [mul_nonneg h hc0, mul_nonneg hMΛ hs]
      · have q1 : A0 * s ≤ A0 * cTau d (uR d u) τ := mul_le_mul_of_nonpos_left hc1 h
        have q2 : -(M * Λ) * s ≤ A0 * s := mul_le_mul_of_nonneg_right hA0low hs
        linarith
    have hcΛ : |(d.j : ℝ) * A0 + (d.N : ℝ) * b0| ≤ 4 * (d.N : ℝ) * Λ := by
      have : 4 * (d.N : ℝ) * (Real.log (B0 * S.rd) + |S.lval|) ≤ 4 * (d.N : ℝ) * Λ :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      linarith
    have p2 : |((d.j : ℝ) * A0 + (d.N : ℝ) * b0) * ubar d (uR d u) τ| ≤ 4 * Λ * s := by
      rw [abs_mul]
      calc |(d.j : ℝ) * A0 + (d.N : ℝ) * b0| * |ubar d (uR d u) τ|
          ≤ 4 * (d.N : ℝ) * Λ * |ubar d (uR d u) τ| :=
            mul_le_mul_of_nonneg_right hcΛ (abs_nonneg _)
        _ = 4 * Λ * ((d.N : ℝ) * |ubar d (uR d u) τ|) := by ring
        _ ≤ 4 * Λ * s := mul_le_mul_of_nonneg_left hn (by positivity)
    have p3 := neg_abs_le (((d.j : ℝ) * A0 + (d.N : ℝ) * b0) * ubar d (uR d u) τ)
    have p4 : -(M * Λ) * s - 4 * Λ * s = -((M + 4) * Λ * s) := by ring
    linarith

  set X1 := ∑ p : Idx d, |(u p : ℝ)| with hX1
  have hX1eq : ∑ τ : Fin d.f, ∑ i : Fin d.N, |uR d u (τ, i)| = X1 := by
    rw [hX1, Fintype.sum_prod_type]; rfl
  have hX10 : 0 ≤ X1 := sum_nonneg fun p _ => abs_nonneg _
  have hsumτ : -((M + 4) * Λ * X1) ≤ ∑ τ : Fin d.f, (A0 * cTau d (uR d u) τ +
      ((d.j : ℝ) * A0 + (d.N : ℝ) * b0) * ubar d (uR d u) τ) := by
    have := sum_le_sum fun τ (_ : τ ∈ (univ : Finset (Fin d.f))) => hτ τ
    rw [sum_neg_distrib, ← mul_sum, hX1eq] at this
    exact this

  set X2 := (jPrime d : ℝ) * ∑ τ : Fin d.f, spread d (uR d u) τ with hX2
  have hj' : (1 : ℝ) ≤ jPrime d := by
    have h1 := d.one_le_j; have h2 := d.j_lt_N
    have : 1 ≤ jPrime d := by unfold jPrime; omega
    exact_mod_cast this
  have hspr : 0 < ∑ τ : Fin d.f, spread d (uR d u) τ :=
    sum_pos (fun τ _ => spread_pos hT.1 τ) ⟨tau0 S, mem_univ _⟩
  have hX2pos : 0 < X2 := mul_pos (by linarith) hspr
  set L := S.vol * (degAt d u : ℝ) with hL
  have hD1 : (0 : ℝ) < (d.D : ℝ) + 1 := by positivity
  have hcoef : 0 < 4 / ((d.f : ℝ) * d.N) * ((d.D : ℝ) + 1) := by
    have : 0 < (d.f : ℝ) * d.N := by positivity
    positivity
  have hbr : |restTot S B0 Q| ≤ 4 / ((d.f : ℝ) * d.N) * ((d.D : ℝ) + 1) * L * X2 := by
    rw [hX2]; linarith [hb]
  have hL0 : 0 ≤ L := by
    by_contra hneg0
    have hneg : L < 0 := not_le.mp hneg0
    have : 4 / ((d.f : ℝ) * d.N) * ((d.D : ℝ) + 1) * L * X2 < 0 :=
      mul_neg_of_neg_of_pos (mul_neg_of_pos_of_neg hcoef hneg) hX2pos
    linarith [abs_nonneg (restTot S B0 Q)]
  have hKL : 0 ≤ ((d.D : ℝ) + 1) * L := mul_nonneg hD1.le hL0
  have h42 : 4 / ((d.f : ℝ) * d.N) ≤ 2 := by
    have hfN : (1 : ℝ) * 2 ≤ (d.f : ℝ) * d.N := mul_le_mul hf hN (by norm_num) (by linarith)
    rw [div_le_iff₀ (by positivity)]; linarith
  have hrest : -(2 * (((d.D : ℝ) + 1) * L * X2)) ≤ restTot S B0 Q := by
    have e1 : 4 / ((d.f : ℝ) * d.N) * ((d.D : ℝ) + 1) * L * X2 ≤ 2 * (((d.D : ℝ) + 1) * L * X2) := by
      calc 4 / ((d.f : ℝ) * d.N) * ((d.D : ℝ) + 1) * L * X2
          = 4 / ((d.f : ℝ) * d.N) * (((d.D : ℝ) + 1) * L * X2) := by ring
        _ ≤ 2 * (((d.D : ℝ) + 1) * L * X2) :=
          mul_le_mul_of_nonneg_right h42 (mul_nonneg hKL hX2pos.le)
    linarith [neg_abs_le (restTot S B0 Q)]

  have hmain : ((d.D : ℝ) + 1) * L * (-((M + 4) * Λ * X1)) ≤ ((d.D : ℝ) + 1) * L *
      ∑ τ : Fin d.f, (A0 * cTau d (uR d u) τ +
        ((d.j : ℝ) * A0 + (d.N : ℝ) * b0) * ubar d (uR d u) τ) :=
    mul_le_mul_of_nonneg_left hsumτ hKL
  have key : (M + 4) * Λ * X1 + 2 * X2 ≤ (M + 6) * (Λ * X1 + X2) := by
    linarith [mul_nonneg hΛ0 hX10, mul_nonneg hM hX2pos.le, hX2pos]
  have hkey := mul_le_mul_of_nonneg_left key hKL
  have e5 : -(M + 6) * ((d.D : ℝ) + 1) * L * (Λ * X1 + X2) = -(((d.D : ℝ) + 1) * L * ((M + 6) * (Λ * X1 + X2))) := by ring
  have e6 : ((d.D : ℝ) + 1) * L * ((M + 4) * Λ * X1 + 2 * X2) = -(((d.D : ℝ) + 1) * L * (-((M + 4) * Λ * X1))) + 2 * (((d.D : ℝ) + 1) * L * X2) := by ring
  have fin : -(M + 6) * ((d.D : ℝ) + 1) * L * (Λ * X1 + X2) ≤ bigP S B0 u := by
    rw [e5]
    linarith [ha, hrest, hmain, hkey, hEq]
  exact fin

end GroundTheory.Heights₂.Heights.TheoremB
