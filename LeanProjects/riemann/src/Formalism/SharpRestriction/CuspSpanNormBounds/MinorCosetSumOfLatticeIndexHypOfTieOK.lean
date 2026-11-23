import Formalism.SharpRestriction.CuspSpanNormBounds.KTwoCosetCount

noncomputable section

namespace Formalism.MainNotions.KTwoCosetCount

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section G

def ccOf (CH Cl : ℝ) : ℝ := 17 + 4 / Cl + 4 * |CH|

theorem frameExp_le {r l : ℕ} (hl : l ≤ r) : frameExp r l ≤ r * r := by
  unfold frameExp
  calc ∑ a ∈ Finset.Icc 1 l, (r + 1 - a) ≤ ∑ a ∈ Finset.Icc 1 l, r :=
        Finset.sum_le_sum fun a ha => by
          simp only [Finset.mem_Icc] at ha
          omega
    _ = l * r := by simp
    _ ≤ r * r := Nat.mul_le_mul_right r hl

theorem expo_le {x a J R M F Nn : ℝ} (hx : 0 ≤ x) (ha : 0 ≤ a) (hJ : 0 ≤ J) (hJR : J ≤ R) (hNn : 0 ≤ Nn) (hNF : Nn ≤ F)
    (hR : 1 ≤ R) (hRM : R ≤ M) (hF : 1 ≤ F) :
    J + (6 + x * (2 * (R * R)) + (1 + a * M) * (2 * R)) * (2 * Nn * J) ≤
      (17 + 4 * x + 4 * a) * M ^ 2 * F * ((17 + 4 * x + 4 * a) * R) := by
  have hR0 : 0 ≤ R := by linarith
  have hM1 : 1 ≤ M := le_trans hR hRM
  have hM0 : 0 ≤ M := by linarith
  have hF0 : 0 ≤ F := by linarith
  have hRM2 : R ≤ M ^ 2 := by nlinarith
  have hc : 1 ≤ 17 + 4 * x + 4 * a := by linarith
  have hA : 6 + x * (2 * (R * R)) + (1 + a * M) * (2 * R) ≤ (8 + 2 * x + 2 * a) * M ^ 2 := by
    have h1 : R * R ≤ M ^ 2 := by nlinarith
    have h3 : a * M * R ≤ a * M ^ 2 := by
      have h5 : M * R ≤ M ^ 2 := by nlinarith
      nlinarith
    have h4 : (1 : ℝ) ≤ M ^ 2 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left h1 hx]
  have hB : 2 * Nn * J ≤ 2 * F * R := by nlinarith
  have hApos : 0 ≤ 6 + x * (2 * (R * R)) + (1 + a * M) * (2 * R) := by
    have h1 : 0 ≤ x * (2 * (R * R)) := mul_nonneg hx (by nlinarith)
    have h2 : 0 ≤ (1 + a * M) * (2 * R) := mul_nonneg (by nlinarith) (by linarith)
    linarith
  have hstep : (6 + x * (2 * (R * R)) + (1 + a * M) * (2 * R)) * (2 * Nn * J) ≤
      (8 + 2 * x + 2 * a) * M ^ 2 * (2 * F * R) :=
    mul_le_mul hA hB (by nlinarith) (by nlinarith)
  have hMF : 1 ≤ M ^ 2 * F := by nlinarith
  have hJ2 : J ≤ M ^ 2 * F * R := by nlinarith
  have hQ : 0 ≤ (17 + 4 * x + 4 * a) * M ^ 2 * F * R := by
    have : 0 ≤ M ^ 2 * F * R := by nlinarith
    nlinarith
  have hc2 : (17 + 4 * x + 4 * a) * M ^ 2 * F * R ≤
      (17 + 4 * x + 4 * a) * M ^ 2 * F * ((17 + 4 * x + 4 * a) * R) := by
    nlinarith [mul_le_mul_of_nonneg_left hc hQ]
  nlinarith

theorem final_arith {L Cl CH rd : ℝ} {r m f n j : ℕ} (hL : 1 < L) (hCl : 0 < Cl) (hrd1 : 1 ≤ rd)
    (hrdL : Real.log rd ≤ L / Cl) (hr : 1 ≤ r) (hrm : r ≤ m) (hjr : j ≤ r) (hnf : n ≤ f) (hf : 1 ≤ f) :
    (2 : ℝ) ^ j * ((64 * (rd ^ (((2 * (r * r) : ℕ)) : ℝ) * (max 1 (2 * Real.exp L ^ (CH * (m : ℝ)))) ^ (2 * r))) ^ (2 * n)) ^ j ≤
      (Real.exp L ^ (ccOf CH Cl * (m : ℝ) ^ 2 * f)) ^ (ccOf CH Cl * (r : ℝ)) := by
  have hL0 : 0 < L := by linarith
  have h2 : (2:ℝ) ≤ Real.exp L := by have := Real.add_one_le_exp L; linarith
  have hrdpos : 0 < rd := by linarith
  have hrd : rd ≤ Real.exp (L / Cl) := by
    rw [← Real.exp_log hrdpos]
    exact Real.exp_le_exp.2 hrdL
  have hx : 0 ≤ 1 / Cl := by positivity
  have ha : 0 ≤ |CH| := abs_nonneg _
  have hM : max 1 (2 * Real.exp L ^ (CH * (m:ℝ))) ≤ Real.exp (L * (1 + |CH| * m)) := by
    have e1 : Real.exp L ^ (CH * (m:ℝ)) ≤ Real.exp (L * (|CH| * m)) := by
      rw [← Real.exp_mul]
      apply Real.exp_le_exp.2
      apply mul_le_mul_of_nonneg_left _ hL0.le
      exact mul_le_mul_of_nonneg_right (le_abs_self CH) (Nat.cast_nonneg m)
    have e2 : (1:ℝ) ≤ Real.exp (L * (|CH| * m)) := Real.one_le_exp (by positivity)
    have e3 : Real.exp (L * (1 + |CH| * m)) = Real.exp L * Real.exp (L * (|CH| * m)) := by
      rw [← Real.exp_add]
      ring_nf
    rw [e3]
    apply max_le
    · nlinarith
    · nlinarith
  have hrdp : rd ^ (((2 * (r * r) : ℕ)) : ℝ) ≤ Real.exp (L * (1 / Cl * (2 * ((r:ℝ) * r)))) := by
    calc rd ^ (((2 * (r * r) : ℕ)) : ℝ) ≤ (Real.exp (L / Cl)) ^ (((2 * (r * r) : ℕ)) : ℝ) :=
          Real.rpow_le_rpow hrdpos.le hrd (by positivity)
      _ = Real.exp (L * (1 / Cl * (2 * ((r:ℝ) * r)))) := by
          rw [← Real.exp_mul]
          congr 1
          push_cast
          ring
  have h64 : (64:ℝ) ≤ Real.exp (L * 6) := by
    rw [show L * 6 = ((6 : ℕ) : ℝ) * L by push_cast; ring, Real.exp_nat_mul]
    calc (64:ℝ) = 2 ^ 6 := by norm_num
      _ ≤ Real.exp L ^ 6 := pow_le_pow_left₀ (by norm_num) h2 6
  have hA : 64 * (rd ^ (((2 * (r * r) : ℕ)) : ℝ) * (max 1 (2 * Real.exp L ^ (CH * (m : ℝ)))) ^ (2 * r)) ≤
      Real.exp (L * 6) * (Real.exp (L * (1 / Cl * (2 * ((r:ℝ) * r)))) * Real.exp (L * (1 + |CH| * m)) ^ (2 * r)) := by
    have hmax0 : 0 ≤ max 1 (2 * Real.exp L ^ (CH * (m : ℝ))) := le_trans zero_le_one (le_max_left _ _)
    gcongr
  have h2j : (2:ℝ) ^ j ≤ Real.exp L ^ j := pow_le_pow_left₀ (by norm_num) h2 j
  have hexpo := expo_le (x := 1 / Cl) (a := |CH|) (J := (j:ℝ)) (R := (r:ℝ)) (M := (m:ℝ)) (F := (f:ℝ)) (Nn := (n:ℝ))
    hx ha (Nat.cast_nonneg j) (by exact_mod_cast hjr) (Nat.cast_nonneg n) (by exact_mod_cast hnf)
    (by exact_mod_cast hr) (by exact_mod_cast hrm) (by exact_mod_cast hf)
  have hcc : ccOf CH Cl = 17 + 4 * (1 / Cl) + 4 * |CH| := by unfold ccOf; ring
  calc (2 : ℝ) ^ j * ((64 * (rd ^ (((2 * (r * r) : ℕ)) : ℝ) * (max 1 (2 * Real.exp L ^ (CH * (m : ℝ)))) ^ (2 * r))) ^ (2 * n)) ^ j
      ≤ Real.exp L ^ j * ((Real.exp (L * 6) * (Real.exp (L * (1 / Cl * (2 * ((r:ℝ) * r)))) *
          Real.exp (L * (1 + |CH| * m)) ^ (2 * r))) ^ (2 * n)) ^ j := by
        have hA0 : 0 ≤ 64 * (rd ^ (((2 * (r * r) : ℕ)) : ℝ) * (max 1 (2 * Real.exp L ^ (CH * (m : ℝ)))) ^ (2 * r)) := by
          have hmax0 : 0 ≤ max 1 (2 * Real.exp L ^ (CH * (m : ℝ))) := le_trans zero_le_one (le_max_left _ _)
          positivity
        have hB := pow_le_pow_left₀ (pow_nonneg hA0 _) (pow_le_pow_left₀ hA0 hA (2 * n)) j
        exact mul_le_mul h2j hB (pow_nonneg (pow_nonneg hA0 _) _) (by positivity)
    _ = Real.exp (L * ((j:ℝ) + (6 + 1 / Cl * (2 * ((r:ℝ) * r)) + (1 + |CH| * m) * (2 * r)) * (2 * n * j))) := by
        simp only [← Real.exp_nat_mul, ← Real.exp_add]
        congr 1
        push_cast
        ring
    _ ≤ Real.exp (L * ((17 + 4 * (1 / Cl) + 4 * |CH|) * (m:ℝ) ^ 2 * f * ((17 + 4 * (1 / Cl) + 4 * |CH|) * r))) :=
        Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hexpo hL0.le)
    _ = (Real.exp L ^ (ccOf CH Cl * (m : ℝ) ^ 2 * f)) ^ (ccOf CH Cl * (r : ℝ)) := by
        rw [← Real.rpow_mul (Real.exp_pos L).le, ← Real.exp_mul, hcc]

end G

section H

variable {D : D7}

theorem minorCosetSum_of_latticeIndexHyp_of_tieOK (hNT : KTwoMinorIntegrality.NormLB) (hLS : KTwoMinorIntegrality.LatSum) (hMI : KTwoMinorIntegrality.MinorInt) (large₂ : SizeData₂ D)
    (X : TermTie D) {C' Cl Cg cb Cu cT CT C0 : ℝ} (hH : LatticeIndexAndWeightTheory.Hyp D large₂ C' Cl Cg cb Cu cT CT C0) (CH : ℝ) {u : D.what₂.Word}
    (hT : LatticeIndexAndWeightTheory.TieOK X u) : KappaEndpoints.MinorCosetSum large₂ X u CH (ccOf CH Cl) := by
  obtain ⟨⟨h0, -, -⟩, -⟩ := hH
  obtain ⟨-, -, hmf, -, -, -, -, -, -, -, hrdL, -, -, -, -, -, -, -, hv, -, -, -, -, -, hCl⟩ := h0
  intro j hj T hTm
  have hjI := Finset.mem_Icc.1 hj
  have hrd2 : 2 ≤ D.host.rdE := by unfold Formalism.BasicNotions.Host.v at hv; linarith
  have hm2 := D.R.two_le_m
  have hf1 : 1 ≤ D.R.f := le_trans (Nat.one_le_pow _ _ (by omega)) hmf
  have : Nonempty D.what₂.Tau := Fintype.card_pos_iff.1 (by rw [D.what₂.card_Tau]; omega)
  have hb2 := KappaEndpoints.two_le_scale_b D large₂
  set H1 : ℝ := large₂.sc.b ^ (CH * (D.R.m : ℝ)) with hH1def
  have hH1 : 0 < H1 := Real.rpow_pos_of_pos (by linarith) _
  have hsum := cosets_sum hNT hLS hMI (by linarith) X hT hH1 hjI.2 T hTm
  set B : ℝ := D.host.rdE ^ (((2 * (D.R.rS * D.R.rS) : ℕ)) : ℝ) * (max 1 (2 * H1)) ^ (2 * D.R.rS) with hB
  have hB1 : 1 ≤ B := one_le_mul_of_one_le_of_one_le (Real.one_le_rpow (by linarith) (Nat.cast_nonneg _))
    (one_le_pow₀ (le_max_left _ _))
  have hRl : ∀ l ∈ Finset.Icc 1 j, Rl (D := D) H1 l ≤ B := by
    intro l hl
    have hlr : l ≤ D.R.rS := (Finset.mem_Icc.1 hl).2.trans hjI.2
    have hfe := frameExp_le hlr
    refine max_le hB1 (mul_le_mul ?_ (pow_le_pow_left₀ (by positivity) (le_max_right _ _) _) (by positivity)
      (Real.rpow_nonneg (by linarith) _))
    exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by exact_mod_cast (by omega : 2 * frameExp D.R.rS l ≤ 2 * (D.R.rS * D.R.rS)))
  have hprod : ∏ l ∈ Finset.Icc 1 j, (64 * Rl (D := D) H1 l) ^ (2 * Fintype.card D.what₂.Tau) ≤
      ((64 * B) ^ (2 * Fintype.card D.what₂.Tau)) ^ j := by
    calc ∏ l ∈ Finset.Icc 1 j, (64 * Rl (D := D) H1 l) ^ (2 * Fintype.card D.what₂.Tau)
        ≤ ∏ l ∈ Finset.Icc 1 j, (64 * B) ^ (2 * Fintype.card D.what₂.Tau) :=
          Finset.prod_le_prod (fun l _ => pow_nonneg (by linarith [one_le_Rl (D := D) H1 l]) _)
            (fun l hl => pow_le_pow_left₀ (by linarith [one_le_Rl (D := D) H1 l]) (by linarith [hRl l hl]) _)
      _ = ((64 * B) ^ (2 * Fintype.card D.what₂.Tau)) ^ j := by rw [Finset.prod_const]; simp
  have hfin := final_arith (L := large₂.sc.L) (CH := CH) (rd := D.host.rdE) (r := D.R.rS) (m := D.R.m) (f := D.R.f)
    (n := Fintype.card D.what₂.Tau) (j := j) (KappaEndpoints.one_lt_scale_L D large₂) hCl (by linarith) hrdL (by omega)
    (by have := KappaEndpoints.two_rank_add_two_eq_m D; omega) hjI.2 (by rw [D.what₂.card_Tau]) hf1
  unfold Hb
  calc _ ≤ _ := hsum
    _ ≤ 2 ^ j * ((64 * B) ^ (2 * Fintype.card D.what₂.Tau)) ^ j := mul_le_mul_of_nonneg_left hprod (by positivity)
    _ ≤ _ := hfin

end H

end Formalism.MainNotions.KTwoCosetCount

end
