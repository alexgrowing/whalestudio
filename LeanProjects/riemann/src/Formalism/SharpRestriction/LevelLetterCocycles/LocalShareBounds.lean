import Formalism.SharpRestriction.LevelLetterCocycles.StatementFamilies.ArithmeticCylinders

noncomputable section

namespace Formalism.MainNotions.N.LocalShareBounds

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ArithmeticCylinders Polynomial Filter Topology

variable {D : D7}

theorem wtOf_off (k : Fin 2) (a : MonoidAlgebra ℂ (GL (Fin D.R.r) (ZMod (D.host.g k))))
    (f : (ZMod (D.host.g k))[X])
    (hf : ¬ (f.Monic ∧ f.natDegree = D.R.r ∧ f.coeff 0 ≠ 0)) : wtOf D k a f = 0 := by
  unfold wtOf
  rw [D.ntypes.eSer_zero k f hf, mul_zero]
  simp

theorem sum_wtOf_le_one (k : Fin 2) (a : MonoidAlgebra ℂ (GL (Fin D.R.r) (ZMod (D.host.g k))))
    (S0 : Finset (ZMod (D.host.g k))[X]) (hS0 : ∑ f ∈ S0, D.ntypes.eSer k f = 1) :
    ∑ f ∈ S0, wtOf D k a f ≤ 1 := by
  have hsum : ∀ T : Finset (ZMod (D.host.g k))[X], ∑ f ∈ T, ((a * D.ntypes.eSer k f).coeff 1).re =
      ((a * ∑ f ∈ T, D.ntypes.eSer k f).coeff 1).re := by
    intro T
    classical
    induction T using Finset.induction_on with
    | empty => simp
    | insert f T hf ih =>
      rw [Finset.sum_insert hf, Finset.sum_insert hf, ih, mul_add]
      simp
  unfold wtOf
  rw [← Finset.sum_div, hsum, hS0, mul_one]
  exact div_self_le_one _

theorem locShare_le_one (eV : VecAt D) (CL : ℝ) (hL : lawL D eV CL) (k : Fin 2) (S : Finset (Tup D k)) :
    locShare D eV k S ≤ 1 := by
  classical
  obtain ⟨L0, hL0, hsum0⟩ := D.ntypes.eSer_sum k
  have hw0 : ∀ v f, 0 ≤ wtOf D k (eV k v) f := fun v f => (hL k v).1 f
  have hfilt : ∑ t ∈ S.filter (fun t => ∀ v, t v ∈ L0), ∏ v, wtOf D k (eV k v) (t v) =
      ∑ t ∈ S, ∏ v, wtOf D k (eV k v) (t v) := by
    apply Finset.sum_filter_of_ne
    intro t _ ht v
    by_contra hv
    apply ht
    apply Finset.prod_eq_zero (Finset.mem_univ v)
    exact wtOf_off k _ _ (fun h => hv ((hL0 _).2 h))
  calc locShare D eV k S = ∑ t ∈ S.filter (fun t => ∀ v, t v ∈ L0), ∏ v, wtOf D k (eV k v) (t v) := by
        unfold locShare; exact hfilt.symm
    _ ≤ ∑ t ∈ Fintype.piFinset (fun _ : D.nd.PlG k => L0), ∏ v, wtOf D k (eV k v) (t v) :=
        Finset.sum_le_sum_of_subset_of_nonneg
          (fun t ht => Fintype.mem_piFinset.2 (Finset.mem_filter.1 ht).2)
          (fun t _ _ => Finset.prod_nonneg fun v _ => hw0 v _)
    _ = ∏ v, ∑ f ∈ L0, wtOf D k (eV k v) f :=
        (Finset.prod_univ_sum (fun _ => L0) (fun v f => wtOf D k (eV k v) f)).symm
    _ ≤ 1 := Finset.prod_le_one (fun v _ => Finset.sum_nonneg fun f _ => hw0 v f)
        (fun v _ => sum_wtOf_le_one k _ L0 hsum0)

def Wk (D : D7) (CL : ℝ) (k : Fin 2) : ℝ :=
  3 * (D.R.f : ℝ) / (D.host.g k : ℝ) +
  23 * (1 + CL * D.R.r / D.host.g k) * D.R.f * Real.log (D.host.g k) * (D.host.g k : ℝ) ^ (-(1 / 2 : ℝ)) +
  2 * (D.R.f : ℝ) * D.R.m * (1 + CL * D.R.r / D.host.g k) *
    (1 / (4 * ((min D.host.q D.host.d : ℕ) : ℝ)) + (1 + Real.log D.R.r) / ((D.host.g k : ℝ) - 1)) +
  (D.R.r : ℝ) / 2 * (7 / 8 * (1 + CL * D.R.r / D.host.g k)) ^ D.R.f +
  ((1 + CL * D.R.r / D.host.g k) * (1 - 1 / (5 * Real.log D.R.r))) ^ D.R.f

def PropW (D : D7) : Prop :=
  ∀ (eV : VecAt D) (CL : ℝ), 0 ≤ CL → lawL D eV CL → TieAdmG D → 100 ≤ D.R.r →
    ∀ k : Fin 2, 2 ^ 12 ≤ D.host.g k →
      ∀ S : Finset (Tup D k), (∀ t ∈ S, ¬ goodAt D k t) → locShare D eV k S ≤ Wk D CL k

theorem ranks_facts (D : D7) : D.R.f ≤ D.R.r ∧ D.R.m ≤ D.R.r ∧ 2 ≤ D.R.f ∧ 6 ≤ D.R.r := by
  have h1 := D.R.m_le_f
  have h2 := D.R.f_le_k
  have h3 := D.R.two_le_m
  have h4 := D.R.m_add_three_le_k
  simp only [Ranks.f, Ranks.r, Ranks.n]
  omega

set_option maxHeartbeats 2000000 in

theorem Wk_le (D : D7) (CL : ℝ) (k : Fin 2) (hCL : 0 ≤ CL) (hr : (100 : ℝ) ≤ D.R.r)
    (hg : (2 : ℝ) ^ 12 ≤ D.host.g k) (hCLg : CL * (D.R.r : ℝ) ^ 2 ≤ D.host.g k) :
    Wk D CL k ≤ 65 * br2 D (1 / 5) 0 := by
  have hrf := ranks_facts D
  have hf_le : (D.R.f : ℝ) ≤ D.R.r := by exact_mod_cast hrf.1
  have hm_le : (D.R.m : ℝ) ≤ D.R.r := by exact_mod_cast hrf.2.1
  have hlogs : ∀ i : Fin 2, 0 ≤ Real.log (D.host.g i) := fun i =>
    Real.log_nonneg (by exact_mod_cast (D.host.g_prime i).one_lt.le)
  unfold Wk br2
  have hB1 : (D.R.f : ℝ) * (D.R.r : ℝ) ^ 5 * Real.log (D.host.g k) * (D.host.g k : ℝ) ^ (-(1 / 2 : ℝ)) ≤
      ∑ i : Fin 2, (D.R.f : ℝ) * (D.R.r : ℝ) ^ 5 * Real.log (D.host.g i) * (D.host.g i : ℝ) ^ (-(1 / 2 : ℝ)) :=
    Finset.single_le_sum (f := fun i : Fin 2 => (D.R.f : ℝ) * (D.R.r : ℝ) ^ 5 * Real.log (D.host.g i) *
      (D.host.g i : ℝ) ^ (-(1 / 2 : ℝ))) (fun i _ => by have := hlogs i; positivity) (Finset.mem_univ k)
  set r : ℝ := (D.R.r : ℝ) with hr_def
  set f : ℝ := (D.R.f : ℝ) with hf_def
  set m : ℝ := (D.R.m : ℝ) with hm_def
  set g : ℝ := (D.host.g k : ℝ) with hg_def
  set μ : ℝ := ((min D.host.q D.host.d : ℕ) : ℝ) with hμ_def
  have hf0 : 0 ≤ f := by positivity
  have hm0 : 0 ≤ m := by positivity
  have hμ0 : 0 ≤ μ := by positivity
  have he1 := Real.exp_one_lt_d9
  have he3 : Real.exp 1 ≤ 3 := by linarith
  have hg0 : 0 < g := by linarith
  have hg1 : 1 ≤ g := by linarith
  have hL8 : 1 ≤ Real.log g := by
    rw [Real.le_log_iff_exp_le hg0]
    linarith
  set s : ℝ := g ^ (-(1 / 2 : ℝ)) with hs
  have hs0 : 0 < s := Real.rpow_pos_of_pos hg0 _
  have hsg : 1 / g ≤ s := by
    rw [hs, one_div, ← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_le hg1 (by norm_num)
  have hlr : 1 ≤ Real.log r := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    linarith
  have hlr_le : Real.log r ≤ r := (Real.log_le_sub_one_of_pos (by linarith)).trans (by linarith)
  have hr5 : (10 : ℝ) ^ 10 ≤ r ^ 5 := by
    have := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 100) hr 5
    norm_num at this ⊢
    linarith
  have hr3 : (10 : ℝ) ^ 6 ≤ r ^ 3 := by
    have := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 100) hr 3
    norm_num at this ⊢
    linarith
  set u : ℝ := 1 + CL * r / g with hu
  have hcr : CL * r / g ≤ 1 / r := by
    rw [div_le_div_iff₀ hg0 (by linarith)]
    nlinarith
  have hcr0 : 0 ≤ CL * r / g := by positivity
  have hu1 : 1 ≤ u := by linarith
  have hr1 : 1 / r ≤ 1 := by rw [div_le_one (by linarith)]; linarith
  have hu2 : u ≤ 2 := by linarith
  have huf : u ^ D.R.f ≤ Real.exp 1 := by
    calc u ^ D.R.f ≤ (Real.exp (CL * r / g)) ^ D.R.f :=
          pow_le_pow_left₀ (by linarith) (by rw [hu]; linarith [Real.add_one_le_exp (CL * r / g)]) _
      _ = Real.exp (f * (CL * r / g)) := by rw [← Real.exp_nat_mul]
      _ ≤ Real.exp 1 := by
        apply Real.exp_le_exp.2
        have h1 : f * (CL * r / g) ≤ f * (1 / r) := mul_le_mul_of_nonneg_left hcr hf0
        have h2 : f * (1 / r) ≤ 1 := by rw [mul_one_div, div_le_one (by linarith)]; exact hf_le
        linarith
  have hT0 : 0 ≤ f * r ^ 5 * Real.log g * s := by positivity
  have hW1 : 3 * f / g ≤ f * r ^ 5 * Real.log g * s := by
    have h2 : 3 * f * (1 / g) ≤ 3 * f * s := mul_le_mul_of_nonneg_left hsg (by positivity)
    have h3 : (3 : ℝ) ≤ r ^ 5 * Real.log g := by nlinarith
    have h4 : 3 * f * s ≤ f * r ^ 5 * Real.log g * s := by
      calc 3 * f * s = 3 * (f * s) := by ring
        _ ≤ (r ^ 5 * Real.log g) * (f * s) := mul_le_mul_of_nonneg_right h3 (by positivity)
        _ = f * r ^ 5 * Real.log g * s := by ring
    have h1 : 3 * f / g = 3 * f * (1 / g) := by ring
    linarith
  have hW2 : 23 * u * f * Real.log g * s ≤ f * r ^ 5 * Real.log g * s := by
    have hB : 0 ≤ f * Real.log g * s := by positivity
    have h46 : 23 * u ≤ r ^ 5 := by nlinarith
    calc 23 * u * f * Real.log g * s = (23 * u) * (f * Real.log g * s) := by ring
      _ ≤ r ^ 5 * (f * Real.log g * s) := mul_le_mul_of_nonneg_right h46 hB
      _ = f * r ^ 5 * Real.log g * s := by ring
  have hW3a : 2 * f * m * u * (1 / (4 * μ)) ≤ f * m / μ := by
    have hfm : 0 ≤ f * m / μ := by positivity
    calc 2 * f * m * u * (1 / (4 * μ)) = (u / 2) * (f * m / μ) := by ring
      _ ≤ 1 * (f * m / μ) := mul_le_mul_of_nonneg_right (by linarith) hfm
      _ = f * m / μ := one_mul _
  have hg1' : 0 < g - 1 := by linarith
  have hW3b : 2 * f * m * u * ((1 + Real.log r) / (g - 1)) ≤ f * r ^ 5 * Real.log g * s := by
    have h3 : 0 ≤ 1 + Real.log r := by linarith
    have hnum : 2 * f * m * u * (1 + Real.log r) ≤ 8 * f * r ^ 2 := by
      have h1 : m * u ≤ r * 2 := mul_le_mul hm_le hu2 (by linarith) (by linarith)
      have h2 : 1 + Real.log r ≤ 2 * r := by linarith
      calc 2 * f * m * u * (1 + Real.log r) = (2 * f) * (m * u) * (1 + Real.log r) := by ring
        _ ≤ (2 * f) * (r * 2) * (1 + Real.log r) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 (by positivity)) h3
        _ ≤ (2 * f) * (r * 2) * (2 * r) := mul_le_mul_of_nonneg_left h2 (by nlinarith)
        _ = 8 * f * r ^ 2 := by ring
    have hden : 1 / (g - 1) ≤ 2 * s := by
      have h1 : 1 / (g - 1) ≤ 2 / g := by rw [div_le_div_iff₀ hg1' hg0]; linarith
      have h2 : 2 / g = 2 * (1 / g) := by ring
      have h3' := mul_le_mul_of_nonneg_left hsg (by norm_num : (0 : ℝ) ≤ 2)
      linarith
    have hr3L : (16 : ℝ) ≤ r ^ 3 * Real.log g := by
      have := mul_le_mul_of_nonneg_left hL8 (by positivity : (0 : ℝ) ≤ r ^ 3)
      linarith
    calc 2 * f * m * u * ((1 + Real.log r) / (g - 1)) = (2 * f * m * u * (1 + Real.log r)) * (1 / (g - 1)) := by ring
      _ ≤ (8 * f * r ^ 2) * (2 * s) := mul_le_mul hnum hden (div_nonneg zero_le_one hg1'.le) (by positivity)
      _ = 16 * (f * r ^ 2 * s) := by ring
      _ ≤ (r ^ 3 * Real.log g) * (f * r ^ 2 * s) := mul_le_mul_of_nonneg_right hr3L (by positivity)
      _ = f * r ^ 5 * Real.log g * s := by ring
  have hW3 : 2 * f * m * u * (1 / (4 * μ) + (1 + Real.log r) / (g - 1)) ≤
      f * m / μ + f * r ^ 5 * Real.log g * s := by
    rw [mul_add]
    linarith
  have hW4 : r / 2 * (7 / 8 * u) ^ D.R.f ≤ 3 / 2 * (r * (7 / 8 + 0) ^ D.R.f) := by
    rw [mul_pow, add_zero]
    have h78 : (0 : ℝ) ≤ (7 / 8) ^ D.R.f := by positivity
    have h1 : (7 / 8 : ℝ) ^ D.R.f * u ^ D.R.f ≤ (7 / 8) ^ D.R.f * 3 :=
      mul_le_mul_of_nonneg_left (huf.trans he3) h78
    calc r / 2 * ((7 / 8) ^ D.R.f * u ^ D.R.f) ≤ r / 2 * ((7 / 8) ^ D.R.f * 3) :=
          mul_le_mul_of_nonneg_left h1 (by linarith)
      _ = 3 / 2 * (r * (7 / 8) ^ D.R.f) := by ring
  have hx0 : 0 ≤ 1 - 1 / (5 * Real.log r) := by
    have : 1 / (5 * Real.log r) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
    linarith
  have hpow : (1 - 1 / (5 * Real.log r)) ^ D.R.f ≤ Real.exp (-(1 / 5 * f / Real.log r)) := by
    calc (1 - 1 / (5 * Real.log r)) ^ D.R.f ≤ (Real.exp (-(1 / (5 * Real.log r)))) ^ D.R.f :=
          pow_le_pow_left₀ hx0 (by linarith [Real.add_one_le_exp (-(1 / (5 * Real.log r)))]) _
      _ = Real.exp (-(1 / 5 * f / Real.log r)) := by
        rw [← Real.exp_nat_mul]
        congr 1
        ring
  have hW5 : (u * (1 - 1 / (5 * Real.log r))) ^ D.R.f ≤ 3 * Real.exp (-(1 / 5 * f / Real.log r)) := by
    rw [mul_pow]
    have h1 : 0 ≤ (1 - 1 / (5 * Real.log r)) ^ D.R.f := pow_nonneg hx0 _
    calc u ^ D.R.f * (1 - 1 / (5 * Real.log r)) ^ D.R.f ≤ 3 * (1 - 1 / (5 * Real.log r)) ^ D.R.f :=
          mul_le_mul_of_nonneg_right (huf.trans he3) h1
      _ ≤ 3 * Real.exp (-(1 / 5 * f / Real.log r)) := mul_le_mul_of_nonneg_left hpow (by norm_num)
  have hB2 : 0 ≤ f * m / μ := by positivity
  have hB3 : 0 ≤ r * (7 / 8 + 0) ^ D.R.f := by positivity
  have hB4 : 0 < Real.exp (-(1 / 5 * f / Real.log r)) := Real.exp_pos _
  linarith

theorem provedLocal_of_law (hW : PropW D) {eV : VecAt D} {CL : ℝ} (hCL : 0 ≤ CL) (hL : lawL D eV CL)
    (hA : TieAdmG D) (hr : ∀ k, (D.R.r : ℝ) ^ 2 ≤ 1 / ((CL + 1) * 2 ^ 12) * D.host.g k) :
    LocalShareBound D eV (10 ^ 10) (1 / 5) 0 := by
  have hlogs : ∀ i : Fin 2, 0 ≤ Real.log (D.host.g i) := fun i =>
    Real.log_nonneg (by exact_mod_cast (D.host.g_prime i).one_lt.le)
  have hbr : ∀ c : ℝ, Real.exp (-(c * D.R.f / Real.log D.R.r)) ≤ br2 D c 0 := by
    intro c
    unfold br2
    have h1 : 0 ≤ ∑ i : Fin 2, (D.R.f : ℝ) * (D.R.r : ℝ) ^ 5 * Real.log (D.host.g i) *
        (D.host.g i : ℝ) ^ (-(1 / 2 : ℝ)) := Finset.sum_nonneg fun i _ => by have := hlogs i; positivity
    have h2 : (0 : ℝ) ≤ (D.R.f : ℝ) * D.R.m / ((min D.host.q D.host.d : ℕ) : ℝ) := by positivity
    have h3 : (0 : ℝ) ≤ (D.R.r : ℝ) * (7 / 8 + 0) ^ D.R.f := by positivity
    linarith
  have hb0 : 0 ≤ br2 D (1 / 5) 0 := le_trans (Real.exp_pos _).le (hbr (1 / 5))
  intro k S hS
  by_cases hr100 : (100 : ℝ) ≤ D.R.r
  · have hpos : (0 : ℝ) < (CL + 1) * 2 ^ 12 := by positivity
    have h := hr k
    have hg' : (D.R.r : ℝ) ^ 2 * ((CL + 1) * 2 ^ 12) ≤ D.host.g k := by
      rw [one_div, inv_mul_eq_div, le_div_iff₀ hpos] at h
      exact h
    have hr2 : (1 : ℝ) ≤ (D.R.r : ℝ) ^ 2 := by nlinarith
    have hg12 : (2 : ℝ) ^ 12 ≤ D.host.g k := by nlinarith
    have hCLg : CL * (D.R.r : ℝ) ^ 2 ≤ D.host.g k := by nlinarith
    have h100 : 100 ≤ D.R.r := by exact_mod_cast hr100
    have hg12n : 2 ^ 12 ≤ D.host.g k := by exact_mod_cast hg12
    have h1 := hW eV CL hCL hL hA h100 k hg12n S hS
    have h2 := Wk_le D CL k hCL hr100 hg12 hCLg
    linarith
  · push_neg at hr100
    have hrf := ranks_facts D
    have hr6 : (6 : ℝ) ≤ D.R.r := by exact_mod_cast hrf.2.2.2
    have hf : (D.R.f : ℝ) ≤ D.R.r := by exact_mod_cast hrf.1
    have he1 := Real.exp_one_lt_d9
    have hlogr : 1 ≤ Real.log D.R.r := by
      rw [Real.le_log_iff_exp_le (by linarith)]
      linarith
    have hq : 1 / 5 * (D.R.f : ℝ) / Real.log D.R.r ≤ 20 := by
      rw [div_le_iff₀ (by linarith)]
      nlinarith
    have he : Real.exp (-20) ≤ Real.exp (-(1 / 5 * (D.R.f : ℝ) / Real.log D.R.r)) := Real.exp_le_exp.2 (by linarith)
    have he20 : 1 ≤ (10 : ℝ) ^ 10 * Real.exp (-20) := by
      rw [Real.exp_neg, ← div_eq_mul_inv, le_div_iff₀ (Real.exp_pos _), one_mul]
      have h1 : Real.exp 20 = Real.exp 1 ^ 20 := by rw [← Real.exp_nat_mul]; norm_num
      rw [h1]
      calc Real.exp 1 ^ 20 ≤ (2.7182818286 : ℝ) ^ 20 := pow_le_pow_left₀ (Real.exp_pos 1).le he1.le 20
        _ ≤ 10 ^ 10 := by norm_num
    have hb := hbr (1 / 5)
    calc locShare D eV k S ≤ 1 := locShare_le_one eV CL hL k S
      _ ≤ (10 : ℝ) ^ 10 * Real.exp (-20) := he20
      _ ≤ 10 ^ 10 * br2 D (1 / 5) 0 := by nlinarith

end Formalism.MainNotions.N.LocalShareBounds
