import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FibreSizeAndRangeBoundStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiPolynomialBoundInDirectionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwiceDifferentiableOfPotential
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FamilyRegularityCauchyEstimate
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedIntegralContinuityEstimate
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical

open Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M

noncomputable section

namespace GlobalTheory.DetLineIntZero

theorem tendsto_log_pow_div_sqrt (n : ℕ) :
    Tendsto (fun R : ℝ => Real.log R ^ n / Real.sqrt R) atTop (𝓝 0) := by
  have h := (isLittleO_log_rpow_rpow_atTop (n : ℝ) (show (0 : ℝ) < 1 / 2 by norm_num)).tendsto_div_nhds_zero
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
  rw [Real.rpow_natCast, Real.sqrt_eq_rpow]

theorem int_sub {e : ℕ} {M : Man e} (K : Calc M) (v : Fin e → K.V) (f g : M.Fun) (hf : M.Smooth f)
    (hg : M.Smooth g) :
    M.int (fun i => K.c1 (v i)) f - M.int (fun i => K.c1 (v i)) g = M.int (fun i => K.c1 (v i)) (f - g) := by
  have hs : M.Smooth (f - g) := fun σ => Cauchy.smooth_sub (hf σ) (hg σ)
  rw [← K.num_ar f hf v, ← K.num_ar g hg v, ← K.num_ar (f - g) hs v]
  have e : K.ar f = K.ar (f - g) + K.ar g := by rw [map_sub]; abel
  rw [e, MultilinearMap.cons_add]
  ring

end GlobalTheory.DetLineIntZero

namespace GlobalTheory.DetLineIntZero

theorem tendsto_int_sub : Hypotheses2 → HypothesesH → OnObj fun D O _ T _ _ => ∀ B : ℝ, 2 ≤ B → ∀ (τ : D.what₂.Tau) c (u : Wt O.Y),
    DomL O.Y.j u → ∀ g : (T.M c).Fun, (T.M c).Smooth g →
      (∀ σ x, x ∉ (T.M c).Z σ → g σ x = (T.F c).ph (fun σ' _ => if σ' = τ then (-1 : ℝ) else 0) σ x) →
      Filter.Tendsto (fun R => (T.M c).int (fun _ => (T.K B c).c1 (T.L B c u + (T.K B c).ar ((T.F c).phR R u)))
          ((T.F c).phR R (fun σ' _ => if σ' = τ then (-1 : ℝ) else 0)) -
        (T.M c).int (fun _ => (T.K B c).c1 (T.L B c u + (T.K B c).ar ((T.F c).phR R u))) g) Filter.atTop (nhds 0) := by
  intro hP hH D O hC hf A T H h B hB τ c u hu g hg hgph
  have hSR := GlobalTheory.T.fibre_size_and_range_bound hP hH D O hC hf A T H h
  have hQP := GlobalTheory.T.quasi_polynomial_bound_in_direction hP hH D O hC hf A T H h
  have hF : (T.F c).FamR O.Y.j :=
    GlobalTheory.Mean4O.InterpFam.famR_of_inR D O.Y T c (fun σ => ((hQP c) σ).1) (hSR c).1 (hSR c).2
  set eτ : Wt O.Y := fun σ' _ => if σ' = τ then (-1 : ℝ) else 0 with heτ
  have hdom : DomL O.Y.j eτ := fun _ _ _ _ _ => le_rfl
  obtain ⟨K, hK⟩ := hF (max ‖u‖ ‖eτ‖)
  have hKu := fun R (hR : Real.exp 2 ≤ R) σ => hK u hu (le_max_left _ _) 0 ⟨le_rfl, zero_le_one⟩ R hR σ
  have hKe := fun R (hR : Real.exp 2 ≤ R) σ => hK eτ hdom (le_max_right _ _) 0 ⟨le_rfl, zero_le_one⟩ R hR σ
  have hK0 : 0 ≤ K := by
    obtain ⟨-, ⟨-, _, _, h1, -⟩, -⟩ := hKu _ le_rfl 0
    exact (abs_nonneg _).trans (h1 0).2
  choose Mg hMg using fun σ =>
    (isCompact_univ (X := (T.M c).X σ)).exists_bound_of_continuousOn
      (GlobalTheory.Mean4O.Cauchy.continuous_of_smooth (hg σ)).continuousOn
  choose C hC using fun σ => GlobalTheory.T.mixed_integral_tail_bound_exists _ _ ((T.M c).A σ) ((T.M c).Z σ) ((T.M c).r σ) ((T.M c).Om σ)
    ((T.M c).bd σ) K
  set e := Formalism.MainNotions.WeightThresholdDefs.dimY O.Y
  let Kt : Fin ((T.M c).n + 1) → ℝ := fun σ => K + |Mg σ|
  have hKt0 : ∀ σ, 0 ≤ Kt σ := fun σ => add_nonneg hK0 (abs_nonneg _)
  let q : ℝ → ℝ := fun R => Real.log R ^ (e + 1) / Real.sqrt R
  let G : ℝ := (T.M c).κ * ∑ σ, (3 * K) ^ e * (4 * Kt σ * |C σ|)
  have hc : ∀ R, Real.exp 2 ≤ R → ∀ σ, Comb ((T.M c).A σ) ((T.M c).Z σ) ((T.M c).r σ) ((T.M c).Om σ) K
      ((T.K B c).c1 (T.L B c u + (T.K B c).ar ((T.F c).phR R u)) σ) := fun R hR σ => by
    have e0 : T.L B c u + (0 : ℝ) • T.a B c + (T.K B c).ar ((T.F c).phR R u) =
        T.L B c u + (T.K B c).ar ((T.F c).phR R u) := by rw [zero_smul, add_zero]
    have l := GlobalTheory.Mean4O.Cauchy.first_chern_form_levi_sum (T.K B c) (T.L B c u) (T.a B c) 0 ((T.F c).phR R u)
      (fun σ => (hKu R hR σ).1) σ (T.th_pot c u σ) (T.a_pot c σ) (T.c1_L B c u σ) (T.firstChern_leviEq_constant B c σ)
    rw [e0] at l
    exact GlobalTheory.Mean4O.Cauchy.comb_of_leviEq ((T.K B c).firstChern_isPotential _ σ) l (hKu R hR σ).2.1
  have bound : ∀ R, Real.exp 2 ≤ R →
      |(T.M c).int (fun _ => (T.K B c).c1 (T.L B c u + (T.K B c).ar ((T.F c).phR R u))) ((T.F c).phR R eτ) -
        (T.M c).int (fun _ => (T.K B c).c1 (T.L B c u + (T.K B c).ar ((T.F c).phR R u))) g| ≤ G * q R := by
    intro R hR
    have h0 : 0 < R := lt_of_lt_of_le (Real.exp_pos _) hR
    have hsq : Real.exp 1 ≤ Real.sqrt R := by
      refine Real.le_sqrt_of_sq_le ?_
      rw [← Real.exp_nat_mul]; simpa using hR
    have hsm : (T.M c).Smooth ((T.F c).phR R eτ) := fun σ => (hKe R hR σ).1
    rw [int_sub (T.K B c) (fun _ => T.L B c u + (T.K B c).ar ((T.F c).phR R u)) _ g hsm hg, Man.int, abs_mul,
      abs_of_pos (T.M c).κ_pos]
    have key : ∀ σ, |mInt ((T.M c).A σ) (fun _ => (T.K B c).c1 (T.L B c u + (T.K B c).ar ((T.F c).phR R u)) σ)
        (((T.F c).phR R eτ - g) σ)| ≤ (3 * K) ^ e * (4 * Kt σ * |C σ|) * q R := by
      intro σ
      have hb := GlobalTheory.Mean4O.CombInt.abs_mInt_comb_le _ _ _ _ _ _ ((T.M c).bd σ) K (C σ) hK0 (hC σ)
        (fun _ => (T.K B c).c1 (T.L B c u + (T.K B c).ar ((T.F c).phR R u)) σ) (((T.F c).phR R eτ - g) σ)
        (2 * Kt σ / R) (2 * Kt σ) (Real.sqrt R) (fun _ => hc R hR σ)
        (GlobalTheory.Mean4O.Cauchy.continuous_of_smooth (GlobalTheory.Mean4O.Cauchy.smooth_sub (hsm σ) (hg σ)))
        (by have := hKt0 σ; positivity) (by have := hKt0 σ; positivity) hsq
        (fun x hx hr => by
          have a1 := ((hKe R hR σ).2.2 x hx).2 hr
          have a2 : K / R ≤ 2 * Kt σ / R := by
            apply div_le_div_of_nonneg_right _ h0.le
            have := abs_nonneg (Mg σ); simp only [Kt]; linarith
          rw [Pi.sub_apply, Pi.sub_apply, hgph σ x hx]
          exact a1.trans a2)
        (fun x hx _ => by
          have a1 := ((hKe R hR σ).2.2 x hx).1
          have a2 := hMg σ x (Set.mem_univ _)
          have hr1 : Real.exp 1 ≤ (T.M c).r σ x := ((T.M c).bd σ).2.2.2.2.2.1 x hx
          have hl : 1 ≤ Real.log ((T.M c).r σ x) := by
            rw [Real.le_log_iff_exp_le (lt_of_lt_of_le (Real.exp_pos _) hr1)]; exact hr1
          rw [Real.norm_eq_abs] at a2
          have a3 : |Mg σ| * 1 ≤ |Mg σ| * Real.log ((T.M c).r σ x) :=
            mul_le_mul_of_nonneg_left hl (abs_nonneg _)
          have a4 : Mg σ ≤ |Mg σ| := le_abs_self _
          have a5 : K * Real.log ((T.M c).r σ x) ≥ 0 := mul_nonneg hK0 (by linarith)
          rw [Pi.sub_apply, Pi.sub_apply]
          calc |(T.F c).phR R eτ σ x - g σ x| ≤ |(T.F c).phR R eτ σ x| + |g σ x| := abs_sub _ _
            _ ≤ K * Real.log ((T.M c).r σ x) + |Mg σ| * Real.log ((T.M c).r σ x) := by linarith
            _ ≤ 2 * Kt σ * Real.log ((T.M c).r σ x) := by
                simp only [Kt]; nlinarith [abs_nonneg (Mg σ)])
      refine hb.trans ?_
      exact (mul_le_mul_of_nonneg_left (GlobalTheory.Mean4O.Cauchy.rate_le (C := C σ) e (hKt0 σ) hR)
        (pow_nonneg (show 0 ≤ 3 * K by linarith) e)).trans_eq (by simp only [q]; ring)
    calc (T.M c).κ * |∑ σ, mInt ((T.M c).A σ) (fun _ => (T.K B c).c1 (T.L B c u + (T.K B c).ar ((T.F c).phR R u)) σ)
          (((T.F c).phR R eτ - g) σ)|
        ≤ (T.M c).κ * ∑ σ, (3 * K) ^ e * (4 * Kt σ * |C σ|) * q R :=
          mul_le_mul_of_nonneg_left ((Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun σ _ => key σ))
            (T.M c).κ_pos.le
      _ = G * q R := by simp only [G, ← Finset.sum_mul]; ring
  have hlim : Tendsto (fun R => G * q R) atTop (𝓝 0) := by
    simpa using (tendsto_log_pow_div_sqrt (e + 1)).const_mul G
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [eventually_ge_atTop (Real.exp 2)] with R hR
  rw [Real.norm_eq_abs]
  exact bound R hR

end GlobalTheory.DetLineIntZero
