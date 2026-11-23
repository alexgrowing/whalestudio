import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.FormulaF
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.RregRep
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.IntegrableOfDecayVG
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.ExpInPPosDef

noncomputable section

open Finset Matrix

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ} {ε : Fin n → Bool} {lam : Fin n → ℝ} {T : S7.KType ε (lowK ε lam)}
  {Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)} {v₀ : T.V}

theorem sigZeroDecay_one_le_hs {g : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) (i : Fin n) : 1 ≤ S7.hs g := by
  unfold S7.hs
  have hg' : gᴴ * Jm ε * g = Jm ε := hg
  have h1 : (gᴴ * Jm ε * g) i i = Jm ε i i := by rw [hg']
  rw [Matrix.mul_apply] at h1
  simp only [Jm, Matrix.mul_diagonal, Matrix.conjTranspose_apply, Matrix.diagonal_apply_eq] at h1
  have key : ‖(if ε i = true then (1 : ℂ) else -1)‖ ≤ ∑ x, ‖g x i‖ ^ 2 := by
    rw [← h1]
    refine (norm_sum_le _ _).trans (le_of_eq ?_)
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [norm_mul, norm_mul, norm_star]
    split_ifs <;> simp [sq]
  have hrow : ∑ x, ‖g x i‖ ^ 2 ≤ ∑ a, ∑ b, ‖g a b‖ ^ 2 :=
    Finset.sum_le_sum fun a _ =>
      Finset.single_le_sum (f := fun b => ‖g a b‖ ^ 2) (fun b _ => by positivity) (Finset.mem_univ i)
  have hn : ‖(if ε i = true then (1 : ℂ) else -1)‖ = 1 := by
    split_ifs <;> simp
  linarith

theorem sigZeroDecay_real {h c s N G : ℝ} (hh : 0 < h) (hc : 1 ≤ c) (hN : 0 < N)
    (hG : 0 < G) (hGle : G ≤ N * Real.exp s) :
    Real.exp (-(h / 8) * min (s ^ 2) (s / c)) ≤
      (Real.exp (h / (8 * c)) * N ^ (h / (8 * c))) * G ^ (-(h / (8 * c))) := by
  have hc0 : 0 < c := lt_of_lt_of_le one_pos hc
  have ha : 0 < h / (8 * c) := by positivity
  have hlog : Real.log G ≤ Real.log N + s := by
    have h1 := Real.log_le_log hG hGle
    rwa [Real.log_mul hN.ne' (Real.exp_pos s).ne', Real.log_exp] at h1
  have hcs : c * (s / c) = s := by
    first
      | (field_simp; done)
      | (field_simp; ring)
  have hmin : s - 1 ≤ c * min (s ^ 2) (s / c) := by
    rcases min_cases (s ^ 2) (s / c) with ⟨h1, _⟩ | ⟨h1, _⟩
    · rw [h1]
      nlinarith [mul_le_mul_of_nonneg_right hc (sq_nonneg s), sq_nonneg (s - 1)]
    · rw [h1, hcs]
      linarith
  have hh8 : h / 8 = c * (h / (8 * c)) := by
    first
      | (field_simp; done)
      | (field_simp; ring)
  rw [Real.rpow_def_of_pos hN, Real.rpow_def_of_pos hG, ← Real.exp_add, ← Real.exp_add,
    Real.exp_le_exp, hh8]
  nlinarith [mul_le_mul_of_nonneg_left hmin ha.le, mul_le_mul_of_nonneg_left hlog ha.le]

theorem dec_gN_sigLam (hgap : StdGap ε lam) (hP : IsPsiFor ε lam T Ψ) (hv₀ : v₀ ≠ 0) {h : ℝ} (hq : 1 ≤ S7.q0 ε)
    (hdec : ∀ (k : S7.KG ε) (X : Matrix (Fin n) (Fin n) ℂ), inP ε X →
      ‖Ψ (S7.toMK k * NormedSpace.exp X)‖ ≤
        Real.exp (-(h / 8) * min (S7.hs X) (Real.sqrt (S7.hs X) / Real.sqrt (2 * S7.q0 ε))))
    (v v' : T.V) :
    ∃ C : ℝ, ∀ g ∈ UJset ε,
      ‖inner ℂ (uniformisationL2 ε Ψ v₀ v') (rreg ε g (uniformisationL2 ε Ψ v₀ v))‖ ≤
        C * Real.sqrt (S7.hs g) ^ (-(h / (8 * Real.sqrt (2 * (S7.q0 ε : ℝ))))) := by

  have hqn : S7.q0 ε ≤ n := by
    unfold S7.q0 pOf
    exact (min_le_left _ _).trans ((Finset.card_filter_le _ _).trans_eq (Finset.card_fin n))
  have hn : 0 < n := lt_of_lt_of_le one_pos (hq.trans hqn)
  have hG1 : ∀ g ∈ UJset ε, 1 ≤ Real.sqrt (S7.hs g) := fun g hg =>
    Real.one_le_sqrt.mpr (sigZeroDecay_one_le_hs hg ⟨0, hn⟩)
  set c := Real.sqrt (2 * (S7.q0 ε : ℝ)) with hcdef
  have hc : 1 ≤ c := by
    rw [hcdef, Real.one_le_sqrt]
    have : (1 : ℝ) ≤ S7.q0 ε := by exact_mod_cast hq
    linarith
  rcases le_or_gt h 0 with hh | hh
  ·
    refine ⟨‖uniformisationL2 ε Ψ v₀ v'‖ * ‖uniformisationL2 ε Ψ v₀ v‖, fun g hg => ?_⟩
    have hiso : ‖rreg ε g (uniformisationL2 ε Ψ v₀ v)‖ = ‖uniformisationL2 ε Ψ v₀ v‖ := (rreg_isURepOn ε).2.1 g hg _
    have hpow : 1 ≤ Real.sqrt (S7.hs g) ^ (-(h / (8 * c))) := by
      refine Real.one_le_rpow (hG1 g hg) ?_
      have : h / (8 * c) ≤ 0 :=
        div_nonpos_of_nonpos_of_nonneg hh (by linarith)
      linarith
    calc ‖inner ℂ (uniformisationL2 ε Ψ v₀ v') (rreg ε g (uniformisationL2 ε Ψ v₀ v))‖
        ≤ ‖uniformisationL2 ε Ψ v₀ v'‖ * ‖rreg ε g (uniformisationL2 ε Ψ v₀ v)‖ := norm_inner_le_norm _ _
      _ = ‖uniformisationL2 ε Ψ v₀ v'‖ * ‖uniformisationL2 ε Ψ v₀ v‖ := by rw [hiso]
      _ ≤ ‖uniformisationL2 ε Ψ v₀ v'‖ * ‖uniformisationL2 ε Ψ v₀ v‖ * Real.sqrt (S7.hs g) ^ (-(h / (8 * c))) :=
          le_mul_of_one_le_right (by positivity) hpow
  ·
    refine ⟨‖uniformisationL2 ε Ψ v₀ T.w‖ ^ 2 * ‖v'‖ * ‖v‖ *
      (Real.exp (h / (8 * c)) * Real.sqrt n ^ (h / (8 * c))), fun g hg => ?_⟩
    obtain ⟨k, X, hX, rfl⟩ := S7.polar_exists hg
    have hd := dec_sigLam hgap hP hv₀ hdec k hX v v'
    set s := Real.sqrt (S7.hs X) with hsdef
    have hsX : S7.hs X = s ^ 2 := (Real.sq_sqrt (S7.hs_nonnegVG X)).symm
    have hN : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hn)
    have hGpos : 0 < Real.sqrt (S7.hs (S7.toMK k * NormedSpace.exp X)) :=
      lt_of_lt_of_le one_pos (hG1 _ hg)
    have hGle : Real.sqrt (S7.hs (S7.toMK k * NormedSpace.exp X)) ≤ Real.sqrt n * Real.exp s := by
      rw [S7.hs_kmulVG]
      have h2 : S7.hs (NormedSpace.exp X) ≤ (Real.sqrt n * Real.exp s) ^ 2 := by
        have e2 : Real.exp s ^ 2 = Real.exp (2 * s) := by
          rw [← Real.exp_nat_mul]; norm_num
        have := S7.hs_exp_leVG X
        rw [← hsdef] at this
        rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg n), e2]
        exact this
      calc Real.sqrt (S7.hs (NormedSpace.exp X)) ≤ Real.sqrt ((Real.sqrt n * Real.exp s) ^ 2) :=
            Real.sqrt_le_sqrt h2
        _ = Real.sqrt n * Real.exp s := Real.sqrt_sq (by positivity)
    have hr := sigZeroDecay_real hh hc hN hGpos hGle
    rw [← hsX] at hr
    have hM : 0 ≤ ‖uniformisationL2 ε Ψ v₀ T.w‖ ^ 2 * ‖v'‖ * ‖v‖ := by positivity
    calc _ ≤ ‖uniformisationL2 ε Ψ v₀ T.w‖ ^ 2 * ‖v'‖ * ‖v‖ *
          Real.exp (-(h / 8) * min (S7.hs X) (Real.sqrt (S7.hs X) / Real.sqrt (2 * S7.q0 ε))) := hd
      _ ≤ ‖uniformisationL2 ε Ψ v₀ T.w‖ ^ 2 * ‖v'‖ * ‖v‖ *
          ((Real.exp (h / (8 * c)) * Real.sqrt n ^ (h / (8 * c))) *
            Real.sqrt (S7.hs (S7.toMK k * NormedSpace.exp X)) ^ (-(h / (8 * c)))) :=
          mul_le_mul_of_nonneg_left hr hM
      _ = _ := by ring

end ReciprocityTheory.ChartRestriction.DS
