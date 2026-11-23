import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceEstimates.SmoothMatrixMaps.TmDSingleMulVec
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceEstimates.GapNeed
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.ReproducingKernels.DecDeriv
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.MeasurePreservingMulRight

noncomputable section

open Matrix MeasureTheory
open scoped ContDiff InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.Lap

open ReciprocityTheory.ChartRestriction.DS

section TMapCalc

variable {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {σ : Mat k r → (H →L[ℂ] H)} {D : Submodule ℂ H}
  {E : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Module.End ℂ D}

theorem tmE_tensV_apply (f : Fin (2 * r + k + 1) → D) (a b c : Fin (2 * r + k + 1)) :
    LemK.tensV E a b f c = E a b (f c) + (if c = a then f b else 0) := by
  by_cases hc : c = a <;> simp [LemK.tensV, LemK.prj, hc]

theorem tmE_coefX_add (x₀ : Mat k r) (w u v : H) (g : Mat k r) :
    coefX σ x₀ w (u + v) g = coefX σ x₀ w u g + coefX σ x₀ w v g := by
  simp [coefX]

theorem tmE_tmap_smooth (x₁ : Fin (2 * r + k + 1) → ℂ) (x₀ : Mat k r) (w : H) (f : Fin (2 * r + k + 1) → H)
    (hsm : ∀ c, Formalism.REAL.SmoothOnG ε (coefX σ x₀ w (f c))) : Formalism.REAL.SmoothOnG ε (tMap ε σ x₁ x₀ w f) := by
  unfold tMap
  exact tmA_sm_sum _ _ fun c _ => Formalism.REAL.smooth_on_group_mul (tmD_cJ_smooth x₁ _) (hsm c)

theorem tmE_eab_tmap (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E) {x₀ : Mat k r}
    (hx₀ : x₀ ∈ UJset ε) (x₁ : Fin (2 * r + k + 1) → ℂ) (w : H) (f : Fin (2 * r + k + 1) → D)
    (hsm : ∀ c, Formalism.REAL.SmoothOnG ε (coefX σ x₀ w ((f c : D) : H))) (a b : Fin (2 * r + k + 1))
    {g : Mat k r} (hg : g ∈ UJset ε) :
    Formalism.REAL.Eab ε a b (tMap ε σ x₁ x₀ w (fun c => ((f c : D) : H))) g =
      tMap ε σ x₁ x₀ w (fun c => ((LemK.tensV E a b f c : D) : H)) g := by
  have hy : x₀⁻¹ * g ∈ UJset ε := tmA_inUJ_mul (tmA_inUJ_inv hx₀) hg
  unfold tMap
  rw [tmA_eab_sum _ _ (fun c _ => Formalism.REAL.smooth_on_group_mul (tmD_cJ_smooth x₁ _) (hsm c)) a b hg]
  rw [Finset.sum_congr rfl (fun c _ => Formalism.REAL.lie_derivative_mul a b (tmD_cJ_smooth x₁ _) (hsm c) hg)]
  have hZ : ∀ c, cJ ε x₁ (Matrix.single a b 1 *ᵥ Pi.single c 1) g =
      if c = b then cJ ε x₁ (Pi.single a 1) g else 0 := by
    intro c; rw [tmD_single_mulVec]; split_ifs <;> simp [tmD_cJ_zero]
  have hT : ∀ c, coefX σ x₀ w ((LemK.tensV E a b f c : D) : H) g =
      coefX σ x₀ w ((E a b (f c) : D) : H) g + if c = a then coefX σ x₀ w ((f b : D) : H) g else 0 := by
    intro c; rw [tmE_tensV_apply]; split_ifs <;> simp [tmE_coefX_add]
  simp only [tmD_eab_cJ x₁ _ a b hg, tmB_eab_coef hσ hD hy, hZ, hT, ite_mul, zero_mul, mul_add, mul_ite,
    mul_zero, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  ring

def tmTw (E : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Module.End ℂ D) :
    List (Fin (2 * r + k + 1) × Fin (2 * r + k + 1)) → (Fin (2 * r + k + 1) → D) → (Fin (2 * r + k + 1) → D)
  | [], f => f
  | p :: w, f => LemK.tensV E p.1 p.2 (tmTw E w f)

theorem tmE_genSub_E {V : Submodule ℂ D} (a b : Fin (2 * r + k + 1)) {v : D} (hv : v ∈ genSub E V) :
    E a b v ∈ genSub E V := by
  unfold genSub at *
  rw [Submodule.mem_sInf] at *
  intro T hT
  exact hT.2 a b v (hv T hT)

theorem tmE_tmTw_mem {V : Submodule ℂ D} (f : Fin (2 * r + k + 1) → D) (hf : ∀ c, f c ∈ genSub E V) :
    ∀ (wd : List (Fin (2 * r + k + 1) × Fin (2 * r + k + 1))) (c : Fin (2 * r + k + 1)),
      tmTw E wd f c ∈ genSub E V
  | [], c => hf c
  | p :: wd, c => by
      simp only [tmTw]
      rw [tmE_tensV_apply]
      refine Submodule.add_mem _ (tmE_genSub_E _ _ (tmE_tmTw_mem f hf wd c)) ?_
      split_ifs
      · exact tmE_tmTw_mem f hf wd p.2
      · exact Submodule.zero_mem _

theorem tmE_eword_tmap (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E) {x₀ : Mat k r}
    (hx₀ : x₀ ∈ UJset ε) (x₁ : Fin (2 * r + k + 1) → ℂ) (w : H) {V : Submodule ℂ D} {a : ℝ}
    (hgood : ∀ m : D, m ∈ genSub E V → TmGood ε σ x₀ w a (m : H))
    (f : Fin (2 * r + k + 1) → D) (hf : ∀ c, f c ∈ genSub E V) :
    ∀ (wd : List (Fin (2 * r + k + 1) × Fin (2 * r + k + 1))) (g : Mat k r), g ∈ UJset ε →
      Formalism.REAL.Eword ε wd (tMap ε σ x₁ x₀ w (fun c => ((f c : D) : H))) g =
        tMap ε σ x₁ x₀ w (fun c => ((tmTw E wd f c : D) : H)) g
  | [], _, _ => rfl
  | p :: wd, g, hg => by
      simp only [Formalism.REAL.Eword, tmTw]
      rw [Formalism.REAL.lie_derivative_congr (h := tMap ε σ x₁ x₀ w (fun c => ((tmTw E wd f c : D) : H))) p.1 p.2
        (fun x hx => tmE_eword_tmap hσ hD hx₀ x₁ w hgood f hf wd x hx) hg]
      exact tmE_eab_tmap hσ hD hx₀ x₁ w (tmTw E wd f)
        (fun c => (hgood _ (tmE_tmTw_mem f hf wd c)).1) p.1 p.2 hg

theorem tmE_tmap_bound {x₀ : Mat k r} (x₁ : Fin (2 * r + k + 1) → ℂ) (w : H) {V : Submodule ℂ D} {a : ℝ}
    (hgood : ∀ m : D, m ∈ genSub E V → TmGood ε σ x₀ w a (m : H))
    (f : Fin (2 * r + k + 1) → D) (hf : ∀ c, f c ∈ genSub E V) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ g ∈ UJset ε, ‖tMap ε σ x₁ x₀ w (fun c => ((f c : D) : H)) g‖ ≤ C * frob g ^ (1 - a) := by
  have hb := fun c => (hgood _ (hf c)).2 []
  choose C hC using hb
  obtain ⟨B, hB0, hBb⟩ : ∃ B : ℝ, 0 ≤ B ∧ ∀ c g, ‖cJ ε x₁ (Pi.single c 1) g‖ ≤ B * frob g :=
    ⟨_, Finset.sum_nonneg fun i _ => norm_nonneg _, fun c g => tmD_cJ_bound x₁ c g⟩
  refine ⟨B * ∑ c, max (C c) 0, mul_nonneg hB0 (Finset.sum_nonneg fun c _ => le_max_right _ _), fun g hg => ?_⟩
  have hF : 1 ≤ frob g := tmA_one_le_frob hg 0
  have hpow : frob g ^ (1 - a) = frob g * frob g ^ (-a) := by
    rw [sub_eq_add_neg, Real.rpow_add (by linarith), Real.rpow_one]
  have hr : 0 ≤ frob g ^ (-a) := Real.rpow_nonneg (by linarith) _
  unfold tMap
  calc ‖∑ c, cJ ε x₁ (Pi.single c 1) g * coefX σ x₀ w ((f c : D) : H) g‖
      ≤ ∑ c, ‖cJ ε x₁ (Pi.single c 1) g‖ * ‖coefX σ x₀ w ((f c : D) : H) g‖ :=
        (norm_sum_le _ _).trans (le_of_eq (by simp))
    _ ≤ ∑ c, (B * frob g) * (max (C c) 0 * frob g ^ (-a)) := by
        refine Finset.sum_le_sum fun c _ => mul_le_mul (hBb c g) ?_ (norm_nonneg _)
          (by positivity)
        exact (hC c g hg).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hr)
    _ = (B * ∑ c, max (C c) 0) * frob g ^ (1 - a) := by
        rw [hpow, Finset.mul_sum, Finset.sum_mul]
        exact Finset.sum_congr rfl fun c _ => by ring

end TMapCalc

section L2

variable {n : ℕ} {ε : Fin n → Bool}

theorem tmF_memLp {F : Matrix (Fin n) (Fin n) ℂ → ℂ} (hF : Formalism.REAL.SmoothOnG ε F) {C a : ℝ}
    (s : Bool) (ha : ((2 * (n * Fintype.card (S7.SgIxV ε s)) : ℕ) : ℝ) < 2 * (a - 1)) (a₀ : Fin n)
    (hb : ∀ g, Formalism.REAL.inUJ ε g → ‖F g‖ ≤ C * frob g ^ (1 - a)) :
    MemLp (fun g : Formalism.REAL.UJ ε => F (Formalism.MainNotions.S.umat g)) 2 (Formalism.REAL.muG ε) := by
  apply memLp_muG_of_haar ε F 2
  intro ν hν
  have hae : AEStronglyMeasurable (fun g : S7.UJ ε => F (S7.toM g)) ν :=
    (Formalism.REAL.continuous_smooth_on_group_eval hF).aestronglyMeasurable
  rw [memLp_two_iff_integrable_sq_norm hae]
  have ha1 : 0 ≤ a - 1 := by
    have : (0 : ℝ) ≤ ((2 * (n * Fintype.card (S7.SgIxV ε s)) : ℕ) : ℝ) := Nat.cast_nonneg _
    linarith
  have hn : (1 : ℝ) ≤ n := by exact_mod_cast a₀.pos
  have key : ∀ g : S7.UJ ε, 1 ≤ S7.hs (S7.toM g) ∧
      ‖‖F (S7.toM g)‖ ^ 2‖ ≤ C ^ 2 * S7.hs (S7.toM g) ^ (1 - a) := by
    intro g
    have hg : Formalism.REAL.inUJ ε (S7.toM g) := g.2
    have h1 := hb _ hg
    have hfr : 1 ≤ frob (S7.toM g) := tmA_one_le_frob hg a₀
    have hsq : frob (S7.toM g) ^ 2 = S7.hs (S7.toM g) := by
      unfold frob S7.hs; exact Real.sq_sqrt (by positivity)
    refine ⟨by rw [← hsq]; nlinarith, ?_⟩
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    calc ‖F (S7.toM g)‖ ^ 2 ≤ (C * frob (S7.toM g) ^ (1 - a)) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) h1 2
      _ = C ^ 2 * S7.hs (S7.toM g) ^ (1 - a) := by
          rw [mul_pow, Real.rpow_pow_comm (by linarith), hsq]
  refine S7.integrable_of_decayVG ε s ν _ (hae.norm.pow 2) (C ^ 2) ?_ (2 * (a - 1)) ha ?_
  · intro g _
    obtain ⟨h1, h2⟩ := key g
    refine h2.trans ?_
    have : S7.hs (S7.toM g) ^ (1 - a) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos h1 (by linarith)
    exact mul_le_of_le_one_right (sq_nonneg C) this
  · intro g _
    obtain ⟨h1, h2⟩ := key g
    have hx : 0 < S7.hs (S7.toM g) / n := div_pos (by linarith) (by linarith)
    refine ⟨Real.log (S7.hs (S7.toM g) / n) / 2, ?_, h2.trans ?_⟩
    · rw [show 2 * (Real.log (S7.hs (S7.toM g) / n) / 2) = Real.log (S7.hs (S7.toM g) / n) by ring,
        Real.exp_log hx, mul_div_cancel₀ _ (by linarith)]
    · apply mul_le_mul_of_nonneg_left _ (sq_nonneg C)
      rw [show -(2 * (a - 1) * (Real.log (S7.hs (S7.toM g) / n) / 2)) =
          Real.log (S7.hs (S7.toM g) / n) * (1 - a) by ring, ← Real.rpow_def_of_pos hx]
      exact Real.rpow_le_rpow_of_nonpos hx (div_le_self (by linarith) hn) (by linarith)

end L2

end ReciprocityTheory.ChartRestriction.DS.Lap
