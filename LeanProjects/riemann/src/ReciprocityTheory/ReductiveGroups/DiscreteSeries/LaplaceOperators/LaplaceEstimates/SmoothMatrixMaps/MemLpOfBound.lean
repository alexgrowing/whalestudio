import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceEstimates.SmoothMatrixMaps.FrobTranslateLe
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceEstimates.GapNeed
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.ReproducingKernels.DecDeriv
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.IntegrVGA
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.MeasurePreservingMulRight

noncomputable section

open Matrix MeasureTheory
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.Lap

open ReciprocityTheory.ChartRestriction.DS

namespace TDAux

variable {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool}

theorem frob_rpow_sq (g : Mat k r) (b : ℝ) : (frob g ^ b) ^ 2 = Formalism.REAL.hs g ^ b := by
  have h0 : 0 ≤ Formalism.REAL.hs g := by unfold Formalism.REAL.hs; positivity
  rw [frob_eq, Real.sqrt_eq_rpow, ← Real.rpow_mul h0, ← Real.rpow_mul_natCast h0]
  congr 1
  push_cast
  ring

theorem memLp_of_bound {F : Mat k r → ℂ} (hs : Formalism.REAL.SmoothOnG ε F) {a C : ℝ}
    (ha : ((2 * r + k + 1 : ℕ) : ℝ) * (S7.q0 ε : ℝ) < a - 1)
    (hb : ∀ g, Formalism.REAL.inUJ ε g → ‖F g‖ ≤ C * frob g ^ (1 - a)) :
    MemLp (fun g : Formalism.REAL.UJ ε => F (Formalism.MainNotions.S.umat g)) 2 (Formalism.REAL.muG ε) := by
  apply memLp_muG_of_haar ε F 2
  intro ν hν
  have hc : Continuous (fun g : S7.UJ ε => F (S7.toM g)) := Formalism.REAL.continuous_smooth_on_group_eval hs
  rw [memLp_two_iff_integrable_sq_norm hc.aestronglyMeasurable]
  obtain ⟨s, hsq⟩ := S7.exists_signVG ε
  have hn1 : (1 : ℝ) ≤ ((2 * r + k + 1 : ℕ) : ℝ) := by exact_mod_cast n_pos
  have hq0 : (0 : ℝ) ≤ (S7.q0 ε : ℝ) := Nat.cast_nonneg _
  have ha1 : 1 - a ≤ 0 := by nlinarith
  set C' := max C 0 with hC'
  have hb' : ∀ g : S7.UJ ε, ‖F (S7.toM g)‖ ^ 2 ≤ C' ^ 2 * Formalism.REAL.hs (S7.toM g) ^ (1 - a) := by
    intro g
    have hg : Formalism.REAL.inUJ ε (S7.toM g) := g.2
    have hF := hb _ hg
    have h1 : ‖F (S7.toM g)‖ ≤ C' * frob (S7.toM g) ^ (1 - a) :=
      hF.trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
        (Real.rpow_nonneg (frob_pos n_pos hg).le _))
    calc ‖F (S7.toM g)‖ ^ 2 ≤ (C' * frob (S7.toM g) ^ (1 - a)) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) h1 2
      _ = C' ^ 2 * Formalism.REAL.hs (S7.toM g) ^ (1 - a) := by rw [mul_pow, frob_rpow_sq]
  have hhs : ∀ g : S7.UJ ε, ((2 * r + k + 1 : ℕ) : ℝ) ≤ Formalism.REAL.hs (S7.toM g) :=
    fun g => Formalism.REAL.dim_le_frobenius (ε := ε) g.2
  have hC2 : 0 ≤ C' ^ 2 := sq_nonneg _
  refine S7.integrable_of_decayVG ε s ν _ (hc.norm.pow 2).aestronglyMeasurable (C' ^ 2) ?_ (2 * (a - 1)) ?_ ?_
  · intro g _
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    refine (hb' g).trans ?_
    calc C' ^ 2 * Formalism.REAL.hs (S7.toM g) ^ (1 - a) ≤ C' ^ 2 * 1 :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_one_of_one_le_of_nonpos (hn1.trans (hhs g)) ha1) hC2
      _ = C' ^ 2 := mul_one _
  · rw [hsq]
    push_cast at ha ⊢
    linarith
  · intro g _
    have hpos : 0 < Formalism.REAL.hs (S7.toM g) := lt_of_lt_of_le one_pos (hn1.trans (hhs g))
    have hnpos : (0 : ℝ) < ((2 * r + k + 1 : ℕ) : ℝ) := lt_of_lt_of_le one_pos hn1
    set t := Real.log (Formalism.REAL.hs (S7.toM g) / ((2 * r + k + 1 : ℕ) : ℝ)) / 2 with ht
    have he : ((2 * r + k + 1 : ℕ) : ℝ) * Real.exp (2 * t) = Formalism.REAL.hs (S7.toM g) := by
      rw [ht, show 2 * (Real.log (Formalism.REAL.hs (S7.toM g) / ((2 * r + k + 1 : ℕ) : ℝ)) / 2) =
        Real.log (Formalism.REAL.hs (S7.toM g) / ((2 * r + k + 1 : ℕ) : ℝ)) by ring,
        Real.exp_log (div_pos hpos hnpos)]
      field_simp
    refine ⟨t, le_of_eq he.symm, ?_⟩
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    refine (hb' g).trans ?_
    rw [← he, Real.mul_rpow hnpos.le (Real.exp_pos _).le, ← Real.exp_mul]
    have hn' : ((2 * r + k + 1 : ℕ) : ℝ) ^ (1 - a) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hn1 ha1
    have e2 : 2 * t * (1 - a) = -(2 * (a - 1) * t) := by ring
    rw [e2]
    calc C' ^ 2 * (((2 * r + k + 1 : ℕ) : ℝ) ^ (1 - a) * Real.exp (-(2 * (a - 1) * t))) ≤
        C' ^ 2 * (1 * Real.exp (-(2 * (a - 1) * t))) := by
          gcongr
      _ = C' ^ 2 * Real.exp (-(2 * (a - 1) * t)) := by rw [one_mul]

end TDAux

namespace TDAux

theorem a_gt {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool} {h : ℝ} (hneed : hNeed ε < h) (hq0 : 1 ≤ S7.q0 ε) :
    8 * ((2 * r + k + 1 : ℕ) : ℝ) * (S7.q0 ε : ℝ) + 1 < aExp ε h := by
  have hq : min ((pOf ε : ℕ) : ℝ) ((qOf ε : ℕ) : ℝ) = (S7.q0 ε : ℝ) := by
    simp only [S7.q0, Nat.cast_min]
  unfold hNeed at hneed
  rw [hq] at hneed
  have h3 := lt_of_le_of_lt ((le_max_right _ _).trans (le_max_right _ _)) hneed
  have hq1 : (1 : ℝ) ≤ (S7.q0 ε : ℝ) := by exact_mod_cast hq0
  have hs : 0 < Real.sqrt (2 * (S7.q0 ε : ℝ)) := Real.sqrt_pos.mpr (by linarith)
  have hn : (0 : ℝ) ≤ ((2 * r + k + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
  have hm : 2 * ((2 * r + k + 1 : ℕ) : ℝ) * (S7.q0 ε : ℝ) ≤
      max (2 * ((2 * r + k + 1 : ℕ) : ℝ) * (S7.q0 ε : ℝ)) (2 * ((qOf ε : ℝ) - 1) * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2) :=
    le_max_left _ _
  unfold aExp
  rw [lt_div_iff₀ (by positivity)]
  nlinarith

end TDAux

theorem tMapD_spec : TMapDStatement := by
  intro k r ε lam h H _ _ _ σ D E V T μ ι hσ hE hV hcas hK hμ hcoef hp hq hgap hHC hGap x₁ x₀ w hx₀ f hf
  obtain ⟨hq0, hneed⟩ := gapNeed k r ε h hp hq hgap
  have hx₀' : Formalism.REAL.inUJ ε x₀ := hx₀
  have hagt := TDAux.a_gt (ε := ε) hneed hq0
  have hn : (0 : ℝ) ≤ ((2 * r + k + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
  have hq0' : (0 : ℝ) ≤ (S7.q0 ε : ℝ) := Nat.cast_nonneg _
  have ha0 : 0 ≤ aExp ε h := by nlinarith
  have ha : ((2 * r + k + 1 : ℕ) : ℝ) * (S7.q0 ε : ℝ) < aExp ε h - 1 := by nlinarith
  have hQ : ∀ m ∈ genSub E V, TDAux.Qp ε σ x₀ ((w : D) : H) (aExp ε h) (m : H) := by
    refine TDAux.Qp_genSub (fun v hv wd => ?_)
    refine TDAux.Qp_word hσ hE hx₀' (ψ := fun y => ⟪ι w, S7.PsiM T μ y (ι ⟨v, hv⟩)⟫_ℂ) ?_
      (TDAux.psi_smooth T μ hμ _ _) ha0 ?_ wd
    · intro y hy
      exact hcoef (x₀⁻¹ * y) (Formalism.REAL.indefinite_unitary_mul_mem ε (TDAux.inv_mem hx₀') hy) ⟨v, hv⟩ w
    · intro wd'
      obtain ⟨C, hC⟩ := S0.DecDeriv.decDeriv _ ε lam h T μ hHC hGap hneed hq0 hμ wd' (ι ⟨v, hv⟩) (ι w)
      exact ⟨C, fun y hy => hC y hy⟩
  have hQf : ∀ wd c, TDAux.Qp ε σ x₀ ((w : D) : H) (aExp ε h) ((TDAux.Fw E wd f c : D) : H) :=
    fun wd c => hQ _ (TDAux.Fw_mem E V hf wd c)
  have hsm := TDAux.tMapD_smooth (σ := σ) x₁ (hQf [])
  refine ⟨⟨hsm, fun wd => ?_⟩, fun a b g hg => TDAux.tMapD_Eab hσ hE hx₀' hg x₁ _ f a b, fun wd => ?_⟩
  · obtain ⟨C, hC⟩ := TDAux.tMapD_bound (σ := σ) x₁ (hQf wd)
    exact TDAux.memLp_of_bound (Formalism.REAL.smooth_iterated_lie_derivative hsm wd) ha (fun g hg => by
      rw [TDAux.tMapD_Eword hσ hE hx₀' x₁ _ f wd g hg]; exact hC g hg)
  · obtain ⟨C, hC⟩ := TDAux.tMapD_bound (σ := σ) x₁ (hQf wd)
    exact ⟨C, fun g hg => by rw [TDAux.tMapD_Eword hσ hE hx₀' x₁ _ f wd g hg]; exact hC g hg⟩

end ReciprocityTheory.ChartRestriction.DS.Lap
