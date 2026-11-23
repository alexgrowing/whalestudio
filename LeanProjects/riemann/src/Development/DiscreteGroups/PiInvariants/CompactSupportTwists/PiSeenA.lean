import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.PiVecExHolds

set_option linter.all false

noncomputable section

open NumberField Matrix MeasureTheory Filter Set
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.Desc
open scoped ENNReal

namespace DiscreteGroups.T1.G.Dcy

attribute [local instance] borelH

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

def chi (N : ℕ) (s : ℝ) : ℝ := max 0 (min 1 ((N : ℝ) + 1 - |s|))

theorem continuous_chi (N : ℕ) : Continuous (chi N) :=
  continuous_const.max (continuous_const.min (continuous_const.sub continuous_abs))

theorem chi_nonneg (N : ℕ) (s : ℝ) : 0 ≤ chi N s := le_max_left _ _

theorem chi_le_one (N : ℕ) (s : ℝ) : chi N s ≤ 1 := max_le zero_le_one (min_le_left _ _)

theorem chi_eq_zero {N : ℕ} {s : ℝ} (h : (N : ℝ) + 1 ≤ |s|) : chi N s = 0 :=
  max_eq_left (min_le_of_right_le (by linarith))

theorem chi_eq_one {N : ℕ} {s : ℝ} (h : |s| ≤ N) : chi N s = 1 := by
  unfold chi
  rw [min_eq_left (by linarith), max_eq_right zero_le_one]

theorem hasCompactSupport_chi_pow (N k : ℕ) : HasCompactSupport fun s : ℝ => chi N s * s ^ k :=
  HasCompactSupport.intro (isCompact_closedBall (0 : ℝ) ((N : ℝ) + 1)) fun s hs => by
    rw [Metric.mem_closedBall, Real.dist_eq, sub_zero, not_le] at hs
    rw [chi_eq_zero hs.le, zero_mul]

theorem countable_GL' (m : ℕ) : Countable (GL (Fin m) E) := by
  have : Countable E := (Module.finBasis ℚ E).equivFun.injective.countable
  have : Countable (Matrix (Fin m) (Fin m) E) := inferInstanceAs (Countable (Fin m → Fin m → E))
  exact Function.Injective.countable (f := (Units.val : GL (Fin m) E → Matrix (Fin m) (Fin m) E)) fun a b hab => Units.ext hab

theorem countable_ratH' : Countable (ratH E n 0) := by
  have := countable_GL' (E := E) n
  have := countable_GL' (E := E) 0
  show Countable ((ratGL E n).prodMap (ratGL E 0)).range
  exact (MonoidHom.rangeRestrict_surjective ((ratGL E n).prodMap (ratGL E 0))).countable

theorem bdd_of_mem {π : CuspSub E n} (hθ : ThetaFix π) {ψ : Sm E n} (hψ : ψ ∈ π.V) (R : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : H E n 0, |ldet x| ≤ R → ‖ψ.1 x.1‖ ≤ C := by
  obtain ⟨C, hC⟩ := cp_decay_wt ψ (π.cusp ψ hψ) (hθ.1 ψ hψ) R 0
  refine ⟨max C 0, le_max_right _ _, fun x hx => ?_⟩
  have := hC x hx
  rw [pow_zero, mul_one] at this
  exact this.trans (le_max_left _ _)

theorem integrable_of_ldet (hn : 1 ≤ n) (D : Dom E n 0) (F : H E n 0 → ℂ) (hF : Continuous F) (R K : ℝ)
    (h0 : ∀ x, R < |ldet x| → F x = 0) (hK : ∀ x, |ldet x| ≤ R → ‖F x‖ ≤ K) : Integrable F D.ν := by
  haveI : BorelSpace (H E n 0) := ⟨rfl⟩
  set S : Set (H E n 0) := {x | |ldet x| ≤ R} with hSdef
  have hSm : MeasurableSet S :=
    (isClosed_le (continuous_abs.comp (continuous_ldet (E := E) (n := n))) continuous_const).measurableSet
  have hS : D.ν S < ⊤ := CP.cp_vol hn D R
  have hind : S.indicator F = F := by
    funext x
    by_cases hx : x ∈ S
    · rw [Set.indicator_of_mem hx]
    · rw [Set.indicator_of_notMem hx, h0 x (lt_of_not_ge hx)]
  rw [← hind, integrable_indicator_iff hSm]
  exact Measure.integrableOn_of_bounded (M := K) hS.ne hF.aestronglyMeasurable
    ((ae_restrict_iff' hSm).2 (Eventually.of_forall fun x hx => hK x hx))

theorem integrable_pair (hn : 1 ≤ n) (D : Dom E n 0) {π : CuspSub E n} (hθ : ThetaFix π) {ψ φ : Sm E n}
    (hψ : ψ ∈ π.V) (hφ : φ ∈ π.V) (U V : ℝ → ℂ) (hU : Continuous U) (hV : Continuous V) (R : ℝ)
    (hUs : ∀ s, R < |s| → U s = 0) :
    Integrable (fun x : H E n 0 => starRingEnd ℂ (ψ.1 x.1 * U (ldet x)) * (φ.1 x.1 * V (ldet x))) D.ν := by
  obtain ⟨Cψ, hCψ0, hCψ⟩ := bdd_of_mem hθ hψ R
  obtain ⟨Cφ, hCφ0, hCφ⟩ := bdd_of_mem hθ hφ R
  obtain ⟨KU, hKU⟩ := (isCompact_Icc : IsCompact (Icc (-R) R)).exists_bound_of_continuousOn hU.continuousOn
  obtain ⟨KV, hKV⟩ := (isCompact_Icc : IsCompact (Icc (-R) R)).exists_bound_of_continuousOn hV.continuousOn
  have hc : Continuous fun x : H E n 0 => starRingEnd ℂ (ψ.1 x.1 * U (ldet x)) * (φ.1 x.1 * V (ldet x)) := by
    have h1 := (continuous_of_mem π hψ).comp (continuous_fst (X := GA E n) (Y := GA E 0))
    have h2 := (continuous_of_mem π hφ).comp (continuous_fst (X := GA E n) (Y := GA E 0))
    have hl := continuous_ldet (E := E) (n := n)
    exact (continuous_star.comp (h1.mul (hU.comp hl))).mul (h2.mul (hV.comp hl))
  refine integrable_of_ldet hn D _ hc R (Cψ * KU * (Cφ * KV)) (fun x hx => by simp [hUs _ hx]) fun x hx => ?_
  have hI : ldet x ∈ Icc (-R) R := abs_le.1 hx
  have hKU0 : 0 ≤ KU := (norm_nonneg _).trans (hKU _ hI)
  rw [norm_mul, RCLike.norm_conj, norm_mul, norm_mul]
  exact mul_le_mul (mul_le_mul (hCψ x hx) (hKU _ hI) (norm_nonneg _) hCψ0)
    (mul_le_mul (hCφ x hx) (hKV _ hI) (norm_nonneg _) hCφ0) (by positivity) (by positivity)

end DiscreteGroups.T1.G.Dcy

end
