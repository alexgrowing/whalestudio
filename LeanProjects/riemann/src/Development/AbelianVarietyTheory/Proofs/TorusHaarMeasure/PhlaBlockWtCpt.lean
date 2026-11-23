import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpStatementPfH

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory.CurvMargin

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def blockWt {r : ℕ} (X : Data E r) : Wt X.Ψ r := fun _ i => if (i : ℕ) < X.p0 then 0 else 1

theorem tele_tail (L : ℕ → ℝ) (p : ℕ) : ∀ r : ℕ, p ≤ r →
    ∑ i ∈ Finset.range r, (if i < p then (0 : ℝ) else 1) * (L (i + 1) - L i) = L r - L p := by
  intro r hr
  induction r, hr using Nat.le_induction with
  | base =>
    rw [sub_self]
    refine Finset.sum_eq_zero fun i hi => ?_
    rw [if_pos (Finset.mem_range.1 hi), zero_mul]
  | succ n hn ih =>
    rw [Finset.sum_range_succ, ih, if_neg (not_lt.2 hn)]
    ring

theorem phla_blockWt_cpt {r : ℕ} (X : Data E r) (x0 : Frame X.Ψ r) (ho : IsOrth X x0)
    {z : V (nd X)} (hz : z ∈ OmF X x0) :
    phla X (blockWt X) (cpt X x0 z) = rhF X x0 z := by
  rw [IW.phla_eq X hz, rhF, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun τ _ => ?_
  set x := cpt X x0 z
  let L' : ℕ → ℝ := fun k => if h : k < r + 1 then IW.Lm X x τ ⟨k, h⟩ else 0
  have h1 : ∀ i : Fin r, IW.Lm X x τ i.succ = L' (i + 1) := fun i => by
    simp only [L', dif_pos (Nat.succ_lt_succ i.isLt)]; rfl
  have h2 : ∀ i : Fin r, IW.Lm X x τ i.castSucc = L' i := fun i => by
    simp only [L', dif_pos (Nat.lt_succ_of_lt i.isLt)]; rfl
  have hk : ∀ i : Fin r, ((blockWt X τ i : ℤ) : ℝ) = if (i : ℕ) < X.p0 then (0 : ℝ) else 1 :=
    fun i => by unfold blockWt; split_ifs <;> simp
  have hLr : L' r = 0 := by
    simp only [L', dif_pos (Nat.lt_succ_self r)]; exact IW.Lm_last_cpt X x0 ho z τ
  have hLp : L' X.p0 = Real.log ‖dmin X.Gm x τ ⟨X.p0, Nat.lt_succ_of_le X.p0_le⟩‖ := by
    simp only [L', dif_pos (Nat.lt_succ_of_le X.p0_le)]; rfl
  simp_rw [h1, h2, hk]
  rw [Fin.sum_univ_eq_sum_range
    (fun i => (if i < X.p0 then (0 : ℝ) else 1) * (L' (i + 1) - L' i)) r, tele_tail L' X.p0 r X.p0_le,
    hLr, hLp, zero_sub]

theorem leviRh_eq {r : ℕ} (X : Data E r) (x0 : Frame X.Ψ r) (ho : IsOrth X x0)
    {z : V (nd X)} (hz : z ∈ OmF X x0) (ξ : Fin (nd X) → ℂ) :
    leviRh X x0 z ξ = leviM X (phla X (blockWt X)) x0 z ξ := by
  have hev : (fun w => ((rhF X x0 w : ℝ) : ℂ)) =ᶠ[𝓝 z]
      fun w => ((phla X (blockWt X) (cpt X x0 w) : ℝ) : ℂ) := by
    filter_upwards [(ExF.isOpen_OmF X x0).mem_nhds hz] with w hw
    rw [phla_blockWt_cpt X x0 ho hw]
  unfold leviRh leviM
  rw [leviV_congr hev]

theorem coeff_cases (p : ℕ) {a b : ℕ} (h : b < a) (u v : ℝ) :
    (a < p ∧ sgn p a * sgn p b * (v - u) = v - u) ∨
    (p ≤ b ∧ sgn p a * sgn p b * (v - u) = v - u) ∨
    (b < p ∧ p ≤ a ∧ sgn p a * sgn p b * (v - u) = u - v) := by
  unfold sgn
  by_cases ha : a < p
  · left; refine ⟨ha, ?_⟩; rw [if_pos ha, if_pos (h.trans ha)]; ring
  · by_cases hb : b < p
    · right; right; refine ⟨hb, not_lt.1 ha, ?_⟩; rw [if_neg ha, if_pos hb]; ring
    · right; left; refine ⟨not_lt.1 hb, ?_⟩; rw [if_neg ha, if_neg hb]; ring

theorem curv_and_margin :
    (∀ (r : ℕ) (X : Data E r) (la : Wt X.Ψ r) (x : Frame X.Ψ r), IsOrth X x → ∀ ξ : Fin (nd X) → ℂ, leviM X (phla X la) x 0 ξ = ∑ e : Ent X, sgn X.p0 e.2.1.1 * sgn X.p0 e.2.1.2 * ((la e.1 e.2.1.2 : ℝ) - (la e.1 e.2.1.1 : ℝ)) * ‖ξ (Fintype.equivFin (Ent X) e)‖ ^ 2) →
    (∀ (r : ℕ) (X : Data E r) (x0 : Frame X.Ψ r) (z : V (nd X)), cpt X x0 z ∈ X.dom → ∃ (x1 : Frame X.Ψ r) (D : (Fin (nd X) → ℂ) →ₗ[ℂ] (Fin (nd X) → ℂ)), IsOrth X x1 ∧ Function.Injective D ∧ ∀ (la : Wt X.Ψ r) (ξ : Fin (nd X) → ℂ), leviM X (phla X la) x0 z ξ = leviM X (phla X la) x1 0 (D ξ)) →
    ((CurvGGStatement (E := E)) ∧ (∀ (r : ℕ) (X : Data E r) (la : Wt X.Ψ r) (m : ℝ), (∀ τ (i j : Fin r), i ≤ j → (j : ℕ) < X.p0 → la τ j ≤ la τ i) → (∀ τ (i j : Fin r), X.p0 ≤ (i : ℕ) → i ≤ j → la τ j ≤ la τ i) → (∀ τ (i j : Fin r), (i : ℕ) < X.p0 → X.p0 ≤ (j : ℕ) → m ≤ (la τ j : ℝ) - (la τ i : ℝ)) → ∀ x0, IsOrth X x0 → ∀ z ∈ OmF X x0, ∀ ξ : Fin (nd X) → ℂ, m * leviRh X x0 z ξ ≤ leviO X x0 (phla X la) z ξ)) := by
  intro hdiag htr
  refine ⟨fun r X la x0 z hz => ⟨fun hd ξ => ?_, fun hd ξ hξ => ?_⟩, ?_⟩
  · obtain ⟨x1, D, ho, -, hD⟩ := htr r X x0 z hz
    show 0 ≤ leviM X (phla X la) x0 z ξ
    rw [hD, hdiag r X la x1 ho]
    refine Finset.sum_nonneg fun e _ => mul_nonneg ?_ (by positivity)
    obtain ⟨τ, ⟨a, b⟩, hab⟩ := e
    obtain ⟨h1, h2, h3⟩ := hd τ
    have hab' : (b : ℕ) < a := hab
    rcases coeff_cases X.p0 hab' (la τ a : ℝ) (la τ b : ℝ) with ⟨h, e⟩ | ⟨h, e⟩ | ⟨h, h', e⟩
    · refine le_of_le_of_eq ?_ e.symm
      exact sub_nonneg.2 (Int.cast_le.2 (h1 b a (le_of_lt hab) h))
    · refine le_of_le_of_eq ?_ e.symm
      exact sub_nonneg.2 (Int.cast_le.2 (h2 b a h (le_of_lt hab)))
    · refine le_of_le_of_eq ?_ e.symm
      exact sub_nonneg.2 (Int.cast_le.2 (h3 b a h h'))
  · obtain ⟨x1, D, ho, hinj, hD⟩ := htr r X x0 z hz
    show 0 < leviM X (phla X la) x0 z ξ
    rw [hD, hdiag r X la x1 ho]
    have hpos : ∀ e : Ent X, 0 < sgn X.p0 e.2.1.1 * sgn X.p0 e.2.1.2 *
        ((la e.1 e.2.1.2 : ℝ) - (la e.1 e.2.1.1 : ℝ)) := by
      intro e
      obtain ⟨τ, ⟨a, b⟩, hab⟩ := e
      obtain ⟨h1, h2, h3⟩ := hd τ
      have hab' : (b : ℕ) < a := hab
      rcases coeff_cases X.p0 hab' (la τ a : ℝ) (la τ b : ℝ) with ⟨h, e⟩ | ⟨h, e⟩ | ⟨h, h', e⟩
      · refine lt_of_lt_of_eq ?_ e.symm
        exact sub_pos.2 (Int.cast_lt.2 (h1 b a hab h))
      · refine lt_of_lt_of_eq ?_ e.symm
        exact sub_pos.2 (Int.cast_lt.2 (h2 b a h hab))
      · refine lt_of_lt_of_eq ?_ e.symm
        exact sub_pos.2 (Int.cast_lt.2 (h3 b a h h'))
    have hne : D ξ ≠ 0 := fun h => hξ (hinj (h.trans (map_zero D).symm))
    obtain ⟨k, hk⟩ := Function.ne_iff.1 hne
    refine Finset.sum_pos' (fun e _ => mul_nonneg (hpos e).le (by positivity))
      ⟨(Fintype.equivFin (Ent X)).symm k, Finset.mem_univ _, mul_pos (hpos _) ?_⟩
    have hkk : (Fintype.equivFin (Ent X)) ((Fintype.equivFin (Ent X)).symm k) = k :=
      Equiv.apply_symm_apply (Fintype.equivFin (Ent X)) k
    refine pow_pos (norm_pos_iff.2 fun h => hk ?_) 2
    exact (congrArg (D ξ) hkk).symm.trans h
  · intro r X la m h1 h2 h3 x0 ho z hz ξ
    obtain ⟨x1, D, ho1, -, hD⟩ := htr r X x0 z hz
    rw [leviRh_eq X x0 ho hz, leviO, hD, hD, hdiag r X la x1 ho1, hdiag r X _ x1 ho1,
      Finset.mul_sum]
    refine Finset.sum_le_sum fun e _ => ?_
    rw [← mul_assoc]
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    obtain ⟨τ, ⟨a, b⟩, hab⟩ := e
    have hab' : (b : ℕ) < a := hab
    show m * (sgn X.p0 a * sgn X.p0 b * ((blockWt X τ b : ℝ) - (blockWt X τ a : ℝ))) ≤
      sgn X.p0 a * sgn X.p0 b * ((la τ b : ℝ) - (la τ a : ℝ))
    rcases coeff_cases X.p0 hab' (la τ a : ℝ) (la τ b : ℝ) with ⟨h, e⟩ | ⟨h, e⟩ | ⟨h, h', e⟩
    · rw [e]
      have := sub_nonneg.2 (Int.cast_le (R := ℝ).2 (h1 τ b a (le_of_lt hab) h))
      simpa [blockWt, h, hab'.trans h] using this
    · rw [e]
      have := sub_nonneg.2 (Int.cast_le (R := ℝ).2 (h2 τ b a h (le_of_lt hab)))
      simpa [blockWt, not_lt.2 h, not_lt.2 (h.trans hab'.le)] using this
    · rw [e]
      have := h3 τ b a h h'
      simpa [blockWt, sgn, h, not_lt.2 h'] using this

end GlobalTheory.CurvMargin
