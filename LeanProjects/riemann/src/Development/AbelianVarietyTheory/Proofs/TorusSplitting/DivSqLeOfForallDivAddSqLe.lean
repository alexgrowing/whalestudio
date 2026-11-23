import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.SplitSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.GaussianTailBound
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.SplitC
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.SplitR
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.SplitV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.SplitOA

namespace GlobalTheory

open NumberField Complex ReciprocityTheory.ChartRestriction.G.I2
open scoped InnerProductSpace

noncomputable section

open NumberField Complex in
open scoped InnerProductSpace in

theorem _root_.GlobalTheory.greedy_splitting_thin :
    (∀ (E : Type) [Field E] [NumberField E] [IsCMField E], ∃ (n : ℕ) (ω : Fin n → 𝓞 E), (∀ j (σ : E →+* ℂ), ‖σ (ω j)‖ ≤ _root_.ReciprocityTheory.ChartRestriction.G.I2.omStar (E := E)) ∧ ∀ α : 𝓞 E, (α : E) ∈ Submodule.span ℚ (Set.range fun j => (ω j : E))) →
    (∀ (E : Type) [Field E] [NumberField E] (X : _root_.ReciprocityTheory.ChartRestriction.G.I2.PT E) (I : Submodule ℤ (_root_.ReciprocityTheory.ChartRestriction.G.I2.Vsp X.dim)), I ≤ X.L → (∀ x ∈ X.L, x ∈ _root_.ReciprocityTheory.ChartRestriction.G.I2.IR I → x ∈ I) → 0 < X.la1 → ∃ x u : Fin (Module.finrank ℝ (_root_.ReciprocityTheory.ChartRestriction.G.I2.IR I)) → _root_.ReciprocityTheory.ChartRestriction.G.I2.Vsp X.dim, (∀ j, x j ∈ X.L ∧ _root_.ReciprocityTheory.ChartRestriction.G.I2.IsU I (x j) (u j)) ∧ LinearIndependent ℝ u ∧ ∀ j, ‖u j‖ ≤ (Module.finrank ℝ (_root_.ReciprocityTheory.ChartRestriction.G.I2.IR I) : ℝ) ^ 2 / X.la1) →
    (∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (X : _root_.ReciprocityTheory.ChartRestriction.G.I2.PT E) (DF : ℕ) (P : _root_.ReciprocityTheory.ChartRestriction.G.I2.Par X DF), X.la1 < P.th → ∃ I, _root_.ReciprocityTheory.ChartRestriction.G.I2.IsSplit P I) := by
  intro hω hshort E _ _ _ X DF P hthin
  obtain ⟨n, ω, hωb, hωs⟩ := hω E
  have hf1 : 1 ≤ _root_.ReciprocityTheory.ChartRestriction.G.I2.PT.f E := le_trans (Nat.one_le_pow _ _ P.hm1) P.hmf
  have hfpos : (0 : ℝ) < _root_.ReciprocityTheory.ChartRestriction.G.I2.PT.f E := by exact_mod_cast hf1
  have hf1' : (1 : ℝ) ≤ _root_.ReciprocityTheory.ChartRestriction.G.I2.PT.f E := by exact_mod_cast hf1
  have hrd : (16 : ℝ) ≤ _root_.ReciprocityTheory.ChartRestriction.G.I2.PT.rd E := P.hrd
  have hrdpos : 0 < _root_.ReciprocityTheory.ChartRestriction.G.I2.PT.rd E := by linarith
  have hf2 : (_root_.ReciprocityTheory.ChartRestriction.G.I2.PT.f E : ℝ) ^ 2 ≤ _root_.ReciprocityTheory.ChartRestriction.G.I2.PT.rd E := P.hf2
  have hr : 1 ≤ X.r := by
    rcases Nat.eq_zero_or_pos X.r with h | h
    · have := P.hfr
      rw [h, mul_zero] at this
      omega
    · exact h
  obtain ⟨τ, hτ⟩ := P.hm
  obtain ⟨x₀, hx₀L, hx₀⟩ := _root_.ReciprocityTheory.ChartRestriction.G.I2.L_ne_zero X hr τ
  have hne : ∃ x ∈ X.L, x ≠ 0 := ⟨x₀, hx₀L, hx₀⟩
  have hla : 0 < X.la1 := _root_.ReciprocityTheory.ChartRestriction.G.I2.first_minimum_pos X hne
  have hth : 0 < P.th := hla.trans hthin
  have hthdef : P.th = _root_.ReciprocityTheory.ChartRestriction.G.I2.th (E := E) P.q P.R0 := rfl
  have hΩ : 0 < _root_.ReciprocityTheory.ChartRestriction.G.I2.omStar (E := E) := by
    unfold _root_.ReciprocityTheory.ChartRestriction.G.I2.omStar
    exact mul_pos (mul_pos two_pos (by positivity)) hrdpos
  have hd1 : (1 : ℝ) ≤ (_root_.ReciprocityTheory.ChartRestriction.G.I2.dstar (E := E) P.m : ℝ) := by
    have : 0 < _root_.ReciprocityTheory.ChartRestriction.G.I2.dstar (E := E) P.m := by
      unfold _root_.ReciprocityTheory.ChartRestriction.G.I2.dstar
      exact Nat.mul_pos (Nat.mul_pos two_pos hf1) P.hm1
    exact_mod_cast this
  have hΩth : _root_.ReciprocityTheory.ChartRestriction.G.I2.omStar (E := E) * P.th ^ 2 ≤ 1 := by
    have h1 : (1 : ℝ) ≤ (_root_.ReciprocityTheory.ChartRestriction.G.I2.dstar (E := E) P.m : ℝ) ^ 2 := one_le_pow₀ hd1
    have hnn : 0 ≤ _root_.ReciprocityTheory.ChartRestriction.G.I2.omStar (E := E) * P.th ^ 2 := mul_nonneg hΩ.le (sq_nonneg _)
    calc _root_.ReciprocityTheory.ChartRestriction.G.I2.omStar (E := E) * P.th ^ 2 = 1 * (_root_.ReciprocityTheory.ChartRestriction.G.I2.omStar (E := E) * P.th ^ 2) := by ring
      _ ≤ (_root_.ReciprocityTheory.ChartRestriction.G.I2.dstar (E := E) P.m : ℝ) ^ 2 * (_root_.ReciprocityTheory.ChartRestriction.G.I2.omStar (E := E) * P.th ^ 2) :=
        mul_le_mul_of_nonneg_right h1 hnn
      _ = (_root_.ReciprocityTheory.ChartRestriction.G.I2.dstar (E := E) P.m : ℝ) ^ 2 * _root_.ReciprocityTheory.ChartRestriction.G.I2.omStar (E := E) * _root_.ReciprocityTheory.ChartRestriction.G.I2.th (E := E) P.q P.R0 ^ 2 := by
        rw [hthdef]; ring
      _ ≤ 1 := P.C1.le
  obtain ⟨I, hG, hthick⟩ := _root_.ReciprocityTheory.ChartRestriction.G.I2.exists_maximal X ω hΩ hth hΩth hωb hωs
  have hshortI : ∀ t, X.la1 < t → t ≤ P.th → ∃ ξ ∈ I, ξ ≠ 0 ∧ ‖ξ‖ < t := by
    intro t ht ht'
    obtain ⟨ξ, hξL, hξ0, hξt⟩ := _root_.ReciprocityTheory.ChartRestriction.G.I2.exists_short X hne ht
    refine ⟨ξ, ?_, hξ0, hξt⟩
    by_contra hξI
    have h1 := hthick ξ hξL hξI
    have h2 : Metric.infDist ξ (_root_.ReciprocityTheory.ChartRestriction.G.I2.IR I : Set (_root_.ReciprocityTheory.ChartRestriction.G.I2.Vsp X.dim)) ≤ ‖ξ‖ := by
      have := Metric.infDist_le_dist_of_mem (x := ξ) (Submodule.zero_mem (_root_.ReciprocityTheory.ChartRestriction.G.I2.IR I))
      rwa [dist_zero_right] at this
    linarith
  have hph : P.ph = 2 * (_root_.ReciprocityTheory.ChartRestriction.G.I2.PT.f E : ℝ) / (_root_.ReciprocityTheory.ChartRestriction.G.I2.PT.rd E ^ 2 * X.la1 ^ 2) := by
    show X.ph P.th = _
    unfold _root_.ReciprocityTheory.ChartRestriction.G.I2.PT.ph
    rw [if_pos hthin]
  obtain ⟨ρ, hρ, hrk⟩ := _root_.ReciprocityTheory.ChartRestriction.G.I2.rank_iso X I hG.le hG.stable hG.iso
  have hρm : ρ ≤ P.m := (hρ τ).trans hτ
  refine ⟨I, _root_.ReciprocityTheory.ChartRestriction.G.I2.IsSplit.mk hG.le (_root_.ReciprocityTheory.ChartRestriction.G.I2.sat_of_IR hG.sat) hG.stable hG.iso ?_ ⟨ρ, hρm, hrk⟩ ?_
    (fun x hx _ hxI => hthick x hx hxI) ?_ ?_ ?_⟩
  · intro x hx
    exact X.eps_iso x (hG.le hx) (fun α => hG.iso _ (hG.stable α x hx) x hx)
  · refine ⟨fun _ => hthin, fun _ hbot => ?_⟩
    obtain ⟨ξ, hξ, hξ0, -⟩ := hshortI P.th hthin le_rfl
    rw [hbot] at hξ
    exact hξ0 ((Submodule.mem_bot ℤ).mp hξ)
  · intro x hx u hu hu0
    have h := hG.sep x hx u hu hu0
    have hq : (1 : ℝ) ≤ P.q := by exact_mod_cast P.hq
    have hR : P.R0 ^ 2 ≠ 0 := by have := P.hR0.1; positivity
    have hM : _root_.ReciprocityTheory.ChartRestriction.G.I2.RR (E := E) = _root_.ReciprocityTheory.ChartRestriction.G.I2.PT.rd E ^ 7 := by unfold _root_.ReciprocityTheory.ChartRestriction.G.I2.RR; rfl
    have hth2 : P.th ^ 2 = (_root_.ReciprocityTheory.ChartRestriction.G.I2.PT.f E : ℝ) * P.R0 ^ 2 * _root_.ReciprocityTheory.ChartRestriction.G.I2.RR (E := E) ^ 3 / P.q := by
      rw [hthdef]
      unfold _root_.ReciprocityTheory.ChartRestriction.G.I2.th
      rw [Real.sq_sqrt]
      rw [hM]
      have : 0 ≤ _root_.ReciprocityTheory.ChartRestriction.G.I2.PT.rd E ^ 7 := by positivity
      positivity
    have hΩ2 : _root_.ReciprocityTheory.ChartRestriction.G.I2.omStar (E := E) ^ 2 = 4 * (_root_.ReciprocityTheory.ChartRestriction.G.I2.PT.f E : ℝ) ^ 3 * _root_.ReciprocityTheory.ChartRestriction.G.I2.PT.rd E ^ 2 := by
      unfold _root_.ReciprocityTheory.ChartRestriction.G.I2.omStar
      rw [mul_pow, mul_pow, ← Real.rpow_mul_natCast hfpos.le]
      norm_num
    have hb0 : _root_.ReciprocityTheory.ChartRestriction.G.I2.b0 (E := E) P.q P.R0 = P.q / (P.R0 ^ 2 * _root_.ReciprocityTheory.ChartRestriction.G.I2.RR (E := E) ^ 4) := by
      unfold _root_.ReciprocityTheory.ChartRestriction.G.I2.b0; rfl
    have hfr : (_root_.ReciprocityTheory.ChartRestriction.G.I2.PT.f E : ℝ) ≤ _root_.ReciprocityTheory.ChartRestriction.G.I2.PT.rd E := by nlinarith
    have hf3 : (_root_.ReciprocityTheory.ChartRestriction.G.I2.PT.f E : ℝ) ^ 3 ≤ _root_.ReciprocityTheory.ChartRestriction.G.I2.PT.rd E ^ 2 := by
      calc (_root_.ReciprocityTheory.ChartRestriction.G.I2.PT.f E : ℝ) ^ 3 = _root_.ReciprocityTheory.ChartRestriction.G.I2.PT.f E * (_root_.ReciprocityTheory.ChartRestriction.G.I2.PT.f E : ℝ) ^ 2 := by ring
        _ ≤ _root_.ReciprocityTheory.ChartRestriction.G.I2.PT.rd E * _root_.ReciprocityTheory.ChartRestriction.G.I2.PT.rd E := mul_le_mul hfr hf2 (by positivity) hrdpos.le
        _ = _root_.ReciprocityTheory.ChartRestriction.G.I2.PT.rd E ^ 2 := by ring
    have hkey : (_root_.ReciprocityTheory.ChartRestriction.G.I2.PT.f E : ℝ) * _root_.ReciprocityTheory.ChartRestriction.G.I2.omStar (E := E) ^ 2 ≤ _root_.ReciprocityTheory.ChartRestriction.G.I2.PT.rd E ^ 7 := by
      rw [hΩ2]
      have h4 : (4 : ℝ) ≤ _root_.ReciprocityTheory.ChartRestriction.G.I2.PT.rd E ^ 3 := by nlinarith [pow_le_pow_left₀ (by norm_num) hrd 3]
      have h5 : (_root_.ReciprocityTheory.ChartRestriction.G.I2.PT.f E : ℝ) * (_root_.ReciprocityTheory.ChartRestriction.G.I2.PT.f E : ℝ) ^ 3 ≤ _root_.ReciprocityTheory.ChartRestriction.G.I2.PT.rd E ^ 2 := by
        calc (_root_.ReciprocityTheory.ChartRestriction.G.I2.PT.f E : ℝ) * (_root_.ReciprocityTheory.ChartRestriction.G.I2.PT.f E : ℝ) ^ 3 = ((_root_.ReciprocityTheory.ChartRestriction.G.I2.PT.f E : ℝ) ^ 2) ^ 2 := by ring
          _ ≤ _root_.ReciprocityTheory.ChartRestriction.G.I2.PT.rd E ^ 2 := pow_le_pow_left₀ (sq_nonneg _) hf2 2
      calc (_root_.ReciprocityTheory.ChartRestriction.G.I2.PT.f E : ℝ) * (4 * (_root_.ReciprocityTheory.ChartRestriction.G.I2.PT.f E : ℝ) ^ 3 * _root_.ReciprocityTheory.ChartRestriction.G.I2.PT.rd E ^ 2)
          = 4 * ((_root_.ReciprocityTheory.ChartRestriction.G.I2.PT.f E : ℝ) * (_root_.ReciprocityTheory.ChartRestriction.G.I2.PT.f E : ℝ) ^ 3) * _root_.ReciprocityTheory.ChartRestriction.G.I2.PT.rd E ^ 2 := by ring
        _ ≤ _root_.ReciprocityTheory.ChartRestriction.G.I2.PT.rd E ^ 3 * _root_.ReciprocityTheory.ChartRestriction.G.I2.PT.rd E ^ 2 * _root_.ReciprocityTheory.ChartRestriction.G.I2.PT.rd E ^ 2 :=
          mul_le_mul_of_nonneg_right (mul_le_mul h4 h5 (by positivity) (by positivity)) (by positivity)
        _ = _root_.ReciprocityTheory.ChartRestriction.G.I2.PT.rd E ^ 7 := by ring
    have hle : _root_.ReciprocityTheory.ChartRestriction.G.I2.b0 (E := E) P.q P.R0 ≤ (1 / (_root_.ReciprocityTheory.ChartRestriction.G.I2.omStar (E := E) * P.th)) ^ 2 := by
      rw [div_pow, one_pow, le_div_iff₀ (by positivity), mul_pow, hth2, hb0, hM]
      have hq0 : (P.q : ℝ) ≠ 0 := by positivity
      have hr7 : (0 : ℝ) < _root_.ReciprocityTheory.ChartRestriction.G.I2.PT.rd E ^ 7 := by positivity
      have hr7' : _root_.ReciprocityTheory.ChartRestriction.G.I2.PT.rd E ^ 7 ≠ 0 := hr7.ne'
      have hrd0 : _root_.ReciprocityTheory.ChartRestriction.G.I2.PT.rd E ≠ 0 := hrdpos.ne'
      have hR0 : P.R0 ≠ 0 := fun h0 => hR (by rw [h0]; ring)
      rw [show (P.q : ℝ) / (P.R0 ^ 2 * (_root_.ReciprocityTheory.ChartRestriction.G.I2.PT.rd E ^ 7) ^ 4) *
          (_root_.ReciprocityTheory.ChartRestriction.G.I2.omStar (E := E) ^ 2 * ((_root_.ReciprocityTheory.ChartRestriction.G.I2.PT.f E : ℝ) * P.R0 ^ 2 * (_root_.ReciprocityTheory.ChartRestriction.G.I2.PT.rd E ^ 7) ^ 3 / P.q))
          = (_root_.ReciprocityTheory.ChartRestriction.G.I2.PT.f E : ℝ) * _root_.ReciprocityTheory.ChartRestriction.G.I2.omStar (E := E) ^ 2 / _root_.ReciprocityTheory.ChartRestriction.G.I2.PT.rd E ^ 7 by
        field_simp]
      rw [div_le_one hr7]
      exact hkey
    exact hle.trans (pow_le_pow_left₀ (by positivity) h.le 2)
  · have hrd0 : _root_.ReciprocityTheory.ChartRestriction.G.I2.PT.rd E ≠ 0 := hrdpos.ne'
    have hf0 : (_root_.ReciprocityTheory.ChartRestriction.G.I2.PT.f E : ℝ) ≠ 0 := hfpos.ne'
    have hla0 : X.la1 ≠ 0 := hla.ne'
    obtain ⟨x, u, hxu, hli, hb⟩ := hshort E X I hG.le hG.sat hla
    refine ⟨x, u, hxu, hli, fun j => ?_⟩
    have hdd : (Module.finrank ℝ (_root_.ReciprocityTheory.ChartRestriction.G.I2.IR I) : ℝ) ≤ (_root_.ReciprocityTheory.ChartRestriction.G.I2.dstar (E := E) P.m : ℝ) := by
      have : Module.finrank ℝ (_root_.ReciprocityTheory.ChartRestriction.G.I2.IR I) ≤ _root_.ReciprocityTheory.ChartRestriction.G.I2.dstar (E := E) P.m := by
        rw [hrk]
        unfold _root_.ReciprocityTheory.ChartRestriction.G.I2.dstar
        exact Nat.mul_le_mul_left _ hρm
      exact_mod_cast this
    calc ‖u j‖ ^ 2 ≤ ((Module.finrank ℝ (_root_.ReciprocityTheory.ChartRestriction.G.I2.IR I) : ℝ) ^ 2 / X.la1) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) (hb j) 2
      _ ≤ ((_root_.ReciprocityTheory.ChartRestriction.G.I2.dstar (E := E) P.m : ℝ) ^ 2 / X.la1) ^ 2 :=
          pow_le_pow_left₀ (div_nonneg (by positivity) hla.le)
            (div_le_div_of_nonneg_right (pow_le_pow_left₀ (Nat.cast_nonneg _) hdd 2) hla.le) 2
      _ = _root_.ReciprocityTheory.ChartRestriction.G.I2.PT.rd E ^ 2 * (_root_.ReciprocityTheory.ChartRestriction.G.I2.dstar (E := E) P.m : ℝ) ^ 4 * P.ph / (2 * (_root_.ReciprocityTheory.ChartRestriction.G.I2.PT.f E : ℝ)) := by
          rw [hph]
          field_simp
  · intro k x u hxu hspan
    have hrd0 : _root_.ReciprocityTheory.ChartRestriction.G.I2.PT.rd E ≠ 0 := hrdpos.ne'
    have hla0 : X.la1 ≠ 0 := hla.ne'
    rw [hph]
    have hbound : ∀ t, X.la1 < t → t ≤ P.th →
        2 * (_root_.ReciprocityTheory.ChartRestriction.G.I2.PT.f E : ℝ) / (_root_.ReciprocityTheory.ChartRestriction.G.I2.PT.rd E ^ 2 * t ^ 2) ≤ ∑ j, ‖u j‖ ^ 2 / 2 := by
      intro t ht ht'
      obtain ⟨ξ, hξI, hξ0, hξt⟩ := hshortI t ht ht'
      refine le_trans ?_ (_root_.ReciprocityTheory.ChartRestriction.G.I2.sum_sq_norm_ge_of_span X I hG.le hG.stable hξI hξ0 k x u hxu hspan)
      exact div_le_div_of_nonneg_left (by positivity)
        (mul_pos (pow_pos hrdpos 2) (pow_pos (norm_pos_iff.mpr hξ0) 2))
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hξt.le 2) (sq_nonneg _))
    have hlim : Filter.Tendsto (fun t : ℝ => 2 * (_root_.ReciprocityTheory.ChartRestriction.G.I2.PT.f E : ℝ) / (_root_.ReciprocityTheory.ChartRestriction.G.I2.PT.rd E ^ 2 * t ^ 2))
        (nhdsWithin X.la1 (Set.Ioi X.la1))
        (nhds (2 * (_root_.ReciprocityTheory.ChartRestriction.G.I2.PT.f E : ℝ) / (_root_.ReciprocityTheory.ChartRestriction.G.I2.PT.rd E ^ 2 * X.la1 ^ 2))) := by
      refine Filter.Tendsto.mono_left ?_ nhdsWithin_le_nhds
      refine ContinuousAt.tendsto ?_
      exact ContinuousAt.div continuousAt_const (by fun_prop)
        (mul_ne_zero (pow_ne_zero 2 hrd0) (pow_ne_zero 2 hla0))
    refine le_of_tendsto hlim ?_
    filter_upwards [Ioo_mem_nhdsGT hthin] with t ht
    exact hbound t ht.1 ht.2.le

end

end GlobalTheory
