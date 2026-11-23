import Development.AutomorphicArithmetic.MeanSquareBounds.PrimeSetTwoBounds
import Development.AutomorphicArithmetic.MeanSquareBounds.meanSqK
import Development.AutomorphicArithmetic.MeanSquareBounds.BadShare
import Development.AutomorphicArithmetic.MeanSquareBounds.BoxOfS
import Development.AutomorphicArithmetic.MeanSquareBounds.TwistPrim
import Development.AutomorphicArithmetic.MeanSquareBounds.IndUnique
import Development.AutomorphicArithmetic.MeanSquareBounds.CountBad
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.MSqCount
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.PNTFinal
import Formalism.LandauZeroFreeBounds.SiegelWalfiszAPOfSiegelLower

open Finset Formalism.HermitianLattices.ZeroFreeRegionGL2 Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds

namespace QH

private theorem stage_log {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ Y : ℝ in Filter.atTop, 3 / 2 * (Y ^ (ε / 5) * Real.log Y ^ 2) ≤ Y ^ (ε / 4) := by
  have h := (isLittleO_log_rpow_rpow_atTop (2 : ℝ) (show 0 < ε / 20 by positivity)).bound
    (show (0 : ℝ) < 2 / 3 by norm_num)
  filter_upwards [h, Filter.eventually_gt_atTop (0 : ℝ)] with Y hY hY0
  rw [Real.rpow_two, Real.norm_of_nonneg (sq_nonneg _),
    Real.norm_of_nonneg (Real.rpow_nonneg hY0.le _)] at hY
  have e : Y ^ (ε / 4) = Y ^ (ε / 5) * Y ^ (ε / 20) := by
    rw [← Real.rpow_add hY0]; congr 1; ring
  have h5 : 0 < Y ^ (ε / 5) := Real.rpow_pos_of_pos hY0 _
  rw [e]
  nlinarith

private theorem stage_pow (C : ℝ) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ U : ℝ in Filter.atTop, |C| * U ^ (3 / 8 : ℝ) ≤ η / 2 * U ^ (9 / 10 : ℝ) := by
  have h := (tendsto_rpow_atTop (show (0 : ℝ) < 21 / 40 by norm_num)).eventually_ge_atTop
    (2 * |C| / η)
  filter_upwards [h, Filter.eventually_gt_atTop (0 : ℝ)] with U hU hU0
  have e : U ^ (9 / 10 : ℝ) = U ^ (21 / 40 : ℝ) * U ^ (3 / 8 : ℝ) := by
    rw [← Real.rpow_add hU0]; norm_num
  have h5 : 0 < U ^ (3 / 8 : ℝ) := Real.rpow_pos_of_pos hU0 _
  rw [div_le_iff₀ hη] at hU
  rw [e]
  nlinarith

theorem stage :
    ∃ C : ℝ, 0 < C ∧ ∀ (ε τ K η : ℝ) (R : ℕ), 0 < ε → ε ≤ 1 / 4 → 0 < τ → 1 ≤ K → 0 < η → ∃ Y₀ : ℝ, ∀ Y ≥ Y₀,
      ∀ (U F : ℝ) (m₀ a₀ : ℕ) (Ξ : Finset (Σ N : ℕ, DirichletCharacter ℂ (N + 1))), admitted ε Y U m₀ a₀ → (∀ p : ℕ, p.Prime → p ∣ m₀ → (p : ℝ) ≤ Y ^ (ε / 5) ∨ (Y ^ K) ^ 400 < (p : ℝ)) →
      1 ≤ F → F ≤ U ^ (1 / 2 : ℝ) → Ξ.card ≤ R → (∀ ξ ∈ Ξ, ξ.2.IsPrimitive ∧ ((ξ.1 + 1 : ℕ) : ℝ) ≤ F) →
      (PPset m₀ a₀ U).Nonempty ∧ ∀ B ⊆ PPset m₀ a₀ U,
        (∀ q ∈ B, ∃ ξ ∈ Ξ, ∃ M : ℕ, M ≠ 0 ∧ ¬ BoxAll (F * U) C τ Y (Y ^ K) (fun n => ξ.2 n * J q n) M) →
        (B.card : ℝ) ≤ η * (PPset m₀ a₀ U).card := by
  classical
  obtain ⟨C, hC, hbox⟩ := box_of_S
  obtain ⟨Cm, hCm, hms⟩ := meanSqK
  obtain ⟨Cb, hcb⟩ := count_bad
  refine ⟨C, hC, fun ε τ K η R hε hε4 hτ hK hη => ?_⟩
  obtain ⟨Y₁, hY₁⟩ := hbox ε τ K hε hε4 hτ hK
  obtain ⟨Y₂, hY₂⟩ := hms ε K hε (by linarith) hK
  obtain ⟨Y₃, hY₃⟩ := bad_share Cm τ (η / (2 * (R + 1))) hCm.le hτ (by positivity)
  obtain ⟨Y₄, hY₄⟩ := count_a Formalism.HermitianLattices.Ext.PrimesInProgressions.pnt_progressions_relative_weak_holds Formalism.ZeroFreeDirichlet.excBound ε hε
  obtain ⟨U₀, hU₀⟩ := Filter.eventually_atTop.1
    ((stage_pow Cb hη).and (Filter.eventually_ge_atTop (4 : ℝ)))
  obtain ⟨Y₅, hY₅⟩ := Filter.eventually_atTop.1 ((stage_log hε).and
    ((tendsto_rpow_atTop (show 0 < ε / 6 by positivity)).eventually_ge_atTop U₀))
  refine ⟨max (max (max Y₁ Y₂) (max Y₃ Y₄)) Y₅, ?_⟩
  intro Y hY U F m₀ a₀ Ξ hA hp hF1 hFU hR hΞ
  simp only [ge_iff_le, max_le_iff] at hY
  obtain ⟨⟨⟨h1, h2⟩, h3, h4⟩, h5⟩ := hY
  obtain ⟨hlog, hU₀Y⟩ := hY₅ Y h5
  have hU0 : 0 < U := by
    by_contra hneg
    push Not at hneg
    rcases hneg.eq_or_lt with h | h
    · rw [h, Real.zero_rpow (by norm_num)] at hFU; linarith
    · rw [Real.rpow_def_of_neg h, show (1 / 2 : ℝ) * Real.pi = Real.pi / 2 by ring,
        Real.cos_pi_div_two, mul_zero] at hFU
      linarith
  obtain ⟨hpow, hU4⟩ := hU₀ U (by
    have := Real.log_le_sub_one_of_pos hU0
    have := hA.lo
    linarith)
  have hcount := hY₄ Y U m₀ a₀ h4 hA.pos hA.eight hA.coprime hA.log_m hA.lo hA.hi
  have hM := hY₂ Y h2 U m₀ a₀ hA hp
  have hsq2 : (2 : ℝ) ≤ U ^ (1 / 2 : ℝ) := by
    rw [← Real.sqrt_eq_rpow]
    exact Real.le_sqrt_of_sq_le (by linarith)
  have hF0 : 0 < F := by linarith
  have hlogF0 : 0 ≤ Real.log F := Real.log_nonneg hF1
  have hlogF : Real.log F ≤ 1 / 2 * Real.log U := by
    rw [← Real.log_rpow hU0]; exact Real.log_le_log hF0 hFU
  have hlo : Y ^ (ε / 6) ≤ Real.log (F * U) := by
    rw [Real.log_mul hF0.ne' hU0.ne']; linarith [hA.lo]
  have hhi : Real.log (F * U) ≤ Y ^ (ε / 4) := by
    rw [Real.log_mul hF0.ne' hU0.ne']; linarith [hA.hi]
  refine ⟨?_, fun B hB hbad => ?_⟩
  · rw [← Finset.card_pos]
    have : (0 : ℝ) < (PPset m₀ a₀ U).card := lt_of_lt_of_le (Real.rpow_pos_of_pos hU0 _) hcount
    exact_mod_cast this
  have hPP : ∀ q ∈ B, q.Prime ∧ U ^ (1 / 2 : ℝ) < q ∧ (q : ℝ) ≤ U := by
    intro q hq
    have := Finset.mem_filter.1 (hB hq)
    refine ⟨this.2.1, this.2.2.2, ?_⟩
    exact (Nat.le_floor_iff hU0.le).1 (Finset.mem_Icc.1 this.1).2
  set B₁ := B.filter (fun q => ∃ (f : ℕ) (_ : NeZero (f * q)) (ψ : DirichletCharacter ℂ (f * q)),
    (f : ℝ) ≤ F ∧ ((f * q : ℕ) : ℝ) ≤ F * U ∧ ψ.IsPrimitive ∧ ¬ ZeroFreeBox (F * U) ψ) with hB₁
  set B₂ : (Σ N : ℕ, DirichletCharacter ℂ (N + 1)) → Finset ℕ := fun ξ => B.filter (fun q =>
    ∃ y ∈ Set.Icc Y (Y ^ K), y ^ (1 / 2 + τ) / 2 < ‖S ((Y ^ K) ^ 400) y q (fun n => ξ.2 n)‖) with hB₂
  have hsub : B ⊆ B₁ ∪ Ξ.biUnion B₂ := by
    intro q hq
    obtain ⟨ξ, hξ, M, hM0, hnb⟩ := hbad q hq
    obtain ⟨hqp, hq1, hq2⟩ := hPP q hq
    obtain ⟨hξp, hξF⟩ := hΞ ξ hξ
    have hq2' : q ≠ 2 := by
      rintro rfl
      push_cast at hq1
      linarith
    have hnd : ¬ q ∣ ξ.1 + 1 := by
      intro hd
      have : (q : ℝ) ≤ ((ξ.1 + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_of_dvd (Nat.succ_pos _) hd
      linarith
    obtain ⟨ψ, hψp, hψ1, hψ⟩ := twist_prim (ξ.1 + 1) q ξ.2 hξp hqp hq2' hnd
    haveI hne : NeZero ((ξ.1 + 1) * q) := ⟨mul_ne_zero (Nat.succ_ne_zero _) hqp.ne_zero⟩
    have hlev : (((ξ.1 + 1) * q : ℕ) : ℝ) ≤ F * U := by
      rw [Nat.cast_mul]
      exact mul_le_mul hξF hq2 (Nat.cast_nonneg _) hF0.le
    by_contra hcon
    rw [Finset.mem_union, not_or] at hcon
    obtain ⟨hc1, hc2⟩ := hcon
    have hz : ZeroFreeBox (F * U) ψ := by
      by_contra hz
      exact hc1 (Finset.mem_filter.2 ⟨hq, ξ.1 + 1, hne, ψ, hξF, hlev, hψp, hz⟩)
    have hS : ∀ y ∈ Set.Icc Y (Y ^ K),
        ‖S ((Y ^ K) ^ 400) y q (fun n => ξ.2 n)‖ ≤ y ^ (1 / 2 + τ) / 2 := by
      intro y hy
      by_contra hy'
      exact hc2 (Finset.mem_biUnion.2 ⟨ξ, hξ, Finset.mem_filter.2 ⟨hq, y, hy, not_le.1 hy'⟩⟩)
    have hB := hY₁ Y h1 (F * U) _ ψ q (fun n => ξ.2 n) hlo hhi ⟨hψ1, hlev, hz⟩ hψ hS
    apply hnb
    intro N _ ψ' hI
    have he := ind_unique N _ M ψ' ψ hM0 hI.1 hψp (fun n hn => (hI.2 n hn).trans (hψ n).symm)
    obtain ⟨rfl, he2⟩ := Sigma.mk.inj_iff.1 he
    obtain rfl := eq_of_heq he2
    exact hB
  have hP0 : (0 : ℝ) ≤ (PPset m₀ a₀ U).card := Nat.cast_nonneg _
  have hb1 : (B₁.card : ℝ) ≤ η / 2 * (PPset m₀ a₀ U).card := by
    have h := hcb (F * U) F B₁ (by nlinarith) (fun q hq => by
      obtain ⟨hq1, hq2⟩ := Finset.mem_filter.1 hq
      exact ⟨(hPP q hq1).1, lt_of_le_of_lt hFU (hPP q hq1).2.1, hq2⟩)
    have e : (U ^ (1 / 2 : ℝ) * U) ^ (1 / 4 : ℝ) = U ^ (3 / 8 : ℝ) := by
      rw [← Real.rpow_add_one hU0.ne', ← Real.rpow_mul hU0.le]; norm_num
    have h' : (F * U) ^ (1 / 4 : ℝ) ≤ U ^ (3 / 8 : ℝ) := by
      rw [← e]
      exact Real.rpow_le_rpow (by positivity) (mul_le_mul_of_nonneg_right hFU hU0.le) (by norm_num)
    calc (B₁.card : ℝ) ≤ Cb * (F * U) ^ (1 / 4 : ℝ) := h
      _ ≤ |Cb| * U ^ (3 / 8 : ℝ) :=
          mul_le_mul (le_abs_self _) h' (by positivity) (abs_nonneg _)
      _ ≤ η / 2 * U ^ (9 / 10 : ℝ) := hpow
      _ ≤ _ := mul_le_mul_of_nonneg_left hcount (by positivity)
  have hb2 : ∀ ξ ∈ Ξ, ((B₂ ξ).card : ℝ) ≤ η / (2 * (R + 1)) * (PPset m₀ a₀ U).card := by
    intro ξ _
    exact hY₃ Y h3 (Y ^ K) _ _ (B₂ ξ) (fun n => ξ.2 n) (fun n => ξ.2.norm_le_one _) hM
      ((Finset.filter_subset _ _).trans hB) (fun q hq => (Finset.mem_filter.1 hq).2)
  have hb3 : ((Ξ.biUnion B₂).card : ℝ) ≤ η / 2 * (PPset m₀ a₀ U).card := by
    have hR' : (Ξ.card : ℝ) ≤ R + 1 := by exact_mod_cast hR.trans (Nat.le_succ R)
    calc ((Ξ.biUnion B₂).card : ℝ) ≤ ∑ ξ ∈ Ξ, ((B₂ ξ).card : ℝ) := by
          exact_mod_cast Finset.card_biUnion_le
      _ ≤ Ξ.card • (η / (2 * (R + 1)) * (PPset m₀ a₀ U).card) := Finset.sum_le_card_nsmul _ _ _ hb2
      _ ≤ (R + 1) * (η / (2 * (R + 1)) * (PPset m₀ a₀ U).card) := by
          rw [nsmul_eq_mul]
          exact mul_le_mul_of_nonneg_right hR' (by positivity)
      _ = _ := by field_simp
  have hc : (B.card : ℝ) ≤ B₁.card + (Ξ.biUnion B₂).card := by
    exact_mod_cast (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  linarith

end QH
