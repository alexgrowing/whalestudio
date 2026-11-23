import Mathlib
import ReciprocityTheory.AnalyticForms.LeviForms.RegGlue
import ReciprocityTheory.AnalyticForms.LeviForms.RegChartC
import ReciprocityTheory.AnalyticForms.LeviForms.TailCut
import Development.AutomorphicSpectrum.Proofs.MetricProofs.LoglogQuotNonneg
open MeasureTheory Metric Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.AnForm.M.FinHolAtlas
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.Ar.RegFin

theorem isPsh_of_posPot {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X)
    (Θ : LocPot X) (h : IsPosPot A Θ) : IsPsh A Θ := by
  intro x j y hy w
  by_cases hw : w = 0
  · subst hw; rw [levi_zero]
  · exact (h x j y hy w hw).le

theorem quot_mem_unit {t : ℝ} (ht : 0 < t) (hte : t ≤ Real.exp (-Real.exp 1)) :
    0 ≤ Real.log (Real.log (1 / t)) / Real.log (1 / t) ∧
      Real.log (Real.log (1 / t)) / Real.log (1 / t) ≤ 1 := by
  obtain ⟨h1, h2⟩ := GlobalTheory.CompanionTheory.Ar.Giv.log_inv_bounds ht hte
  have hl : 0 < Real.log (1 / t) := lt_of_lt_of_le (Real.exp_pos 1) h1
  refine ⟨div_nonneg (by linarith) hl.le, ?_⟩
  rw [div_le_one hl]
  have := Real.log_le_sub_one_of_pos hl
  linarith

theorem quot_mono {t t' : ℝ} (ht : 0 < t) (htt : t ≤ t') (hte : t' ≤ Real.exp (-Real.exp 1)) :
    Real.log (Real.log (1 / t)) / Real.log (1 / t) ≤
      Real.log (Real.log (1 / t')) / Real.log (1 / t') := by
  have ht' := ht.trans_le htt
  have h1 := (GlobalTheory.CompanionTheory.Ar.Giv.log_inv_bounds ht' hte).1
  have hle : Real.log (1 / t') ≤ Real.log (1 / t) :=
    Real.log_le_log (by positivity) (one_div_le_one_div_of_le ht htt)
  exact Real.log_div_self_antitoneOn (Set.mem_Ici.2 h1) (Set.mem_Ici.2 (h1.trans hle)) hle

theorem isRegFamily_of_glue : ∀ {e : ℕ} {X : Type} [TopologicalSpace X] (A B : FinHolAtlas e X) (Θ L th : LocPot X) (s : X → X → ℂ) (ph : X → ℝ) (C₅ K Cl t₀ : ℝ) (f : ℝ → Fin B.n → X → ℝ) (F : ℝ → X → ℝ), IsPotential A Θ → IsPosPot A Θ → IsPotential A th → (∀ y, logNormSec L s y ≤ 0) → (∀ y, ∃ j, y ∈ chartBall B j 1) → (∀ y ∉ bdry s, -C₅ * Real.log (rW L s y) ≤ ph y) → 0 < K → 1 ≤ Cl → 0 < t₀ → t₀ ≤ Real.exp (-Real.exp 1) → (∀ t, 0 < t → t ≤ t₀ → A.Smooth (F t) ∧ IsPsh A (th + LocPot.ofFun (F t) + Θ.rsmul (K * epsT Cl t)) ∧ ∀ j, ∀ y ∈ chartBall B j (5 / 4), f t j y ≤ F t y ∧ F t y ≤ f t j y + K * epsT Cl t) → (∀ t, 0 < t → t ≤ t₀ → ∀ j, ∀ y ∈ chartBall B j (5 / 4), f t j y ≤ Cl ∧ -Cl * Real.log (Real.log (1 / t)) ≤ f t j y ∧ (y ∉ bdry s → ph y ≤ f t j y ∧ (rW L s y ≤ Real.log (1 / t) → f t j y ≤ ph y + t ^ ((1 : ℝ) / 3)))) → (∀ t t', 0 < t → t ≤ t' → t' ≤ t₀ → ∀ j, ∀ y ∈ chartBall B j (5 / 4), f t j y ≤ f t' j y + epsT Cl t') → ∃ C : ℝ, IsRegFamily A Θ L s th ph F C t₀ := by
  intro e X _ A B Θ L th s ph C₅ K Cl t₀ f F hΘ hΘp hth hs hcov hph hK hCl ht₀ ht₀e hF hf hmono
  have hΘpsh := isPsh_of_posPot A Θ hΘp
  obtain ⟨C, hCdef⟩ : ∃ C : ℝ, C = Cl * (1 + K) + |C₅| + 1 := ⟨_, rfl⟩
  have hC5 := abs_nonneg C₅
  have hClK : 0 ≤ Cl * K := by positivity
  have hC1 : 1 ≤ C := by nlinarith
  have hCK : Cl * (1 + K) ≤ C := by linarith
  have hCl' : Cl ≤ C := by nlinarith
  have hKCl : K * Cl ≤ C := by nlinarith
  have hr : ∀ y, Real.exp 1 ≤ rW L s y := rW_ge L s hs
  have he1 : (1 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hpt : ∀ y, ∃ j, y ∈ chartBall B j (5 / 4) := fun y => by
    obtain ⟨j, hj⟩ := hcov y
    exact ⟨j, chartBall_mono B j (by norm_num) hj⟩
  have ht₀1 : t₀ < 1 :=
    lt_of_le_of_lt ht₀e (by
      have := Real.exp_lt_exp.2 (show -Real.exp 1 < 0 by linarith [Real.exp_pos 1])
      rwa [Real.exp_zero] at this)
  refine ⟨C, ht₀, ht₀1, fun t ht htt => ?_⟩
  have hte := htt.trans ht₀e
  obtain ⟨hl1, hll⟩ := GlobalTheory.CompanionTheory.Ar.Giv.log_inv_bounds ht hte
  obtain ⟨hg0, hg1⟩ := quot_mem_unit ht hte
  obtain ⟨g, hgdef⟩ : ∃ g : ℝ, g = Real.log (Real.log (1 / t)) / Real.log (1 / t) := ⟨_, rfl⟩
  rw [← hgdef] at hg0 hg1
  have hεC : epsT C t = C * g := by rw [GlobalTheory.CompanionTheory.Ar.Giv.epsT_eq_mul, hgdef]
  have hεl : epsT Cl t = Cl * g := by rw [GlobalTheory.CompanionTheory.Ar.Giv.epsT_eq_mul, hgdef]
  obtain ⟨hsm, hpsh, hFf⟩ := hF t ht htt
  have hKg : K * (Cl * g) ≤ K * Cl := by
    have := mul_le_mul_of_nonneg_left hg1 (by linarith : (0 : ℝ) ≤ Cl)
    nlinarith
  have hKg0 : 0 ≤ K * (Cl * g) := by positivity
  have hFC : ∀ y, F t y ≤ Cl * (1 + K) := fun y => by
    obtain ⟨j, hj⟩ := hpt y
    have h1 := (hFf j y hj).2
    have h2 := (hf t ht htt j y hj).1
    rw [hεl] at h1
    nlinarith
  refine ⟨hsm, fun y => (hFC y).trans hCK, fun y hy => ?_, fun y => ?_, ?_,
    fun y hy hyr => ?_, fun y hy => ?_, fun t' htt' ht' y => ?_⟩
  · obtain ⟨j, hj⟩ := hpt y
    exact ((hf t ht htt j y hj).2.2 hy).1.trans (hFf j y hj).1
  · obtain ⟨j, hj⟩ := hpt y
    have h1 := (hFf j y hj).1
    have h2 := (hf t ht htt j y hj).2.1
    have : Cl * Real.log (Real.log (1 / t)) ≤ C * Real.log (Real.log (1 / t)) :=
      mul_le_mul_of_nonneg_right hCl' (by linarith)
    linarith
  · refine GlobalTheory.CompanionTheory.Ar.Giv.isPsh_rsmul_mono A Θ th (F t) hΘ hΘpsh hth hsm ?_ hpsh
    rw [hεl, hεC]
    have := mul_le_mul_of_nonneg_right hKCl hg0
    nlinarith
  · obtain ⟨j, hj⟩ := hpt y
    have h1 := (hFf j y hj).2
    have h2 := ((hf t ht htt j y hj).2.2 hy).2 hyr
    rw [hεl] at h1
    rw [hεC]
    have := mul_le_mul_of_nonneg_right hKCl hg0
    nlinarith
  · obtain ⟨j, hj⟩ := hpt y
    have h1 := (hFf j y hj).2
    have hfj := hf t ht htt j y hj
    rw [hεl] at h1
    rw [hεC]
    have hry := hr y
    have hrpos : 0 < rW L s y := by linarith
    have ht3 : 0 ≤ t ^ ((1 : ℝ) / 3) := by positivity
    have hCg0 : 0 ≤ C * g := by positivity
    by_cases hyr : rW L s y ≤ Real.log (1 / t)
    · have h2 := (hfj.2.2 hy).2 hyr
      have h3 : C * g ≤ C * g * rW L s y := le_mul_of_one_le_right hCg0 (by linarith)
      have := mul_le_mul_of_nonneg_right hKCl hg0
      nlinarith
    · push_neg at hyr
      have hlog : Real.log (rW L s y) / rW L s y ≤ g := by
        rw [hgdef]
        exact Real.log_div_self_antitoneOn (Set.mem_Ici.2 hl1) (Set.mem_Ici.2 hry) hyr.le
      have hlog' : Real.log (rW L s y) ≤ g * rW L s y := by
        rw [div_le_iff₀ hrpos] at hlog
        linarith
      have hlpos : 0 < Real.log (1 / t) := by linarith [Real.exp_pos 1]
      have hgr : 1 ≤ g * rW L s y := by
        have e1 : g * rW L s y = Real.log (Real.log (1 / t)) * (rW L s y / Real.log (1 / t)) := by
          rw [hgdef]; ring
        have e2 : 1 ≤ rW L s y / Real.log (1 / t) := by
          rw [le_div_iff₀ hlpos]; linarith
        rw [e1]
        nlinarith
      have hlr0 : 0 ≤ Real.log (rW L s y) := Real.log_nonneg (by linarith)
      have hph1 := hph y hy
      have hph2 : -|C₅| * Real.log (rW L s y) ≤ -C₅ * Real.log (rW L s y) :=
        mul_le_mul_of_nonneg_right (by linarith [le_abs_self C₅]) hlr0
      have h4 : |C₅| * Real.log (rW L s y) ≤ |C₅| * (g * rW L s y) :=
        mul_le_mul_of_nonneg_left hlog' hC5
      have h5 : Cl * (1 + K) ≤ Cl * (1 + K) * (g * rW L s y) :=
        le_mul_of_one_le_right (by positivity) hgr
      have hCg : C * g * rW L s y = (Cl * (1 + K) + |C₅| + 1) * (g * rW L s y) := by
        rw [hCdef]; ring
      have := hFC y
      nlinarith
  · have ht'0 : 0 < t' := ht.trans_le htt'
    have hte' := ht'.trans ht₀e
    obtain ⟨hg0', hg1'⟩ := quot_mem_unit ht'0 hte'
    have hgm := quot_mono ht htt' hte'
    obtain ⟨g', hgdef'⟩ : ∃ g' : ℝ, g' = Real.log (Real.log (1 / t')) / Real.log (1 / t') :=
      ⟨_, rfl⟩
    rw [← hgdef'] at hg0' hg1'
    rw [← hgdef, ← hgdef'] at hgm
    have hεC' : epsT C t' = C * g' := by rw [GlobalTheory.CompanionTheory.Ar.Giv.epsT_eq_mul, hgdef']
    have hεl' : epsT Cl t' = Cl * g' := by rw [GlobalTheory.CompanionTheory.Ar.Giv.epsT_eq_mul, hgdef']
    obtain ⟨j, hj⟩ := hpt y
    have h1 := (hFf j y hj).2
    have h2 := hmono t t' ht htt' ht' j y hj
    have h3 := ((hF t' ht'0 ht').2.2 j y hj).1
    rw [hεl] at h1
    rw [hεl'] at h2
    rw [hεC']
    have h4 : K * (Cl * g) ≤ K * (Cl * g') :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hgm (by linarith)) hK.le
    have h5 : Cl * (1 + K) * g' ≤ C * g' := mul_le_mul_of_nonneg_right hCK hg0'
    have h6 : C * g' ≤ C * (C * g') := le_mul_of_one_le_left (by positivity) hC1
    linarith

end GlobalTheory.CompanionTheory.Ar.RegFin
