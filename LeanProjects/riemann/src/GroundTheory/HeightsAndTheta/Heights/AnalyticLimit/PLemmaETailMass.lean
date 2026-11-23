import Mathlib
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.StLemmaETailMass
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.StLemmaETrunc
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.StLemmaETruncMass
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.StLemmaETruncTail
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open Filter Topology
open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot IsPotential IsSection IsPsh)

theorem LemmaETailMass.proof (hT : LemmaETrunc.Statement) (hC : LemmaETruncMass.Statement)
    (hB : LemmaETruncTail.Statement) : LemmaETailMass.Statement := by
  intro X _ _ _ D A Om L s hL hs hd hle C₁ hC₁
  obtain ⟨K, hK0, hK⟩ := hB D A Om L s hL hs hd hle
  refine ⟨(C₁ + 2) ^ D * K, fun u hu R₀ hR₀ => ?_⟩
  have htr : ∀ R, Real.exp 1 ≤ R → ∀ i, ∃ v : X → ℝ, A.Smooth v ∧ IsPsh A (potForm Om.pot v) ∧
      (∀ x, -(C₁ * Real.log R + 2) ≤ v x ∧ v x ≤ 0) ∧
      ∃ c : ℝ, ∀ x ∈ secOpen s, rSec L s x < R → v x = u i x + c := fun R hR i =>
    hT A Om (secOpen s) (rSec L s) C₁ (u i) (isOpen_secOpen hL hs) hd
      (fun x _ => exp_one_le_rSec hle x) hC₁ (hu i).smooth (hu i).nonneg (hu i).nonpos (hu i).le_u
      (hu i).smooth_or_pole R hR
  classical
  let ut : ℝ → Fin D → X → ℝ := fun R i =>
    if h : Real.exp 1 ≤ R then Classical.choose (htr R h i) else fun _ => 0
  have hut : ∀ R (h : Real.exp 1 ≤ R) i, ut R i = Classical.choose (htr R h i) := fun R h i => by
    simp only [ut, dif_pos h]
  obtain ⟨hint, hle₁⟩ := hC D A Om (secOpen s) (rSec L s) u ut (isOpen_secOpen hL hs)
    (continuousOn_rSec hL hs) (fun i => (hu i).smooth) (fun i => (hu i).nonneg)
    (fun R hR i => by
      rw [hut R hR i]
      obtain ⟨h1, h2, -, h4⟩ := Classical.choose_spec (htr R hR i)
      exact ⟨h1, h2, h4⟩) R₀ hR₀
  refine ⟨hint, hle₁.trans ?_⟩
  have hlog : 1 ≤ Real.log R₀ := by
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) hR₀
  have hM : 1 ≤ C₁ * Real.log R₀ + 2 := by nlinarith
  have hb := hK (C₁ * Real.log R₀ + 2) hM (ut R₀)
    (fun i => by rw [hut R₀ hR₀ i]; exact (Classical.choose_spec (htr R₀ hR₀ i)).1)
    (fun i => by rw [hut R₀ hR₀ i]; exact (Classical.choose_spec (htr R₀ hR₀ i)).2.1)
    (fun i x => by rw [hut R₀ hR₀ i]; exact (Classical.choose_spec (htr R₀ hR₀ i)).2.2.1 x) R₀ hR₀
  refine hb.trans ?_
  have hR₀pos : 0 < R₀ := lt_of_lt_of_le (Real.exp_pos 1) hR₀
  have hMle : C₁ * Real.log R₀ + 2 ≤ (C₁ + 2) * Real.log R₀ := by nlinarith
  have hpow : (C₁ * Real.log R₀ + 2) ^ D ≤ (C₁ + 2) ^ D * Real.log R₀ ^ D := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by linarith) hMle D
  have hnum : (C₁ * Real.log R₀ + 2) ^ D * K ≤ (C₁ + 2) ^ D * K * Real.log R₀ ^ D := by
    calc (C₁ * Real.log R₀ + 2) ^ D * K ≤ (C₁ + 2) ^ D * Real.log R₀ ^ D * K :=
          mul_le_mul_of_nonneg_right hpow hK0
      _ = (C₁ + 2) ^ D * K * Real.log R₀ ^ D := by ring
  exact div_le_div_of_nonneg_right hnum hR₀pos.le

end GroundTheory.Heights₂.Heights.AnalyticLimit
