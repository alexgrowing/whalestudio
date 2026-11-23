import Mathlib
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsMoriwakiBigCurve
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsCurveCountLower
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsSmallPacking
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open ReciprocityTheory.ChartRestriction.G.Geo Filter

theorem chartLat_le_chartLatNm {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]
    (y : (Σ k, ι k) → Ω) (a : K → ℤ) (τ : ℕ) : chartLat y a τ ≤ chartLatNm y a τ := fun _ hs c hc =>
  (mem_integralClosure_iff _ _).mpr (isIntegral_algebraMap (R := chartRingZ y c) (A := Ω) (x := ⟨_, hs c hc⟩))

theorem MoriwakiBigCurve.proof (hL : CurveCountLower.Statement)
    (hPk : HilbertSamuel.SmallPacking.Statement) : MoriwakiBigCurve.Statement := by
  intro K _ ι _ Ω _ y A P0 II hII hP hB _ hS hC _ _
  set Q := IsSmallH (mCoordIdeal y) y A
  set La := chartLat y A.a
  set T := II K ι (mCoordIdeal y) (0 + 1) (fun _ => A)
  obtain ⟨C, hC⟩ := hL K ι Ω y A II hII hP hB hS.1 hC
  obtain ⟨C', hC'⟩ := (hPk K ι Ω y 0 A La hP hB hS.1 fun τ => chartLat_le_chartLatNm y A.a τ).2
  have h0 : ∀ τ, 0 ≤ smallSectionCount Q La τ := fun τ => Real.log_natCast_nonneg _
  have hf : (fun k : ℕ => smallSectionCount Q La (1 * k) / (((1 * k : ℕ) : ℝ) ^ (0 + 1) / ((0 + 1).factorial : ℝ))) =
      fun k : ℕ => smallSectionCount Q La k / k := by
    funext k
    simp
  unfold arVolP
  rw [hf]
  have hC'0 : 0 ≤ C' := by simpa using (h0 0).trans (hC' 0)
  have hbdd : IsBoundedUnder (· ≤ ·) atTop fun k : ℕ => smallSectionCount Q La k / k := by
    refine ⟨2 * C', eventually_map.mpr ((eventually_ge_atTop 1).mono fun k hk => ?_)⟩
    have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
    show smallSectionCount Q La k / k ≤ 2 * C'
    rw [div_le_iff₀ (by linarith)]
    have h1 : smallSectionCount Q La k ≤ C' * ((k : ℝ) + 1) := by simpa using hC' k
    nlinarith
  refine le_of_forall_sub_le fun ε hε => le_limsup_of_frequently_le ?_ hbdd
  refine Eventually.frequently ((eventually_ge_atTop (⌈C / ε⌉₊ + 1)).mono fun k hk => ?_)
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast (Nat.le_add_left 1 _).trans hk
  have hkC : C ≤ ε * k := by
    have h1 : C / ε ≤ k := (Nat.le_ceil _).trans (by exact_mod_cast (Nat.le_succ _).trans hk)
    rwa [div_le_iff₀ hε, mul_comm] at h1
  have hτ : (k : ℝ) * T - C ≤ smallSectionCount Q La k := hC k ((Nat.le_add_left 1 _).trans hk)
  rw [le_div_iff₀ (by linarith)]
  show (T - ε) * k ≤ _
  nlinarith

end GroundTheory.Heights₂.Heights.Targets
