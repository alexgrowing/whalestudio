import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.CrystallineFirstChernLevelCompat
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.DividedPowerReduction.CoefficientReductionFirstChernClassTateTwist
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.SplittingFieldLattices.BcOnFalse
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.IsProperOfProj
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.TranscendentalPeriodUnits.IsUOfIsUnit

set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
set_option linter.unusedVariables false

noncomputable section

set_option maxHeartbeats 6000000

open CategoryTheory AlgebraicGeometry Limits GlobalTheory.LogCris DividedPowers

namespace CrystallineSemistableComparison.Pb.Kap

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} {m : ℕ} {L : Lev (per l K) m} (hL : L.Good)
  (d : ∀ n, RedIn (B.DD false (PAlg.base l) n) (B.κb (okToOC l K) false n) L.γ l n)
  (hc : ∀ n (c : Acris l), (d n).ρ ((PAlg.base l).cris n c) = Ideal.Quotient.mk _ (L.lam c)) (M : Model l K) (s : ℕ)

omit d hc in
theorem pdP_B_bot (hL : L.Good) : pdP L.γB m = ⊥ := by
  obtain ⟨y, hy⟩ := (hL.toB_ker 0).1 (map_zero _)
  by_cases ht : (per l K).tB ∈ (per l K).P
  · rw [hL.pdP_B m ⟨_, ht⟩ rfl, Ideal.span_singleton_eq_bot, ← map_pow, hL.toB_ker]
    exact ⟨1, by simp⟩
  · exact absurd (facts l K).t_mem ht

omit d hc in

theorem quoM_bMap (hQ : ∀ T, QB L M s T → QA L M s (((nmB M hL).mor 0).obj T)) (r : ℤ) (j : ℕ) (z : HO (QA L M s) j)
    (hz : quoM (QA L M s) r j z = 0) : quoM (QB L M s) r j (bMap M s hL hQ j z) = 0 := by
  have e : quoM (QB L M s) r j (bMap M s hL hQ j z) =
      ((smB M s hL hQ).sq (a := sFil _ 0) (a' := sFil _ 0) (b := sFil _ r) (b' := sFil _ r) (fun _ _ hx => hx)
        fun _ _ hx => hx).pull j (quoM (QA L M s) r j z) := by
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ z
    rfl
  rw [e, hz, map_zero]

set_option maxHeartbeats 1600000 in
theorem fil_lev_pf [FiniteDimensional ℚ_[l] K] (hM : M.Sm) (U : Cov M.q) (hU : ∀ α, U.d α + m ≤ s) (hs : m ≤ s) {j : ℕ}
    (x : ∀ n, M.Hc false n j) (hx : (chainOf hL M s (qb_le hL M s) (rHof d hc M s)).Comp x)
    (f : Module.Dual K (HdR M.q j) →+ L.B) (hf : (chainOf hL M s (qb_le hL M s) (rHof d hc M s)).Rho x f) (N r : ℕ) (hN : N ≤ s)
    (hfil : ∀ n, x n ∈ B.HcFil (B.schFn M.p) (okToOC l K) false n N j) (φ : Module.Dual K (HdR M.q j))
    (hφ : ∀ h ∈ FilR M.q j (r + 1), φ h = 0) : f φ ∈ pdP L.γB (N - r) := by
  obtain ⟨hlin, e, z, hz, hb⟩ := hf
  obtain ⟨e', -, -, hsep⟩ := cg_lift hL M hM s hs j
  have h1 : ∀ n, redM (QA L M s) (some (N : ℤ)) ((l : L.A) ^ n) j z = 0 := fun n => by
    have h2 : redM (QA L M s) none ((l : L.A) ^ n) j z = (l : L.A) ^ e • rHof d hc M s n j (x n) := hz n
    rw [← toSome_redM, h2, map_smul]
    have h3 : toSome (QA L M s) N ((l : L.A) ^ n) j (rHof d hc M s n j (x n)) = 0 :=
      red_fil (d n) M.p s {⊤} ((PAlg.base l).cris n) L.lam (hc n) N j (x n) (hfil n)
    rw [h3, smul_zero]
  have h4 := hsep N (by exact_mod_cast hN) z h1
  rw [← map_smul] at h4
  have h5 := quoM_bMap hL M s (qb_le hL M s) N j _ h4
  haveI := (m_fin M hM j).1
  let bs := Module.finBasis K (HdR M.q j)
  have h6 : (l : L.B) ^ e • ∑ t, f (bs.coord t) • muB L.γB M.q 1 s {⊤} j (bs t) = bMap M s hL (qb_le hL M s) j z := hb bs
  rw [LinearMap.map_smulₛₗ, ← h6, map_pow, map_natCast, map_smul, map_smul] at h5
  have hu := unit_B hL
  rw [(hu.pow e').smul_eq_zero, (hu.pow e).smul_eq_zero] at h5
  have h7 := (basisB L.γB s m (pdP_B_bot hL) hs M.q U hU {⊤} sSup_singleton j bs).2 N hN _ h5 r φ hφ
  have h8 : f φ = ∑ t, f (bs.coord t) * algebraMap K L.B (φ (bs t)) := by
    conv_lhs => rw [← bs.dualBasis.sum_repr φ]
    rw [map_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    refine (hlin _ _).trans ?_
    rw [Module.Basis.dualBasis_repr, Module.Basis.coe_dualBasis, mul_comm]
    rfl
  rw [h8]
  exact h7

end CrystallineSemistableComparison.Pb.Kap
