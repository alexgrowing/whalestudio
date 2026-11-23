import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.CrystallineFirstChernLevelCompat
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.DividedPowerReduction.CoefficientReductionFirstChernClassTateTwist
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.RSubOneMem

set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
set_option linter.unusedVariables false

noncomputable section

set_option maxHeartbeats 1000000

open CategoryTheory AlgebraicGeometry Limits GlobalTheory.LogCris DividedPowers

namespace CrystallineSemistableComparison.Pb.Kap

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} {m : ℕ} {L : Lev (per l K) m} (hL : L.Good)
  (d : ∀ n, RedIn (B.DD false (PAlg.base l) n) (B.κb (okToOC l K) false n) L.γ l n)
  (hc : ∀ n (c : Acris l), (d n).ρ ((PAlg.base l).cris n c) = Ideal.Quotient.mk _ (L.lam c)) (M : Model l K) (s : ℕ)

theorem crystalline_firstChern_level [FiniteDimensional ℚ_[l] K] (hM : M.Sm) (U : Cov M.q) (hU : ∀ α, U.d α + m ≤ s) (hs : m ≤ s)
    (a : (dat Amp).Ch M) (x : ((dat Amp).H a).N 2) (hx : (dat Amp).c1H a x) (c : HdR M.q 2) (hcK : IsFirstChernDeRham M.q (lineK a.1) c) :
    (chainOf hL M s (qb_le hL M s) (rHof d hc M s)).Rho (fun n => (show (M.HS false 2).lim from x).1 n) (evB M c) := by
  obtain ⟨N, i, -, -, hi⟩ := a.2
  have hcov := sSup_𝒱D a.1 N i hi
  obtain ⟨z, hz, -⟩ := thickening_firstChern_existsUnique L.γ M.p l s a.1 hcov
  refine ⟨fun k φ => ?_, 0, z, fun n => ?_, fun {e} bs => ?_⟩
  · show algebraMap K L.B (k • φ c) = algebraMap K L.B k * algebraMap K L.B (φ c)
    rw [smul_eq_mul, map_mul]
  · rw [pow_zero, one_smul]
    exact coefficientReduction_firstChernClass_tateTwist (d n) M.p s ((PAlg.base l).cris n) L.lam (hc n) a.1 hcov _ z (hx n) hz
  · rw [pow_zero, one_smul]
    have h1 : bMap M s hL (qb_le hL M s) 2 z = muB L.γB M.q 1 s {⊤} 2 c :=
      thickening_firstChern_pullback (nmB M hL) (QA L M s) (TF 1 s) (Or.inl ⟨rfl, 1, s, rfl⟩) (qb_le hL M s) a.1 s z _ hcov hz
        (deRham_firstChern_to_thickening L.γB M.q s (lineK a.1) c hcK)
    refine Eq.trans ?_ h1.symm
    show ∑ t, algebraMap K L.B (bs.coord t c) • muB L.γB M.q 1 s {⊤} 2 (bs t) = muB L.γB M.q 1 s {⊤} 2 c
    conv_rhs => rw [← bs.sum_repr c]
    rw [map_sum]
    exact Finset.sum_congr rfl fun t _ => (LinearMap.map_smulₛₗ _ _ _).symm

end CrystallineSemistableComparison.Pb.Kap
