import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.ChainOf
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.RHof
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.DividedPowerReduction.CoefficientReductionFirstChernClassTateTwist
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.DividedPowerReduction.ReductionChangeLevel
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.IsProperOfProj
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.TotPairing
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.DatPull
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.LimitBilinearCup.OmCup

set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false

noncomputable section

set_option maxHeartbeats 1000000

open CategoryTheory AlgebraicGeometry Limits GlobalTheory.LogCris DividedPowers

namespace CrystallineSemistableComparison.Pb.Kap

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

section
variable (M : Model l K)

def cupS (n i j : ℕ) : M.Hc false n i →ₗ[Acris l] M.Hc false n j →ₗ[Acris l] M.Hc false n (i + j) :=
  (CrystallineSemistableComparison.P.cup_bilin (CH.mulP (B.OcA (B.schFn M.p) (okToOC l K) false n)) (rfl : i + j = i + j)).choose

theorem cupS_apply (n i j : ℕ) (x : M.Hc false n i) (y : M.Hc false n j) :
    cupS M n i j x y = (CH.mulP (B.OcA (B.schFn M.p) (okToOC l K) false n)).cup rfl x y :=
  (CrystallineSemistableComparison.P.cup_bilin (CH.mulP (B.OcA (B.schFn M.p) (okToOC l K) false n)) (rfl : i + j = i + j)).choose_spec x y

end

section
variable {m : ℕ} (L : Lev (per l K) m) (M : Model l K) (s : ℕ)

def cupZn (n i j : ℕ) : HM (QA L M s) none ((l : L.A) ^ n) i →ₗ[L.A] HM (QA L M s) none ((l : L.A) ^ n) j →ₗ[L.A]
    HM (QA L M s) none ((l : L.A) ^ n) (i + j) :=
  (CrystallineSemistableComparison.P.cup_bilin (sqP (stdI (QA L M s) none ((l : L.A) ^ n))) (rfl : i + j = i + j)).choose

theorem cupZn_apply (n i j : ℕ) (x : HM (QA L M s) none ((l : L.A) ^ n) i) (y : HM (QA L M s) none ((l : L.A) ^ n) j) :
    cupZn L M s n i j x y = (sqP (stdI (QA L M s) none ((l : L.A) ^ n))).cup rfl x y :=
  (CrystallineSemistableComparison.P.cup_bilin (sqP (stdI (QA L M s) none ((l : L.A) ^ n))) (rfl : i + j = i + j)).choose_spec x y

def cupZ (i j : ℕ) : HO (QA L M s) i →ₗ[L.A] HO (QA L M s) j →ₗ[L.A] HO (QA L M s) (i + j) :=
  (CrystallineSemistableComparison.P.cup_bilin (CH.mulP (sP (QA L M s)).A) (rfl : i + j = i + j)).choose

theorem cupZ_apply (i j : ℕ) (x : HO (QA L M s) i) (y : HO (QA L M s) j) :
    cupZ L M s i j x y = (CH.mulP (sP (QA L M s)).A).cup rfl x y :=
  (CrystallineSemistableComparison.P.cup_bilin (CH.mulP (sP (QA L M s)).A) (rfl : i + j = i + j)).choose_spec x y

def cupW (i j : ℕ) : HO (QB L M s) i →ₗ[L.B] HO (QB L M s) j →ₗ[L.B] HO (QB L M s) (i + j) :=
  (CrystallineSemistableComparison.P.cup_bilin (CH.mulP (sP (QB L M s)).A) (rfl : i + j = i + j)).choose

theorem cupW_apply (i j : ℕ) (x : HO (QB L M s) i) (y : HO (QB L M s) j) :
    cupW L M s i j x y = (CH.mulP (sP (QB L M s)).A).cup rfl x y :=
  (CrystallineSemistableComparison.P.cup_bilin (CH.mulP (sP (QB L M s)).A) (rfl : i + j = i + j)).choose_spec x y

end

section
variable {m : ℕ} {L : Lev (per l K) m} (hL : L.Good) (M : Model l K) (s : ℕ)
  (hQ : ∀ T, QB L M s T → QA L M s (((nmB M hL).mor 0).obj T))
  (d : ∀ n, RedIn (B.DD false (PAlg.base l) n) (B.κb (okToOC l K) false n) L.γ l n)
  (hc : ∀ n (c : Acris l), (d n).ρ ((PAlg.base l).cris n c) = Ideal.Quotient.mk _ (L.lam c))

namespace CupProductChain

theorem cg_r (n i j : ℕ) (x : M.Hc false n i) (y : M.Hc false n j) :
    rHof d hc M s n (i + j) (cupS M n i j x y) = cupZn L M s n i j (rHof d hc M s n i x) (rHof d hc M s n j y) := by
  refine (congrArg (rHof d hc M s n (i + j)) (cupS_apply M n i j x y)).trans ?_
  refine Eq.trans ?_ (cupZn_apply L M s n i j _ _).symm
  exact (red_cup (d n) M.p s {⊤} ((PAlg.base l).cris n) L.lam (hc n) none).1 rfl x y

theorem cg_red (n i j : ℕ) (z : HO (QA L M s) i) (w : HO (QA L M s) j) :
    redM (QA L M s) none ((l : L.A) ^ n) (i + j) (cupZ L M s i j z w) =
      cupZn L M s n i j (redM (QA L M s) none ((l : L.A) ^ n) i z) (redM (QA L M s) none ((l : L.A) ^ n) j w) := by
  refine (congrArg (redM (QA L M s) none ((l : L.A) ^ n) (i + j)) (cupZ_apply L M s i j z w)).trans ?_
  refine Eq.trans ?_ (cupZn_apply L M s n i j _ _).symm
  exact redM_cup (QA L M s) none ((l : L.A) ^ n) rfl z w

theorem cg_b (i j : ℕ) (z : HO (QA L M s) i) (w : HO (QA L M s) j) :
    bMap M s hL hQ (i + j) (cupZ L M s i j z w) = cupW L M s i j (bMap M s hL hQ i z) (bMap M s hL hQ j w) := by
  refine (congrArg (bMap M s hL hQ (i + j)) (cupZ_apply L M s i j z w)).trans ?_
  refine Eq.trans ?_ (cupW_apply L M s i j _ _).symm
  exact (smor_cup (smB M s hL hQ)).1 rfl z w

theorem cg_mu (i j : ℕ) (v : HdR M.q i) (w : HdR M.q j) :
    muB L.γB M.q 1 s {⊤} (i + j) (cupR M i j v w) =
      cupW L M s i j (muB L.γB M.q 1 s {⊤} i v) (muB L.γB M.q 1 s {⊤} j w) := by
  refine (congrArg (muB L.γB M.q 1 s {⊤} (i + j)) (cupR_eq M i j v w)).trans ?_
  refine Eq.trans ?_ (cupW_apply L M s i j _ _).symm
  exact (muB_cup L.γB M.q 1 s {⊤}).1 rfl v w

theorem cg_tS (n i j : ℕ) (x : M.Hc false (n + 1) i) (y : M.Hc false (n + 1) j) :
    (M.HS false (i + j)).r n (cupS M (n + 1) i j x y) = cupS M n i j ((M.HS false i).r n x) ((M.HS false j).r n y) := by
  refine (congrArg ((M.HS false (i + j)).r n) (cupS_apply M (n + 1) i j x y)).trans ?_
  refine Eq.trans ?_ (cupS_apply M n i j _ _).symm
  exact CrystallineSemistableComparison.CupAbs.om_cup _ _ _ rfl x y

theorem cg_oneS (n : ℕ) : (M.HS false 0).r n (CH.oneH (B.OcA (B.schFn M.p) (okToOC l K) false (n + 1))) =
    CH.oneH (B.OcA (B.schFn M.p) (okToOC l K) false n) :=
  CrystallineSemistableComparison.CupAbs.om_one _ _ _

theorem cg_one_r (n : ℕ) : redM (QA L M s) none ((l : L.A) ^ n) 0 (CH.oneH (sP (QA L M s)).A) =
    rHof d hc M s n 0 (CH.oneH (B.OcA (B.schFn M.p) (okToOC l K) false n)) :=
  (red_cup (d n) M.p s {⊤} ((PAlg.base l).cris n) L.lam (hc n) none).2.symm

theorem cg_one_b : bMap M s hL hQ 0 (CH.oneH (sP (QA L M s)).A) = muB L.γB M.q 1 s {⊤} 0 (oneK M.q) :=
  (smor_cup (smB M s hL hQ)).2.trans (muB_cup L.γB M.q 1 s {⊤}).2.symm

end CupProductChain

end

section
variable {m : ℕ} {L : Lev (per l K) m} (hL : L.Good) (M : Model l K) (s : ℕ)
  (hQ : ∀ T, QB L M s T → QA L M s (((nmB M hL).mor 0).obj T))

def cupOf (rH : ∀ n j, M.Hc false n j →ₛₗ[L.lam] HM (QA L M s) none ((l : L.A) ^ n) j) :
    Cup (chainOf hL M s hQ rH) where
  cS n i j := cupS M n i j
  cZn n i j := cupZn L M s n i j
  cZ i j := cupZ L M s i j
  cW i j := cupW L M s i j
  cV i j := cupR M i j
  oneS n := CH.oneH (B.OcA (B.schFn M.p) (okToOC l K) false n)
  oneZ := CH.oneH (sP (QA L M s)).A
  oneV := oneK M.q

theorem one_iff (rH : ∀ n j, M.Hc false n j →ₛₗ[L.lam] HM (QA L M s) none ((l : L.A) ^ n) j)
    {Amp : ∀ M : Model l K, E.LineData M.X → Prop} (a : (dat Amp).Ch M) (x : ((dat Amp).H a).N 0) :
    ((dat Amp).H a).one x ↔ ∀ n, (show (M.HS false 0).lim from x).1 n = (cupOf hL M s hQ rH).oneS n :=
  Iff.rfl

end

end CrystallineSemistableComparison.Pb.Kap
