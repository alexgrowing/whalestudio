import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.ToBSurj
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.OneSTr
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.MapUgAlgebraMap
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.GalOCOkToOC

set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false

noncomputable section

set_option maxHeartbeats 1000000

open CategoryTheory AlgebraicGeometry Limits GlobalTheory.LogCris DividedPowers

namespace CrystallineSemistableComparison.Pb.Kap

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} {R : Per l K} {m : ℕ}

section
variable (L : Lev R m) (M : Model l K) (s : ℕ)

abbrev QA : ObjectProperty (Thick (nlFun L.γ 0 M.X M.p (κA (OK l K) L.I))) := TS L.γ M.p l s {⊤}

abbrev QB : ObjectProperty (Thick (nlFun L.γB 0 M.gen M.q (κA K L.IB))) := TS L.γB M.q 1 s {⊤}

variable {L} in

def nmB (hL : L.Good) : NMor L.γ M.p (κA (OK l K) L.I) L.γB M.q (κA K L.IB) L.ι where
  hI := hL.ι_dp
  u := pullback.fst _ _
  g := (OK l K).subtype
  hu := pullback.condition
  hκ a r h := by
    have h1 : algebraMap (OK l K) L.A a - r ∈ L.I := Ideal.Quotient.eq.1 h
    rw [hL.ι_I, Ideal.mem_comap, map_sub, hL.ι_O] at h1
    exact Ideal.Quotient.eq.2 h1

variable {L} in

def smB (hL : L.Good) (hQ : ∀ T, QB L M s T → QA L M s (((nmB M hL).mor 0).obj T)) :
    SMor (sP (QA L M s)) (sP (QB L M s)) L.ι :=
  (nmB M hL).smor (QA L M s) (QB L M s) hQ

variable {L} in

def bMap (hL : L.Good) (hQ : ∀ T, QB L M s T → QA L M s (((nmB M hL).mor 0).obj T)) (j : ℕ) :
    HO (QA L M s) j →ₛₗ[L.ι] HO (QB L M s) j :=
  (smB M s hL hQ).o.pull j

end

def Lev.CrisOK {m : ℕ} (L : Lev (per l K) m) : Prop :=
  L.lam (algebraMap (Ainf l) (Acris l) (xi0 l)) ∈ L.I ∧
  ∀ (a : OK l K) (w : Ainf l), theta0 l w = okToOC l K a →
    algebraMap (OK l K) L.A a - L.lam (algebraMap (Ainf l) (Acris l) w) ∈ L.I

section
variable {m : ℕ} {L : Lev (per l K) m} (hL : L.Good) (M : Model l K) (s : ℕ)
  (hQ : ∀ T, QB L M s T → QA L M s (((nmB M hL).mor 0).obj T))

def chainOf (rH : ∀ n j, M.Hc false n j →ₛₗ[L.lam] HM (QA L M s) none ((l : L.A) ^ n) j) :
    Chain.{1} (per l K).A L.A L.B K where
  ℓ := l
  S n j := M.Hc false n j
  Zn n j := HM (QA L M s) none ((l : L.A) ^ n) j
  Z j := HO (QA L M s) j
  W j := HO (QB L M s) j
  V j := HdR M.q j
  lam := L.lam
  ι := L.ι
  o := algebraMap K L.B
  tS n j := (M.HS false j).r n
  tZ n j := trM (QA L M s) none (l : L.A) n j
  r := rH
  red n j := redM (QA L M s) none ((l : L.A) ^ n) j
  b j := bMap M s hL hQ j
  μ j := muB L.γB M.q 1 s {⊤} j

end

end CrystallineSemistableComparison.Pb.Kap
