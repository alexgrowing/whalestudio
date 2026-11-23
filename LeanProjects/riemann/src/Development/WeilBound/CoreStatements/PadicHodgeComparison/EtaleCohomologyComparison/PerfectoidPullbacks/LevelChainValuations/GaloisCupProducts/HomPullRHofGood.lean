import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.GaloisCupProducts.NmHONmPullBBMap

set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false

noncomputable section

set_option maxHeartbeats 1000000

open CategoryTheory AlgebraicGeometry Limits GlobalTheory.LogCris DividedPowers

namespace CrystallineSemistableComparison.Pb.Kap

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

section
variable {m : ℕ} {L : Lev (per l K) m} (hL : L.Good) {M N : Model l K} (u : M.X ⟶ N.X) (hu : u ≫ N.p = M.p) (s : ℕ)
  (hQN : ∀ T, QB L N s T → QA L N s (((nmB N hL).mor 0).obj T))
  (hQM : ∀ T, QB L M s T → QA L M s (((nmB M hL).mor 0).obj T))
  (rHN : ∀ n j, N.Hc false n j →ₛₗ[L.lam] HM (QA L N s) none ((l : L.A) ^ n) j)
  (rHM : ∀ n j, M.Hc false n j →ₛₗ[L.lam] HM (QA L M s) none ((l : L.A) ^ n) j)

theorem homPull_good_of_nmHM_pull
    (hr : ∀ n j x, nmHM (nmPullA L u hu) l s none n j (rHN n j x) =
      rHM n j (B.pullHc (okToOC l K) (B.schMap u hu) false n j x)) :
    (homPull hL u hu s hQN hQM rHN rHM).Good where
  ℓ := rfl
  lam _ := rfl
  ι _ := rfl
  o _ := rfl
  tS n j x := ((Model.pullH u hu false j).comm n x).symm
  r n j x := hr n j x
  red n j z := nmHM_redM _ l s none n j z
  b j z := nmHO_nmPullB_bMap hL u hu s hQN hQM j z
  μ j v := nm_muB (nmPullB L u hu) (Model.genMap_q u hu) 1 s (fun _ => rfl) j v

end

theorem homPull_rHof_good {m : ℕ} {L : Lev (per l K) m}
    (d : ∀ n, RedIn (B.DD false (PAlg.base l) n) (B.κb (okToOC l K) false n) L.γ l n)
    (hc : ∀ n (c : Acris l), (d n).ρ ((PAlg.base l).cris n c) = Ideal.Quotient.mk _ (L.lam c))
    {M N : Model l K} (u : M.X ⟶ N.X) (hu : u ≫ N.p = M.p) (s : ℕ) (hL : L.Good)
    (hQN : ∀ T, QB L N s T → QA L N s (((nmB N hL).mor 0).obj T))
    (hQM : ∀ T, QB L M s T → QA L M s (((nmB M hL).mor 0).obj T)) :
    (homPull hL u hu s hQN hQM (rHof d hc N s) (rHof d hc M s)).Good :=
  homPull_good_of_nmHM_pull hL u hu s hQN hQM _ _ (rHof_pull d hc u hu s)

end CrystallineSemistableComparison.Pb.Kap
