import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.GaloisCupProducts.BMapIncl

set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
set_option linter.unusedVariables false

noncomputable section

set_option maxHeartbeats 1000000

open CategoryTheory AlgebraicGeometry Limits GlobalTheory.LogCris DividedPowers

namespace CrystallineSemistableComparison.Pb.Kap

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

section
variable (S : LevSys (per l K)) (hS : S.Good) (m : ℕ) (M : Model l K) (s : ℕ)
  (hQ₁ : ∀ T, QB (S.L (m + 1)) M s T → QA (S.L (m + 1)) M s (((nmB M (hS.lev (m + 1))).mor 0).obj T))
  (hQ₀ : ∀ T, QB (S.L m) M s T → QA (S.L m) M s (((nmB M (hS.lev m)).mor 0).obj T))
  (rH₁ : ∀ n j, M.Hc false n j →ₛₗ[(S.L (m + 1)).lam] HM (QA (S.L (m + 1)) M s) none ((l : (S.L (m + 1)).A) ^ n) j)
  (rH₀ : ∀ n j, M.Hc false n j →ₛₗ[(S.L m).lam] HM (QA (S.L m) M s) none ((l : (S.L m).A) ^ n) j)

def homLev : Hom (chainOf (hS.lev (m + 1)) M s hQ₁ rH₁) (chainOf (hS.lev m) M s hQ₀ rH₀) where
  sΛ := RingHom.id _
  sA := S.dA m
  sB := S.dB m
  fS n j := LinearMap.id
  fZn n j := nmHM (nmLevA S hS m M) l s none n j
  fZ j := nmHO (nmLevA S hS m M) l s j
  fW j := nmHO (nmLevB S hS m M) 1 s j
  fV j := LinearMap.id

end

section
variable {m : ℕ} {L : Lev (per l K) m} (hL : L.Good) (M : Model l K) {s s' : ℕ} (h : s ≤ s')
  (hQ : ∀ T, QB L M s T → QA L M s (((nmB M hL).mor 0).obj T))
  (hQ' : ∀ T, QB L M s' T → QA L M s' (((nmB M hL).mor 0).obj T))
  (rH : ∀ n j, M.Hc false n j →ₛₗ[L.lam] HM (QA L M s) none ((l : L.A) ^ n) j)
  (rH' : ∀ n j, M.Hc false n j →ₛₗ[L.lam] HM (QA L M s') none ((l : L.A) ^ n) j)

def inclHM (n j : ℕ) : HM (QA L M s') none ((l : L.A) ^ n) j →ₗ[L.A] HM (QA L M s) none ((l : L.A) ^ n) j :=
  ((incl (ts_le L.γ M.p l h {⊤})).sq (a := IdF.top _) (a' := IdF.top _) (fun _ _ _ => trivial)
    (incl_std (ts_le L.γ M.p l h {⊤}) none ((l : L.A) ^ n))).pull j

def homS : Hom (chainOf hL M s' hQ' rH') (chainOf hL M s hQ rH) where
  sΛ := RingHom.id _
  sA := RingHom.id _
  sB := RingHom.id _
  fS n j := LinearMap.id
  fZn n j := inclHM M h n j
  fZ j := (incl (ts_le L.γ M.p l h {⊤})).o.pull j
  fW j := (incl (ts_le L.γB M.q 1 h {⊤})).o.pull j
  fV j := LinearMap.id

end

end CrystallineSemistableComparison.Pb.Kap
