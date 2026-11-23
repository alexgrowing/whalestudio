import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.SubThickRees
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.LimitBilinearCup.CupAbs

set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory GlobalTheory.LogCris

namespace CrystallineSemistableComparison.CupAbs

variable {b b' : Base} {L : b.Fun} {L' : b'.Fun} {σ : b.R →+* b'.R} (m : GlobalTheory.LogCris.Mor L L' σ) {Λ Λ' : Type}
  [CommRing Λ] [CommRing Λ'] {c : Λ →+* b.R} {c' : Λ' →+* b'.R} (σ₀ : Λ →+* Λ') (h : ∀ a, σ (c a) = c' (σ₀ a))

theorem om_cup {p q n : ℕ} (e : p + q = n) (x : CH.H (B.OM L c) p) (y : CH.H (B.OM L c) q) :
    (B.omMor m σ₀ h).pull n ((CH.mulP (B.OA L c)).cup e x y) =
      (CH.mulP (B.OA L' c')).cup e ((B.omMor m σ₀ h).pull p x) ((B.omMor m σ₀ h).pull q y) :=
  P.cup_pull (CH.mulP (B.OA L c)) (CH.mulP (B.OA L' c')) (B.omMor m σ₀ h).G (B.omMor m σ₀ h).τ (B.omMor m σ₀ h).τ
    (B.omMor m σ₀ h).τ (B.omMor m σ₀ h).nat (B.omMor m σ₀ h).nat (B.omMor m σ₀ h).nat (fun _ _ _ => rfl) e x y

theorem om_one : (B.omMor m σ₀ h).pull 0 (CH.oneH (B.OA L c)) = CH.oneH (B.OA L' c') :=
  pull_one (B.omMor m σ₀ h) (fun _ => rfl)

end CrystallineSemistableComparison.CupAbs
