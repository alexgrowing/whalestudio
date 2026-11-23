import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.IsCrystallineChernClassLimit
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.LimitBilinearCup.CupAbs
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.LimitBilinearCup.OmCup
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

noncomputable section

open CategoryTheory TensorProduct

namespace CrystallineSemistableComparison

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

namespace PlusCup

def lev (r : Res l K) (M : Model l K) (i j m : ℕ) :
    (Wc.HS l (B.schFn M.p) r.ρ i).M m →ₗ[WittVector l r.k] (Wc.HS l (B.schFn M.p) r.ρ j).M m →ₗ[WittVector l r.k]
      (Wc.HS l (B.schFn M.p) r.ρ (i + j)).M m :=
  (P.cup_bilin (CH.mulP (Wc.OA l (B.schFn M.p) r.ρ m)) (rfl : i + j = i + j)).choose

theorem lev_eq (r : Res l K) (M : Model l K) (i j m : ℕ) (x : (Wc.HS l (B.schFn M.p) r.ρ i).M m)
    (y : (Wc.HS l (B.schFn M.p) r.ρ j).M m) :
    lev r M i j m x y = (CH.mulP (Wc.OA l (B.schFn M.p) r.ρ m)).cup rfl x y :=
  (P.cup_bilin (CH.mulP (Wc.OA l (B.schFn M.p) r.ρ m)) (rfl : i + j = i + j)).choose_spec x y

theorem lev_comm (r : Res l K) (M : Model l K) (i j m : ℕ) (x : (Wc.HS l (B.schFn M.p) r.ρ i).M (m + 1))
    (y : (Wc.HS l (B.schFn M.p) r.ρ j).M (m + 1)) :
    (Wc.HS l (B.schFn M.p) r.ρ (i + j)).r m (lev r M i j (m + 1) x y) =
      lev r M i j m ((Wc.HS l (B.schFn M.p) r.ρ i).r m x) ((Wc.HS l (B.schFn M.p) r.ρ j).r m y) := by
  rw [lev_eq, lev_eq]
  exact CupAbs.om_cup (Wc.redM l (B.schFn M.p) r.ρ m) (RingHom.id _) (Wc.red_mk l r.k m) rfl x y

def limCup (r : Res l K) (M : Model l K) (i j : ℕ) :
    Pb.Lim r M i →ₗ[WittVector l r.k] Pb.Lim r M j →ₗ[WittVector l r.k] Pb.Lim r M (i + j) :=
  CupAbs.limBil (lev r M i j) (lev_comm r M i j)

end PlusCup

open PlusCup in

theorem cupEx : CupEx := by
  intro l _ K r
  refine ⟨fun M i j => CupAbs.bc (Wc.K₀ l r.k) (limCup r M i j), fun M i j x y =>
    ⟨limCup r M i j x y, fun m => ?_, ?_⟩⟩
  · exact (CupAbs.limBil_apply _ _ x y m).trans (lev_eq r M i j m _ _)
  · exact CupAbs.bc_tmul _ _ _ _

theorem limOne_ex (r : Res l K) (M : Model l K) : ∃ x, Pb.LimOne r M x :=
  ⟨⟨fun m => CH.oneH (Wc.OA l (B.schFn M.p) r.ρ m),
    fun m => CupAbs.om_one (Wc.redM l (B.schFn M.p) r.ρ m) (RingHom.id _) (Wc.red_mk l r.k m)⟩, fun _ => rfl⟩

end CrystallineSemistableComparison
