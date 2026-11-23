import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.RestrictionInclusions.RHofIncl
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.CrSEqOne

set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false

noncomputable section

set_option maxHeartbeats 1000000

open CategoryTheory AlgebraicGeometry Limits GlobalTheory.LogCris DividedPowers

namespace CrystallineSemistableComparison.Pb.Kap

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}
namespace RestrictedLevelComparison

theorem pullHc_id (M : Model l K) (n j : ℕ) (x : M.Hc false n j) :
    B.pullHc (okToOC l K) (B.schMap (𝟙 M.X) (Category.id_comp _)) false n j x = x := by
  refine (CrystallineSemistableComparison.cr_pull_eq (B.pullMorC (okToOC l K) (B.schMap (𝟙 M.X) (Category.id_comp M.p)) false n) (CH.Mor.id _)
    (fun T => CrystallineSemistableComparison.crHom (RingHom.id T.B) (fun _ => rfl) (DPMorphism.id T.δ).isDPMorphism
      (fun h => (CrystallineSemistableComparison.pt_id _ h _).trans (by first | exact Category.comp_id (C := Scheme.{0}) _ | (change _ ≫ 𝟙 M.X = _; exact Category.comp_id _) | erw [Category.comp_id] | rfl))) (fun _ _ => rfl) (fun _ _ => rfl) j x).trans ?_
  exact (CrystallineSemistableComparison.P.pull_comp (CH.Mor.id _) (CH.Mor.id _) j x).2

end RestrictedLevelComparison

variable (S : LevSys (per l K)) (hS : S.Good) (hC : ∀ m, (S.L m).CrisOK)

namespace RestrictedLevelComparison

theorem dOf_lev (m n : ℕ) (y : (PAlg.base l).Acr n) :
    (dOf S hS hC m n).ρ y = lnMap (S.dA m) l le_rfl ((dOf S hS hC (m + 1) n).ρ y) := by
  obtain ⟨c, rfl⟩ := ((RL.base_acr (PAlg.base l) PAlg.isBase_base).2 n).1 y
  rw [hcOf, hcOf, ← hS.dlam m c]
  exact Ideal.quotientMap_mk.symm

end RestrictedLevelComparison

theorem rHof_lev (M : Model l K) (m s n j : ℕ) (x : M.Hc false n j) :
    nmHM (nmLevA S hS m M) l s none n j (rHof (dOf S hS hC (m + 1)) (hcOf S hS hC (m + 1)) M s n j x) =
      rHof (dOf S hS hC m) (hcOf S hS hC m) M s n j x := by
  have hcomp := RestrictedLevelComparison.dOf_lev S hS hC m n
  have e : nmHM (nmLevA S hS m M) l s none n j (rHof (dOf S hS hC (m + 1)) (hcOf S hS hC (m + 1)) M s n j x) =
      rHof (dOf S hS hC m) (hcOf S hS hC m) M s n j
        (B.pullHc (okToOC l K) (B.schMap (𝟙 M.X) (Category.id_comp _)) false n j x) :=
    (red_nm (dOf S hS hC (m + 1) n) (dOf S hS hC m n) s (nmLevA S hS m M) _ _ _ _ _ (hcOf S hS hC (m + 1) n)
      (hcOf S hS hC m n) _ _ (fun _ _ => rfl) hcomp none j x).symm
  exact e.trans (congrArg (rHof (dOf S hS hC m) (hcOf S hS hC m) M s n j) (RestrictedLevelComparison.pullHc_id M n j x))

end CrystallineSemistableComparison.Pb.Kap
