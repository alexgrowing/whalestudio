import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.CechDifferentialPullback.Bridge

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite Limits

namespace CrystallineSemistableComparison.Om.Cech

open GroundTheory.Arith.SchemeCoh GlobalTheory.SheafPull

theorem hPull_omega_pf : ∀ {K : Type} [Field K] {X Y : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K))
    (p : Y ⟶ Spec (CommRingCat.of K)) (u : X ⟶ Y) (hu : u ≫ p = q) (a j : ℕ)
    (y : Sheaf.H.{0} ((GlobalTheory.toAbSheaf Y).obj (GlobalTheory.HodgeCoh.Omega p a)) j),
    (GlobalTheory.coh.toH (GlobalTheory.HodgeCoh.Omega q a) j).symm (hPull u.base (GlobalTheory.toAbSheafPush (GlobalTheory.HodgeCoh.omegaPull hu a)) j y) =
      pullC u hu a j ((GlobalTheory.coh.toH (GlobalTheory.HodgeCoh.Omega p a) j).symm y) := by
  intro K _ X Y q p u hu a j y
  apply (GlobalTheory.coh.toH (GlobalTheory.HodgeCoh.Omega q a) j).injective
  rw [AddEquiv.apply_symm_apply]
  obtain ⟨w, rfl⟩ := (GlobalTheory.SiteCoh.terminalEquiv ((GlobalTheory.toAbSheaf Y).obj (GlobalTheory.HodgeCoh.Omega p a)) j
    isTerminalTop).surjective y
  obtain ⟨z, rfl⟩ := (GlobalTheory.cohOn.toH' (GlobalTheory.HodgeCoh.Omega p a) ⊤ j).surjective w
  have hz : (GlobalTheory.coh.toH (GlobalTheory.HodgeCoh.Omega p a) j).symm
      (GlobalTheory.SiteCoh.terminalEquiv _ j isTerminalTop (GlobalTheory.cohOn.toH' _ ⊤ j z)) = z :=
    (GlobalTheory.coh.toH (GlobalTheory.HodgeCoh.Omega p a) j).symm_apply_apply z
  rw [hz]
  change GlobalTheory.SiteCoh.terminalEquiv _ j isTerminalTop
      (GlobalTheory.SheafPull.pull u.base (GlobalTheory.toAbSheafPush (GlobalTheory.HodgeCoh.omegaPull hu a)) j (homOfLE le_top)
        ((GlobalTheory.SiteCoh.terminalEquiv _ j isTerminalTop).symm
          (GlobalTheory.SiteCoh.terminalEquiv _ j isTerminalTop (GlobalTheory.cohOn.toH' _ ⊤ j z)))) =
    GlobalTheory.SiteCoh.terminalEquiv _ j isTerminalTop (GlobalTheory.cohOn.toH' _ _ j (GlobalTheory.HodgeCoh.hodgePull hu a j z))
  rw [AddEquiv.symm_apply_apply]
  congr 1

end CrystallineSemistableComparison.Om.Cech
