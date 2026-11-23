import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.CechDifferentialPullback.Bridge

set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite Limits GroundTheory.Arith.SchemeCoh GlobalTheory.SheafPull CrystallineSemistableComparison CrystallineSemistableComparison.Om CrystallineSemistableComparison.Om.Cech

namespace GlobalTheory.CompanionTheory.OmCech

theorem cechOmAdd_smul {K : Type} [Field K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) {ι : Type}
    (U : ι → X.Opens) (hU : iSup U = ⊤) (hUaff : ∀ (n : ℕ) (i : Fin (n + 1) → ι), IsAffineOpen (⨅ a, U (i a)))
    (a j : ℕ) (r : K) (x : CO q U a j) :
    cechOmAdd q U hU hUaff a j (r • x) = r • cechOmAdd q U hU hUaff a j x := by
  letI := GlobalTheory.HodgeCoh.algΓ q
  apply (GlobalTheory.coh.toH (GlobalTheory.HodgeCoh.Omega q a) j).injective
  have h1 : ∀ z : CO q U a j, GlobalTheory.coh.toH (GlobalTheory.HodgeCoh.Omega q a) j (cechOmAdd q U hU hUaff a j z) =
      cechHAddEquivH.{0} U hU hUaff (GlobalTheory.HodgeCoh.Omega q a) j z :=
    fun z => (GlobalTheory.coh.toH (GlobalTheory.HodgeCoh.Omega q a) j).apply_symm_apply _
  have h2 := cechHAddEquivH_naturality.{0} U hU hUaff
    (smulHom (GlobalTheory.HodgeCoh.Omega q a) (algebraMap K Γ(X, ⊤) r)) j x
  have h3 := GlobalTheory.coh.toH_map K (smulHom (GlobalTheory.HodgeCoh.Omega q a) (algebraMap K Γ(X, ⊤) r)) j
    (cechOmAdd q U hU hUaff a j x)
  rw [h1] at h3 ⊢
  exact h2.trans h3.symm

end GlobalTheory.CompanionTheory.OmCech
