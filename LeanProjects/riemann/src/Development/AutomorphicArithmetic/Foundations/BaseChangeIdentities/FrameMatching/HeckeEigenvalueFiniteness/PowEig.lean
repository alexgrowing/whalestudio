import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.FrameMatching.HeckeEigenvalueFiniteness.PowEigAlt
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalAlgebraHolds

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcB.F.F5 PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.Bc.ArchbcB.B
  PositivityTheory.Rg.BcB.F.Choice PositivityTheory.Rg.BcB.F.Eig PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcN.F2
open scoped Classical

set_option synthInstance.maxHeartbeats 200000

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.HeckeLevelFrameExistence.powEig :
    UpperTheory.HeckeLevelFrameExistence.PowEig := by
  intro E _ _ _ n w σ K' hlev g hg y hy m
  have key : ∀ k : ℕ, IsHecke K' (U.lpow K' g k) ∧ locOp σ K' (U.lpow K' g k) y = y := by
    intro k
    induction k with
    | zero =>
      obtain ⟨-, -, -, -, -, -, h1, h2⟩ := GlobalTheory.CompanionTheory.LocHecke.locAlg E n w σ K' hlev g g hg hg
      refine ⟨h1, ?_⟩
      show locOp σ K' ((K' : Set (UL n w)).indicator fun _ => ((K'.relIndex (KL n w) : ℕ) : ℂ)) y = y
      rw [h2]
      rfl
    | succ k ih =>
      obtain ⟨-, -, h3, -, h5, -⟩ := GlobalTheory.CompanionTheory.LocHecke.locAlg E n w σ K' hlev g _ hg ih.1
      refine ⟨h3, ?_⟩
      show locOp σ K' (lconv g (U.lpow K' g k)) y = y
      rw [h5, Module.End.mul_apply, ih.2, hy]
  exact (key m).2
