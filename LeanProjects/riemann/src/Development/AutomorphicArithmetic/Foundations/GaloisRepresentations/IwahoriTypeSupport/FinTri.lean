import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IwahoriTypeSupport.TorusScalar
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BlockIndexMonotone

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel Matrix UpperTheory.Gal.TypesAndIwahori

theorem UpperTheory.Gal.TypesAndIwahori.finTri :
    UpperTheory.Gal.TypesAndIwahori.FinTri := by
  intro R _ N s d hd h hh
  have hp : h ∈ parab R (stdBlocks d hd) := by
    rw [mem_parab_iff]
    intro a b i j hba
    exact hh _ _ (GlobalTheory.CompanionTheory.BlockIndex.stdBlocks_lt_of_lt d hd hba i j)
  refine ⟨hp, fun a => ?_⟩
  rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_of_upperTriangular]
  · apply Finset.prod_congr rfl
    intro j _
    exact leviProj_apply R (stdBlocks d hd) ⟨h, hp⟩ a j j
  · intro i j hij
    rw [leviProj_apply]
    apply hh
    have hij' : (j : ℕ) < (i : ℕ) := hij
    rw [Fin.lt_def, stdBlocks_val, stdBlocks_val]
    omega
