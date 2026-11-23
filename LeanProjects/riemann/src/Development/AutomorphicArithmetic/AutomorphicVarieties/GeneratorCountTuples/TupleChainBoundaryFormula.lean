import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.LeftMultiplication.Lmul
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.ToInhPartialProd
open UpperTheory.V.ZK UpperTheory.V.ZK.PM

private theorem hbd_eq (A : Type) [CommRing A] (G : Type) [Group G] :
    ∀ (m : ℕ) (z : Ch A G (m + 1)), PM.hbd A G m z = UpperTheory.V.ZK.hbd A G m z
  | 0, z => ch_ext A (fun x => by
      have h := hbd_cone_zero A (x 0) (Finsupp.single (Fin.tail (α := fun _ => G) x) 1)
      rw [cone_single, Fin.cons_self_tail] at h
      rw [h, PM.hbd, Finsupp.linearCombination_single, one_smul]) z
  | m + 1, z => ch_ext A (fun x => by
      have h := hbd_cone A (x 0) m (Finsupp.single (Fin.tail (α := fun _ => G) x) 1)
      rw [cone_single, Fin.cons_self_tail] at h
      rw [h, PM.hbd, Finsupp.linearCombination_single, one_smul, hbd_eq A G m]
      rfl) z

theorem UpperTheory.tupleChain_boundary_formula :
    ∀ (A : Type) [CommRing A] (G : Type) [Group G] (m : ℕ) (z : Ch A G (m + 2)), bd A G m (pr A G (m + 1) z) = pr A G m (PM.hbd A G (m + 1) z) := by
  intro A _ G _ m z
  rw [hbd_eq]
  exact bd_toInh A m z
