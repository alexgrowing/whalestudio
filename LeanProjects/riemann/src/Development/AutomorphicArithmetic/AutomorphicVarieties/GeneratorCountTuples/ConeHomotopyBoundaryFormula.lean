import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.LeftMultiplication.Lmul
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.ToInhPartialProd
open UpperTheory.V.ZK UpperTheory.V.ZK.PM

private theorem hp_eq (A : Type) [CommRing A] (G : Type) [Group G] (k : G) :
    ∀ (m : ℕ) (z : Ch A G m), hp A k m z = hprism A (· * k) m z
  | 0, z => by rw [hprism_zero]; rfl
  | m + 1, z => ch_ext A (fun x => by
      have h := hprism_cone A (· * k) (x 0) m (Finsupp.single (Fin.tail (α := fun _ => G) x) 1)
      rw [← hmap_cone A (· * k), cone_single, Fin.cons_self_tail] at h
      rw [h, hp, Finsupp.linearCombination_single, one_smul, hp_eq A G k m, map_sub]
      rfl) z

theorem UpperTheory.coneHomotopy_boundary_formula :
    ∀ (A : Type) [CommRing A] (G : Type) [Group G] (k : G) (m : ℕ) (z : Ch A G (m + 1)), pr A G (m + 1) (hp A k (m + 1) z) = prism A k m (pr A G m z) := by
  intro A _ G _ k m z
  rw [hp_eq]
  exact (prism_toInh A k m z).symm
