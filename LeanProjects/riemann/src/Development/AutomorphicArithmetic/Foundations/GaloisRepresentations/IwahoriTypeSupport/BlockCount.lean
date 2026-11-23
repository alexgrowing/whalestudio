import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IwahoriTypeSupport.TorusScalar

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel Matrix UpperTheory.Gal.TypesAndIwahori

theorem UpperTheory.Gal.TypesAndIwahori.blockCount :
    UpperTheory.Gal.TypesAndIwahori.BlockCount := by
  intro β N s d hd θ
  have hsum : Multiset.map (fun i => θ (blockOf d hd i)) Finset.univ.val =
      ∑ i, ({θ (blockOf d hd i)} : Multiset β) := by
    rw [← Multiset.sum_map_singleton (Multiset.map _ _), Multiset.map_map]
    rfl
  rw [hsum, ← (stdBlocks d hd).sum_comp, Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp [blockOf, Multiset.nsmul_singleton]
