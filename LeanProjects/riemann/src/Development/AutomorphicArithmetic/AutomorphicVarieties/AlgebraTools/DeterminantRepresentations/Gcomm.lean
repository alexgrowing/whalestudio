import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DComm
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DkerOfKills
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DToDet

open Polynomial UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.CA

theorem UpperTheory.V.AlgebraTools.Det.gcomm :
    ∀ {n : ℕ} {A G : Type} [CommRing A] [Group G] (D : GDet n A G),
    (∀ (B : Type) [CommRing B] [Algebra A B] (x y : MonoidAlgebra B G), D.D B (1 + x * y) = D.D B (1 + y * x)) ∧
    ∃ I : TwoSidedIdeal (MonoidAlgebra A G), ∀ y, y ∈ I ↔ D.Kills y := by
  intro n A G _ _ D
  refine ⟨fun B _ _ x y => ?_, D.toDet.ker, fun y =>
    (UpperTheory.V.CA.d_ker D.toDet y).1.trans (UpperTheory.V.CA.d_toDet D y).2.2.2⟩
  have h := UpperTheory.V.CA.d_comm D.toDet B (toT A G B x) (toT A G B y)
  change D.D B (ofT A G B _) = D.D B (ofT A G B _) at h
  simpa only [map_add, map_one, map_mul, ofT_toT] using h
