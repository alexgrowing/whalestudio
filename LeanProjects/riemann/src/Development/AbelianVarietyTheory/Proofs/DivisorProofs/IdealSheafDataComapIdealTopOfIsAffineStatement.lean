import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdealSheafDataComapIdealTopOfIsAffine
import Mathlib
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.idealSheafData_comap_ideal_top_of_isAffine : ∀ (X Y : Scheme.{0}) [IsAffine X] [IsAffine Y] (f : X ⟶ Y) (J : Y.IdealSheafData), (J.comap f).ideal ⟨⊤, isAffineOpen_top X⟩ = Ideal.map f.appTop.hom (J.ideal ⟨⊤, isAffineOpen_top Y⟩) := by
  first | exact @GlobalTheory.IdealSheafData.ideal_comap_top_of_isAffine | exact GlobalTheory.IdealSheafData.ideal_comap_top_of_isAffine | (intros; apply GlobalTheory.IdealSheafData.ideal_comap_top_of_isAffine <;> assumption)
