import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdealSheafComapIdealAffineOpenOfIsAffine
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdealSheafDataComapIdealTopOfIsAffine
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.idealSheaf_comap_ideal_affineOpen_of_isAffine : ∀ {X Y : Scheme.{0}} [IsAffine Y] (f : X ⟶ Y) (K : Y.IdealSheafData) (W : X.affineOpens), (K.comap f).ideal W = Ideal.map (f.appLE ⊤ W (by simp)).hom (K.ideal ⟨⊤, isAffineOpen_top Y⟩) := by
  first | (exact @GlobalTheory.IdealSheafData.ideal_comap_affineOpen_of_isAffine) | (exact GlobalTheory.IdealSheafData.ideal_comap_affineOpen_of_isAffine) | (intros; apply GlobalTheory.IdealSheafData.ideal_comap_affineOpen_of_isAffine  <;> assumption)
