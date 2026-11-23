import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.CubePull
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AuxiliaryInertOddPrime
import Development.AbelianVarietyTheory.Statements.HeckeInFamilies.GenericMemChart
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsCoreOfIsAbelianScheme
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.IsSymmetricOfSymmetryGenerator
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

noncomputable section

namespace GlobalTheory.Models.Point

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

local instance isCommMonObj_zero (S : Scheme.{0}) : IsCommMonObj (Out.Inh.zeroPolAV S).A := (Out.Inh.zeroPolAV S).isAb.comm

def zeroTriple (H : Host E) (S : Scheme.{0}) : SAB H S where
  G := (Out.Inh.zeroPolAV S).A
  semi := isSemiAbelian_of_isAbelianScheme _ (Out.Inh.zeroPolAV S).isAb
  act := ⟨fun _ => 𝟙 _, fun _ => inferInstance, rfl, fun _ _ => toUnit_unique _ _, fun _ _ => toUnit_unique _ _⟩
  PP := (UU.CP.triv _).L
  cub := (UU.CP.triv _).c
  sym := isSymmetric_of_symmetry_generator _ _ (UU.CP.triv _).sym_gen (UU.CP.triv _).sym_rig
  adj := fun _ => ⟨⟨fun _ => 1⟩, ZJ.isGen_one_of_g_eq_one _
    (ZJ.div_g_eq_one _ _ (Out.Inh.linComb_triv_g _ _) (Out.Inh.linComb_triv_g _ _))⟩
  prim := ⟨⟨fun _ => 1⟩, ZJ.isGen_one_of_g_eq_one _
    (ZJ.div_g_eq_one _ _ (Out.Inh.linComb_triv_g _ _) fun _ _ => rfl)⟩

theorem abLocus_eq_univ {S : Scheme.{0}} (G : Over S) [IsProper G.hom] : abLocus G = Set.univ :=
  Set.eq_univ_of_forall fun _ _ _ _ _ _ => inferInstance

instance isProper_zeroTriple (H : Host E) (S : Scheme.{0}) : IsProper (zeroTriple H S).G.hom :=
  (Out.Inh.zeroPolAV S).isAb.proper

theorem isProjOver_id (R : Type) [CommRing R] : IsProjOver (𝟙 (Sp R)) := by
  let s : (Out.Inh.trivLB (Sp R)).Sec :=
    ⟨fun _ => 1, fun _ _ =>
      (map_one _).trans ((congrArg₂ (· * ·) rfl (map_one _)).trans (_root_.mul_one _)).symm⟩
  have hs : ⨆ i : Fin (0 + 1), Out.nonzeroLocus ((fun _ => s) i) = ⊤ := by
    simp only [iSup_const, Out.nonzeroLocus, s, Scheme.basicOpen_one]
    exact (Out.Inh.trivLB_isLB _).cover
  have h := ProjSpace.toProj_str (𝟙 (Sp R)) (fun _ => s) hs
  refine ⟨0, _, ?_, h⟩
  have := isProper_str R 0
  have : IsClosedImmersion (ProjSpace.toProj (𝟙 (Sp R)) (fun _ => s) hs ≫ PSpace.str R 0) := by
    rw [h]; infer_instance
  exact IsClosedImmersion.of_comp _ (PSpace.str R 0)

end GlobalTheory.Models.Point

end
