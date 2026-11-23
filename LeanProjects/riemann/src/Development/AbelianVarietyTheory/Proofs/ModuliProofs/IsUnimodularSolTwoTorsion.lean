import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AuxiliaryInertOddPrime
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.ExistsRetractTensorTriple
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeSchemeOver
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsCommGrpObjWeierstrassScheme
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.PtHomEqPtHomIffProportional
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

namespace GlobalTheory.Models.EllipticModel

open GlobalTheory.WeierstrassCurve

noncomputable def curve : _root_.WeierstrassCurve ℤ_[3] := ⟨0, 0, 0, -1, 0⟩

theorem isUnit_curve_Δ : IsUnit curve.Δ := by
  have h : curve.Δ = ((64 : ℤ) : ℤ_[3]) := by
    simp only [curve, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
      WeierstrassCurve.b₈]
    norm_num
  rw [h, PadicInt.isUnit_iff]
  refine le_antisymm (PadicInt.norm_le_one _) (not_lt.1 fun hlt => ?_)
  rw [PadicInt.norm_int_lt_one_iff_dvd] at hlt
  revert hlt
  norm_num

theorem isUnimodularSol_origin : IsUnimodularSol (curve.map (RingHom.id _)) ![0, 1, 0] := by
  refine ⟨?_, (Ideal.eq_top_iff_one _).2 (Ideal.subset_span ⟨1, rfl⟩)⟩
  rw [WeierstrassCurve.Projective.equation_iff]
  simp

theorem isUnimodularSol_twoTorsion : IsUnimodularSol (curve.map (RingHom.id _)) ![0, 0, 1] := by
  refine ⟨?_, (Ideal.eq_top_iff_one _).2 (Ideal.subset_span ⟨2, rfl⟩)⟩
  rw [WeierstrassCurve.Projective.equation_iff]
  simp [curve]

theorem not_mono_toSpec : ¬ Mono (toSpec curve) := by
  intro hm
  have h : ptHom curve (RingHom.id _) _ isUnimodularSol_origin =
      ptHom curve (RingHom.id _) _ isUnimodularSol_twoTorsion := by
    rw [← cancel_mono (toSpec curve), ptHom_toSpec, ptHom_toSpec]
  have h' := (GlobalTheory.AddLaw.ptHom_eq_ptHom_iff_proportional _ curve _ _ _ _ _ _).1 h 1 2
  simp at h'

theorem not_isIso_tensorTriple {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) {X : Scheme.{0}}
    (A : Over X) [GrpObj A] [IsCommMonObj A] (hA : IsAbelianScheme A) (h : ¬ Mono A.hom) :
    ¬ IsIso (tensorTriple H A hA).G.hom := by
  intro hi
  obtain ⟨i, r, hir⟩ := exists_retract_tensorTriple (H := H) A hA
  have e : i.left ≫ r.left = 𝟙 A.left := by rw [← Over.comp_left, hir, Over.id_left]
  have : Mono i.left := mono_of_mono_fac e
  exact h (Over.w i ▸ inferInstance)

end GlobalTheory.Models.EllipticModel
