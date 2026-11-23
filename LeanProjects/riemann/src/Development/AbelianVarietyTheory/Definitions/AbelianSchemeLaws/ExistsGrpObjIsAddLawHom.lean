import Mathlib
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.OpensRangeChartYSupOpensRangeChartZ
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.ExistsLiftAddOfIsReducedEq
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.AddXYZOrChordXYZOrOriginXYZNeZero
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.HomExtOfLocalRingPoints
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsEqPtHomOfIsLocalRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.EigLatBasis

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.WeierstrassCurve GlobalTheory.AddLaw

namespace GlobalTheory.WeierstrassCurve

variable {R : Type} [CommRing R] (W : _root_.WeierstrassCurve R)

def IsAddLawHom (m : schemeOver W ⊗ schemeOver W ⟶ schemeOver W) : Prop :=
  ∀ (A : Type) [CommRing A] (ρ : R →+* A) (P Q T : Fin 3 → A)
    (hP : IsUnimodularSol (W.map ρ) P) (hQ : IsUnimodularSol (W.map ρ) Q)
    (hT : IsUnimodularSol (W.map ρ) T),
    (Proportional T ((W.map ρ).toProjective.addXYZ P Q) ∧
      Proportional T (diagXYZ (W.map ρ).toProjective P Q)) →
    ∀ x y : Over.mk (spMap ρ) ⟶ schemeOver W, x.left = ptHom W ρ P hP →
      y.left = ptHom W ρ Q hQ → (lift x y ≫ m).left = ptHom W ρ T hT

variable [W.IsElliptic]

theorem isAddLawHom_mul : IsAddLawHom W μ[schemeOver W] := by
  intro A _ ρ P Q T hP hQ hT h x y hx hy
  let : Algebra R A := ρ.toAlgebra
  obtain rfl : x = ptOver W (A := A) P hP := Over.OverMorphism.ext hx
  obtain rfl : y = ptOver W (A := A) Q hQ := Over.OverMorphism.ext hy
  exact congrArg (·.left) (ptOver_mul_ptOver W (A := A) hP hQ hT ⟨h.1, h.2⟩)

theorem IsAddLawHom.unique {m m' : schemeOver W ⊗ schemeOver W ⟶ schemeOver W}
    (h : IsAddLawHom W m) (h' : IsAddLawHom W m') : m = m' := by
  refine Over.OverMorphism.ext ?_
  refine hom_ext_of_localRing_points _ _ _ _
    fun A _ _ (t : Sp A ⟶ (schemeOver W ⊗ schemeOver W).left) => ?_
  obtain ⟨g, hg⟩ := Spec.map_surjective (t ≫ (schemeOver W ⊗ schemeOver W).hom)
  obtain ⟨ρ, hρ⟩ : ∃ ρ : R →+* A, t ≫ (schemeOver W ⊗ schemeOver W).hom = spMap ρ :=
    ⟨g.hom, hg.symm⟩
  let t' : Over.mk (spMap ρ) ⟶ schemeOver W ⊗ schemeOver W := Over.homMk t hρ
  obtain ⟨P, hP, eP⟩ := exists_eq_ptHom_of_isLocalRing R W A ρ (t' ≫ fst _ _).left
    (Over.w (t' ≫ fst _ _))
  obtain ⟨Q, hQ, eQ⟩ := exists_eq_ptHom_of_isLocalRing R W A ρ (t' ≫ snd _ _).left
    (Over.w (t' ≫ snd _ _))
  let : Algebra R A := ρ.toAlgebra
  obtain ⟨S, hS, hS', -⟩ := exists_ptOver_mul_ptOver_eq W (A := A) hP hQ
  have hs : IsSumTriple (W.map ρ) P Q S := by
    rcases hS' with rfl | rfl
    exacts [isSumTriple_addXYZ hP.equation hQ.equation, isSumTriple_diagXYZ hP.equation hQ.equation]
  have e := h A ρ P Q S hP hQ hS ⟨hs.add, hs.diag⟩ _ _ eP eQ
  have e' := h' A ρ P Q S hP hQ hS ⟨hs.add, hs.diag⟩ _ _ eP eQ
  rw [lift_comp_fst_snd] at e e'
  exact e.trans e'.symm

theorem ptHom_grpObj_inv {A : Type} [CommRing A] (ρ : R →+* A) (P : Fin 3 → A)
    (hP : IsUnimodularSol (W.map ρ) P) :
    ptHom W ρ P hP ≫ (GrpObj.inv : schemeOver W ⟶ schemeOver W).left = ptHom W ρ _ hP.neg :=
  (congrArg (_ ≫ ·) (inv_left W)).trans (ptHom_negHom W ρ P hP)

omit [W.IsElliptic] in

theorem exists_grpObj_isAddLawHom (hΔ : IsUnit W.Δ) :
    ∃ _ : GrpObj (schemeOver W), IsCommMonObj (schemeOver W) ∧ η[schemeOver W].left = zero W ∧
      IsAddLawHom W μ[schemeOver W] ∧
      ∀ (A : Type) [CommRing A] (ρ : R →+* A) (P : Fin 3 → A) (hP : IsUnimodularSol (W.map ρ) P),
        ∃ hN : IsUnimodularSol (W.map ρ) ((W.map ρ).toProjective.neg P),
          ptHom W ρ P hP ≫ (GrpObj.inv : schemeOver W ⟶ schemeOver W).left = ptHom W ρ _ hN :=
  haveI : W.IsElliptic := ⟨hΔ⟩
  ⟨grpObj W, isCommMonObj W, one_left W, isAddLawHom_mul W,
    fun _ _ ρ P hP => ⟨hP.neg, ptHom_grpObj_inv W ρ P hP⟩⟩

end GlobalTheory.WeierstrassCurve
