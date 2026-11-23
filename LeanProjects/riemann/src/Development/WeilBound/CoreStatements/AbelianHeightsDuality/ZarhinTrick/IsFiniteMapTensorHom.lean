import Mathlib
import Development.AutomorphicSpectrum.Statements.AlgebraStatements.IsPolarisationOfRelAmple
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.WeilBound.CoreStatements.AbelianHeightsDuality.ZarhinTrick.FibAmpleD
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.TensorMapFiniteOfSplit
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.RelAmpleExternalTensorPowerGroupPower
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.RelAmpleFormBundlePowerOfPosDef

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open GlobalTheory.CechPic GlobalTheory.AbDual
open GlobalTheory.IndefiniteRowSideFullHecke.ZeroSectionBase (IsPrincipalPol sqToBase toBase)

attribute [local instance] Over.cartesianMonoidalCategory

namespace PositivityTheory.PrwZar.XB

variable {S : Scheme.{0}}

def pr8 (A : Over S) : Fin 8 → (G4 (A ⊗ A) ⟶ A)
  | 0 => prj (A ⊗ A) 0 ≫ fst A A
  | 1 => prj (A ⊗ A) 0 ≫ snd A A
  | 2 => prj (A ⊗ A) 1 ≫ fst A A
  | 3 => prj (A ⊗ A) 1 ≫ snd A A
  | 4 => prj (A ⊗ A) 2 ≫ fst A A
  | 5 => prj (A ⊗ A) 2 ≫ snd A A
  | 6 => prj (A ⊗ A) 3 ≫ fst A A
  | 7 => prj (A ⊗ A) 3 ≫ snd A A

def lim8 (A : Over S) : IsLimit (Fan.mk (G4 (A ⊗ A)) (pr8 A)) :=
  mkFanLimit _ (fun s => fourfoldProductLift ![lift (s.proj 0) (s.proj 1), lift (s.proj 2) (s.proj 3),
      lift (s.proj 4) (s.proj 5), lift (s.proj 6) (s.proj 7)])
    (fun s k => by fin_cases k <;> simp [pr8, fourfoldProductLift, prj])
    (fun s m hm => by
      have h0 : m ≫ pr8 A 0 = s.proj 0 := hm 0
      have h1 : m ≫ pr8 A 1 = s.proj 1 := hm 1
      have h2 : m ≫ pr8 A 2 = s.proj 2 := hm 2
      have h3 : m ≫ pr8 A 3 = s.proj 3 := hm 3
      have h4 : m ≫ pr8 A 4 = s.proj 4 := hm 4
      have h5 : m ≫ pr8 A 5 = s.proj 5 := hm 5
      have h6 : m ≫ pr8 A 6 = s.proj 6 := hm 6
      have h7 : m ≫ pr8 A 7 = s.proj 7 := hm 7
      simp only [pr8, prj, ← Category.assoc] at h0 h1 h2 h3 h4 h5 h6 h7
      refine CartesianMonoidalCategory.hom_ext _ _ (CartesianMonoidalCategory.hom_ext _ _ ?_ ?_)
        (CartesianMonoidalCategory.hom_ext _ _ (CartesianMonoidalCategory.hom_ext _ _ ?_ ?_)
          (CartesianMonoidalCategory.hom_ext _ _ (CartesianMonoidalCategory.hom_ext _ _ ?_ ?_)
            (CartesianMonoidalCategory.hom_ext _ _ ?_ ?_))) <;>
        simp [fourfoldProductLift, ← h0, ← h1, ← h2, ← h3, ← h4, ← h5, ← h6, ← h7])

variable {T : Scheme.{0}} (s : T ⟶ S)

theorem isFinite_map_tensorHom {X Y X' Y' : Over S} (f : X ⟶ Y) (g : X' ⟶ Y')
    (hf : IsFinite ((Over.pullback s).map f).left) (hg : IsFinite ((Over.pullback s).map g).left) :
    IsFinite ((Over.pullback s).map (f ⊗ₘ g)).left := by
  set F := Over.pullback s
  have he : F.map (f ⊗ₘ g) =
      CartesianMonoidalCategory.prodComparison F X X' ≫ (F.map f ⊗ₘ F.map g) ≫
        inv (CartesianMonoidalCategory.prodComparison F Y Y') := by
    rw [← Category.assoc, ← CartesianMonoidalCategory.prodComparison_natural, Category.assoc,
      IsIso.hom_inv_id, Category.comp_id]
  have ht : IsFinite (Over.Hom.left (F.map f ⊗ₘ F.map g)) :=
    GlobalTheory.TensorFinite.isFinite_tensorHom _ _ hf hg
  haveI : IsIso (CartesianMonoidalCategory.prodComparison F X X') :=
    CartesianMonoidalCategory.isIso_prodComparison_of_preservesLimit_pair F X X'
  haveI : IsIso (CartesianMonoidalCategory.prodComparison F Y Y') :=
    CartesianMonoidalCategory.isIso_prodComparison_of_preservesLimit_pair F Y Y'
  haveI : IsIso (Over.Hom.left (CartesianMonoidalCategory.prodComparison F X X')) :=
    (Over.forget T).map_isIso (CartesianMonoidalCategory.prodComparison F X X')
  haveI : IsIso (Over.Hom.left (inv (CartesianMonoidalCategory.prodComparison F Y Y'))) :=
    (Over.forget T).map_isIso (inv (CartesianMonoidalCategory.prodComparison F Y Y'))
  have h1 : IsFinite (Over.Hom.left (CartesianMonoidalCategory.prodComparison F X X')) := inferInstance
  have h2 : IsFinite (Over.Hom.left (inv (CartesianMonoidalCategory.prodComparison F Y Y'))) :=
    inferInstance
  rw [he, Over.comp_left, Over.comp_left]
  exact MorphismProperty.comp_mem @IsFinite _ _ h1 (MorphismProperty.comp_mem @IsFinite _ _ ht h2)

end PositivityTheory.PrwZar.XB
