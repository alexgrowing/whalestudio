import Mathlib
import Development.AutomorphicSpectrum.Statements.AlgebraStatements.IsPolarisationOfRelAmple
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.WeilBound.CoreStatements.AbelianHeightsDuality.ZarhinTrick.PolQuasiInverse

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open GlobalTheory.CechPic GlobalTheory.AbDual
open GlobalTheory.IndefiniteRowSideFullHecke.ZeroSectionBase (IsPrincipalPol sqToBase toBase)

attribute [local instance] Over.cartesianMonoidalCategory

namespace PositivityTheory.PrwZar

variable {S : Scheme.{0}} {A B : Over S} [GrpObj A] [GrpObj B]

omit [GrpObj A] [GrpObj B] in

theorem one_comp_prj {G : Over S} [GrpObj G] {Y : Over S} (i : Fin 4) : (1 : Y ⟶ G4 G) ≫ prj G i = 1 := by
  fin_cases i <;> simp [prj]

theorem zc_rigid {P : LB (A ⊗ B).left} (hD : IsDual A B P) (l : A ⟶ B) [IsMonHom l] (mu : B ⟶ A) [IsMonHom mu]
    (α : Matrix (Fin 4) (Fin 4) ℤ) :
    pull (lift (1 : G4 (A ⊗ B) ⟶ G4 (A ⊗ B)) (𝟙 _)).left (zc hD.isLB l mu α) = 0 ∧
      pull (lift (𝟙 _) (1 : G4 (A ⊗ B) ⟶ G4 (A ⊗ B))).left (zc hD.isLB l mu α) = 0 := by
  have e1 : ∀ {Y : Over S} (t : Y ⟶ B), evc hD.isLB (1 : Y ⟶ A) t = 0 :=
    fun t => IsAdditive.evc_one hD.isLB hD.additive t
  have e2 : ∀ {Y : Over S} (a : Y ⟶ A), evc hD.isLB a (1 : Y ⟶ B) = 0 :=
    fun a => evc_one_right hD.isLB hD.zero a
  have o1 : ∀ {Y : Over S} (i : Fin 4) (f : A ⊗ B ⟶ A) [IsMonHom f],
      (1 : Y ⟶ G4 (A ⊗ B)) ≫ prj _ i ≫ f = 1 := by
    intro Y i f _; rw [← Category.assoc, one_comp_prj, MonObj.one_comp]
  have o2 : ∀ {Y : Over S} (i : Fin 4) (f : A ⊗ B ⟶ B) [IsMonHom f],
      (1 : Y ⟶ G4 (A ⊗ B)) ≫ prj _ i ≫ f = 1 := by
    intro Y i f _; rw [← Category.assoc, one_comp_prj, MonObj.one_comp]
  constructor <;>
  · simp only [zc, zcPair, map_add, map_sum, map_nsmul, map_zsmul, pull_evc, lift_fst_assoc, lift_snd_assoc,
      Category.id_comp, o1, o2, e1, e2, smul_zero, add_zero, zero_add, Finset.sum_const_zero]

end PositivityTheory.PrwZar
