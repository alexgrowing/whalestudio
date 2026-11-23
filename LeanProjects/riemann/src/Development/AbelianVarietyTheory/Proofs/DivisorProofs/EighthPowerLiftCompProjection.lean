import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnifAfterFin
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.E8invTranspose
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsGoodModelOfPowQuotient

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Mum.Pow8

variable {S : Scheme.{0}} (G : Over S) [GrpObj G] [IsCommMonObj G]

abbrev G8 : Over S := powObj G 8

abbrev pr8 (i : Fin 8) : G8 G ⟶ G := powPr G i

def mk8 {T : Over S} (x : Fin 8 → (T ⟶ G)) : T ⟶ G8 G := (powIsLimit G 8).lift (Fan.mk T x)

theorem eighthPowerLift_comp_projection {T : Over S} (x : Fin 8 → (T ⟶ G)) (i : Fin 8) : mk8 G x ≫ pr8 G i = x i :=
  (powIsLimit G 8).fac (Fan.mk T x) ⟨i⟩

theorem eighthPowerGroupObj_hom_ext {T : Over S} {x y : T ⟶ G8 G} (h : ∀ i, x ≫ pr8 G i = y ≫ pr8 G i) : x = y :=
  (powIsLimit G 8).hom_ext fun ⟨i⟩ => h i

def matAct (a : Matrix (Fin 8) (Fin 8) ℤ) : G8 G ⟶ G8 G := mk8 G fun i => ∏ j, pr8 G j ^ a i j

theorem matAct_pr (a : Matrix (Fin 8) (Fin 8) ℤ) (i : Fin 8) : matAct G a ≫ pr8 G i = ∏ j, pr8 G j ^ a i j :=
  eighthPowerLift_comp_projection G _ i

def inc8 : G ⟶ G8 G := mk8 G fun i => if i = 0 then 𝟙 G else 1

def L8 (PP : LB (G2 G).left) : LB (G8 G).left :=
  LB.LinComb PP (K := Fin 8 × Fin 8) (fun ij => (lift (pr8 G ij.1) (pr8 G ij.2) : G8 G ⟶ G2 G).left)
    (fun ij => GlobalTheory.W8 ij.1 ij.2)

theorem matAct_hom (a : Matrix (Fin 8) (Fin 8) ℤ) : IsMonHom (matAct G a) :=
  Serre.isMonHom_of_mul_comp _ fun T x y => eighthPowerGroupObj_hom_ext G fun k => by
    have hc : IsMonHom (∏ j, pr8 G j ^ a k j) :=
      PowQuotient.isMonHom_prod _ fun j => Serre.isMonHom_zpow _ _
    rw [MonObj.mul_comp _ _ (pr8 G k), Category.assoc, Category.assoc, Category.assoc, matAct_pr,
      MonObj.mul_comp _ _ (∏ j, pr8 G j ^ a k j)]

theorem matAct_one : matAct G 1 = 𝟙 (G8 G) := eighthPowerGroupObj_hom_ext G fun i => by
  rw [matAct_pr, Category.id_comp, Finset.prod_eq_single i]
  · simp
  · intro j _ hj; simp [Matrix.one_apply_ne' hj]
  · simp

theorem zpow_sum8 {M : Type} [CommGroup M] (x : M) (f : Fin 8 → ℤ) : x ^ (∑ j, f j) = ∏ j, x ^ f j := by
  simp only [Fin.sum_univ_eight, Fin.prod_univ_eight, zpow_add]

theorem matAct_add (a b : Matrix (Fin 8) (Fin 8) ℤ) :
    matAct G (a + b) = padd (G8 G) (matAct G a) (matAct G b) := eighthPowerGroupObj_hom_ext G fun k => by
  have e : padd (G8 G) (matAct G a) (matAct G b) = matAct G a * matAct G b := rfl
  rw [e, MonObj.mul_comp _ _ (pr8 G k), matAct_pr, matAct_pr, matAct_pr, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [Matrix.add_apply, zpow_add]

theorem matAct_mul (a b : Matrix (Fin 8) (Fin 8) ℤ) :
    matAct G (a * b) = matAct G b ≫ matAct G a := eighthPowerGroupObj_hom_ext G fun k => by
  rw [Category.assoc, matAct_pr, matAct_pr, PowQuotient.comp_prod]
  simp only [GrpObj.comp_zpow, matAct_pr, Matrix.mul_apply]
  simp only [← Finset.prod_zpow, ← zpow_mul]
  rw [Finset.prod_comm]
  refine Finset.prod_congr rfl fun l _ => ?_
  rw [zpow_sum8]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [mul_comm]

def ringAct8 : RingAct (G8 G) GlobalTheory.Mum.E8Ring.O8 where
  act a := matAct G a
  hom a := matAct_hom G a
  map_one := matAct_one G
  map_mul a b := matAct_mul G a b
  map_add a b := matAct_add G a b

end GlobalTheory.Mum.Pow8
