import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LabRange
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
open MonObj GrpObj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc

def diagPrecomp {T : Scheme.{0}} {X Y M : Over T} [MonObj M] (f : X ⟶ Y) : (Y ⟶ M) →* (X ⟶ M) where
  toFun := (f ≫ ·)
  map_one' := by
    change f ≫ toUnit Y ≫ η = toUnit X ≫ η
    rw [← Category.assoc, toUnit_unique (f ≫ toUnit Y)]
  map_mul' g h := by
    change f ≫ lift g h ≫ μ = lift (f ≫ g) (f ≫ h) ≫ μ
    rw [← Category.assoc, comp_lift]

theorem exists_diagEnd_isMonHom (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (T : Scheme.{0})
    (P : PolAV T) (u : T ⟶ F.X) (h : SharpOver F W P u) :
    ∃ ε : Matrix (Fin 8) (Fin 8) ℤ → (P.A ⟶ P.A), IsDiagEnd F W P u ε ∧ ∀ E, IsMonHom (ε E) := by
  obtain ⟨c, hc, pr, hpr, huniq, hL⟩ := h
  choose ε hε _ using fun E : Matrix (Fin 8) (Fin 8) ℤ =>
    huniq P.A (fun a => ((List.finRange 8).map fun b => pr b ^ E a b).prod)
  have ext : ∀ (T' : Over T) (x x' : T' ⟶ P.A), (∀ a, x ≫ pr a = x' ≫ pr a) → x = x' := fun T' x x' hx =>
    (huniq T' (fun a => x' ≫ pr a)).unique hx (fun _ => rfl)
  refine ⟨ε, ⟨c, hc, pr, hpr, huniq, hL, hε⟩, fun E => ?_⟩
  have key : ∀ (T' : Over T) (x : T' ⟶ P.A) (a : Fin 8),
      (x ≫ ε E) ≫ pr a = ((List.finRange 8).map fun b => (x ≫ pr b) ^ E a b).prod := by
    intro T' x a
    rw [Category.assoc, hε]
    change diagPrecomp (M := c.A) x _ = _
    rw [map_list_prod, List.map_map]
    congr 1
    refine List.map_congr_left fun b _ => ?_
    exact map_zpow (diagPrecomp (M := c.A) x) (pr b) (E a b)
  refine isMonHom_of_mul _ fun T' x z => ext T' _ _ fun a => ?_
  have hm : ∀ (b : Fin 8) (x z : T' ⟶ P.A), (x * z) ≫ pr b = (x ≫ pr b) * (z ≫ pr b) := fun b x z =>
    map_mul (IsMonHom.monoidHom (pr b) T') x z
  have hm' : ((x ≫ ε E) * (z ≫ ε E)) ≫ pr a = ((x ≫ ε E) ≫ pr a) * ((z ≫ ε E) ≫ pr a) :=
    map_mul (IsMonHom.monoidHom (pr a) T') (x ≫ ε E) (z ≫ ε E)
  rw [key, hm', key, key, ← List.prod_map_mul]
  congr 1
  refine List.map_congr_left fun b _ => ?_
  rw [hm, mul_zpow]

end GlobalTheory.Poinc
