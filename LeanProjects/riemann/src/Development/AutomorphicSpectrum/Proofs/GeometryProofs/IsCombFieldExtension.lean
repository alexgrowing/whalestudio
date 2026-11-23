import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsExcisionNbhdAway
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat

namespace GlobalTheory.CompanionTheory.Ar.CombBase

theorem comp_list_prod {S : Scheme.{0}} {G A B : Over S} [GrpObj G] (g : A ⟶ B) (l : List (B ⟶ G)) :
    g ≫ l.prod = (l.map (g ≫ ·)).prod := by
  induction l with
  | nil => simp [comp_one]
  | cons a l ih => simp only [List.prod_cons, List.map_cons, comp_mul, ih]

theorem isComb_base : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (F : Type) [Field F] (x : Sp F ⟶ S) (F' : Type) [Field F'] (f : F →+* F') (x' : Sp F' ⟶ S), spMap f ≫ x = x' → ∀ (n : ℕ) (v : Fin n → (epsAt x ⟶ G)) (cf : Fin n → F) (w : epsAt x ⟶ G) (v' : Fin n → (epsAt x' ⟶ G)) (w' : epsAt x' ⟶ G), (∀ i, (v' i).left = spMap (dualMap f) ≫ (v i).left) → w'.left = spMap (dualMap f) ≫ w.left → IsComb cf v w → IsComb (fun i => f (cf i)) v' w' := by
  rintro S G _ _ F _ x F' _ f x' hx n v cf w v' w' hv hw ⟨u, hu, e⟩
  refine ⟨fun i => LieTangent.epsBase f hx ≫ u i, fun i => ?_, ?_⟩
  · change spMap (dualMap f) ≫ (u i).left = _
    rw [hu i, ← Category.assoc, LieTangent.spec_dual_eps, Category.assoc, hv i]
  · rw [(LieTangent.left_eq_iff f hx w' w).1 hw, e, comp_list_prod, List.map_ofFn]
    rfl

end GlobalTheory.CompanionTheory.Ar.CombBase
