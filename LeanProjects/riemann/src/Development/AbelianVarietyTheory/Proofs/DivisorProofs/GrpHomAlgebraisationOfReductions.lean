import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.FormalAlgebraisation
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem isMonHom_of_fst_mul_snd {S : Scheme.{0}} {A B : Over S} [GrpObj A] [GrpObj B] (g : A ⟶ B)
    (h : (fst A A * snd A A) ≫ g = (fst A A ≫ g) * (snd A A ≫ g)) : IsMonHom g := by
  have hm : ∀ (T : Over S) (x y : T ⟶ A), (x * y) ≫ g = (x ≫ g) * (y ≫ g) := fun T x y => by
    have := congrArg (lift x y ≫ ·) h
    simpa only [← Category.assoc, MonObj.comp_mul, lift_fst, lift_snd] using this
  refine ⟨?_, ?_⟩
  · have h1 := hm (𝟙_ _) 1 1
    rw [_root_.mul_one] at h1
    have h2 : (1 : 𝟙_ (Over S) ⟶ A) ≫ g = 1 := left_eq_mul.1 h1
    simpa [Hom.one_def] using h2
  · have e : (fst A A * snd A A) = μ[A] := by simp [Hom.mul_def]
    rw [e] at h
    rw [h, Hom.mul_def]
    congr 1

theorem mul_comp_of_isGrpPullback {S S' : Scheme.{0}} {A B : Over S} [GrpObj A] [GrpObj B]
    {Y Z : Over S'} [GrpObj Y] [GrpObj Z] {t : S' ⟶ S} {a : Y.left ⟶ A.left} {b : Z.left ⟶ B.left}
    (ha : IsGrpPullback Y A t a) (hb : IsGrpPullback Z B t b) (f : Y ⟶ Z) [IsMonHom f] (g : A ⟶ B)
    (hg : a ≫ g.left = f.left ≫ b) (T : Over S') (x y : Over.mk (T.hom ≫ t) ⟶ A) :
    (x * y) ≫ g = (x ≫ g) * (y ≫ g) := by
  let x' : T ⟶ Y := Over.homMk (ha.1.lift x.left T.hom (Over.w x)) (ha.1.lift_snd _ _ _)
  let y' : T ⟶ Y := Over.homMk (ha.1.lift y.left T.hom (Over.w y)) (ha.1.lift_snd _ _ _)
  have hx : x.left = x'.left ≫ a := (ha.1.lift_fst _ _ _).symm
  have hy : y.left = y'.left ≫ a := (ha.1.lift_fst _ _ _).symm
  have h1 := ha.2 T x' y' x y hx hy
  have h2 := hb.2 T (x' ≫ f) (y' ≫ f) (x ≫ g) (y ≫ g)
    (by rw [Over.comp_left, Over.comp_left, hx, Category.assoc, Category.assoc, hg])
    (by rw [Over.comp_left, Over.comp_left, hy, Category.assoc, Category.assoc, hg])
  ext
  rw [h2, Over.comp_left, h1, ← MonObj.mul_comp, Over.comp_left, Category.assoc, Category.assoc, hg]

theorem grpHom_algebraise : GlobalTheory.Published.FormalAlgebraisation.Morphisms → ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R), IsAdicComplete I R → ∀ (A B : Over (Spec (CommRingCat.of R))) [GrpObj A] [GrpObj B], IsProper A.hom → IsProper B.hom → ∀ (Y Z : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) [∀ e, GrpObj (Y e)] [∀ e, GrpObj (Z e)] (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left) (δ : ∀ e, (Z e).left ⟶ (Z (e + 1)).left) (a : ∀ e, (Y e).left ⟶ A.left) (b : ∀ e, (Z e).left ⟶ B.left), (∀ e, IsGrpPullback (Y e) A (thick R I e) (a e)) → (∀ e, β e ≫ a (e + 1) = a e) → (∀ e, IsGrpPullback (Z e) B (thick R I e) (b e)) → (∀ e, δ e ≫ b (e + 1) = b e) → ∀ f : ∀ e, Y e ⟶ Z e, (∀ e, IsMonHom (f e)) → (∀ e, β e ≫ (f (e + 1)).left = (f e).left ≫ δ e) → ∃ g : A ⟶ B, IsMonHom g ∧ (∀ e, a e ≫ g.left = (f e).left ≫ b e) ∧ ∀ g' : A ⟶ B, (∀ e, a e ≫ g'.left = (f e).left ≫ b e) → g' = g := by
  intro H R _ _ I hI A B _ _ hA hB Y Z _ _ β δ a b ha hβ hb hδ f hf hc
  obtain ⟨g, hg, hu⟩ := H R I hI A B hA inferInstance inferInstance inferInstance Y β a
    (fun e => (ha e).1) hβ (fun e => (f e).left ≫ b e)
    (fun e => by rw [Category.assoc, (hb e).1.w, ← Category.assoc, Over.w])
    (fun e => by rw [← Category.assoc, hc, Category.assoc, hδ])
  refine ⟨g, isMonHom_of_fst_mul_snd g ?_, hg, hu⟩
  haveI : IsProper (A ⊗ A).hom := by
    change IsProper (pullback.fst A.hom A.hom ≫ A.hom)
    infer_instance
  refine H.hom_ext hI fun e => ?_
  haveI := hf e
  let T : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) :=
    Over.mk (pullback.snd (A ⊗ A).hom (thick R I e))
  let P : Over.mk (T.hom ≫ thick R I e) ⟶ A ⊗ A :=
    Over.homMk (pullback.fst (A ⊗ A).hom (thick R I e)) pullback.condition
  have key := mul_comp_of_isGrpPullback (ha e) (hb e) (f e) g (hg e) T (P ≫ fst A A) (P ≫ snd A A)
  have key' : P ≫ (fst A A * snd A A) ≫ g = P ≫ ((fst A A ≫ g) * (snd A A ≫ g)) := by
    rw [← Category.assoc, MonObj.comp_mul, key, MonObj.comp_mul, Category.assoc, Category.assoc]
  exact congrArg (·.left) key'

end GlobalTheory
