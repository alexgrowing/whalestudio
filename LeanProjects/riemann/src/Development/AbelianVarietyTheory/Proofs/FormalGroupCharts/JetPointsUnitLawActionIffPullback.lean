import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GermCut
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GermBGen
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ChartPrimTrPfA
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.IntChartPf
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ExistsTruncatedIntegralChart
import Formalism.LocalToGlobal.ProjectiveLattices.PlaceBelow
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1 FGLaw)
open MvPolynomial (X)

noncomputable section

namespace GlobalTheory

section Push

variable {X0 : Scheme.{0}} {S : Type} [CommRing S] {x0 : Sp S ⟶ X0} {G : Over X0} {G' : Over (Sp S)}
  [GrpObj G] [GrpObj G'] {φ : G'.left ⟶ G.left}

def algPtPush (h : IsGrpPullback G' G x0 φ) (A : Type) [CommRing A] [Algebra S A] :
    (overAt (𝟙 (Sp S)) A ⟶ G') →* (overAt x0 A ⟶ G) :=
  (preHom (Over.homMk (𝟙 (Sp A)) (by simp) :
    overAt x0 A ⟶ Over.mk ((overAt (𝟙 (Sp S)) A).hom ≫ x0))).comp (pushHom h (overAt (𝟙 (Sp S)) A))

theorem algPtPush_left (h : IsGrpPullback G' G x0 φ) (A : Type) [CommRing A] [Algebra S A]
    (a : overAt (𝟙 (Sp S)) A ⟶ G') : (algPtPush h A a).left = a.left ≫ φ :=
  Category.id_comp (a.left ≫ φ)

theorem algPtPush_injective (h : IsGrpPullback G' G x0 φ) (A : Type) [CommRing A] [Algebra S A] :
    Function.Injective (algPtPush h A) := fun a b e => by
  refine Over.OverMorphism.ext (h.1.hom_ext ?_ ((Over.w a).trans (Over.w b).symm))
  exact (algPtPush_left h A a).symm.trans ((congrArg (fun q => q.left) e).trans (algPtPush_left h A b))

theorem algPtPush_homAt (h : IsGrpPullback G' G x0 φ) {A B : Type} [CommRing A] [Algebra S A] [CommRing B]
    [Algebra S B] (ψ : A →ₐ[S] B) (a : overAt (𝟙 (Sp S)) A ⟶ G') :
    algPtPush h B (Formalism.L2.Pj.homAt (𝟙 (Sp S)) ψ ≫ a) = Formalism.L2.Pj.homAt x0 ψ ≫ algPtPush h A a :=
  Over.OverMorphism.ext ((algPtPush_left h B _).trans ((Category.assoc (spMap (ψ : A →+* B)) a.left φ).trans
    (congrArg (fun q => spMap (ψ : A →+* B) ≫ q) (algPtPush_left h A a).symm)))

theorem algPtPush_comp (h : IsGrpPullback G' G x0 φ) {A : Type} [CommRing A] [Algebra S A]
    (u' : G' ⟶ G') (u : G ⟶ G) (e : u'.left ≫ φ = φ ≫ u.left) (a : overAt (𝟙 (Sp S)) A ⟶ G') :
    algPtPush h A (a ≫ u') = algPtPush h A a ≫ u :=
  Over.OverMorphism.ext ((algPtPush_left h A _).trans ((Category.assoc a.left u'.left φ).trans
    ((congrArg (fun q => a.left ≫ q) e).trans ((Category.assoc a.left φ u.left).symm.trans
      (congrArg (fun q => q ≫ u.left) (algPtPush_left h A a).symm)))))

end Push

theorem jetPoints_laws_iff_pullback : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X0 : Scheme.{0}) (t : SAB H X0) (S : Type) [CommRing S] (x0 : Sp S ⟶ X0) (t' : SAB H (Sp S)) (mp : SABMap t' t x0) (w : LB.Iso t'.PP.L (t.PP.L.pull mp.φ)), RigIso mp w → ∀ (d : ℕ) (x : ∀ m, jOG x0 d m 1 ⟶ t.G) (x' : ∀ m, jOG (𝟙 (Sp S)) d m 1 ⟶ t'.G), (∀ m, (x' m).left ≫ mp.φ = (x m).left) → ((∀ m, homAt x0 (jetAug : Jet S (Fin 1 × Fin d) m →ₐ[S] S) ≫ x m = 1) ↔ (∀ m, homAt (𝟙 (Sp S)) (jetAug : Jet S (Fin 1 × Fin d) m →ₐ[S] S) ≫ x' m = 1)) ∧ (∀ F : Fin d → PS S 2 d, (∀ m, homAt x0 (jetSubstP m fun p : Fin 1 × Fin d => psTrunc m (F p.2)) ≫ x m = jptG t x0 d x m (0 : Fin 2) * jptG t x0 d x m (1 : Fin 2)) ↔ (∀ m, homAt (𝟙 (Sp S)) (jetSubstP m fun p : Fin 1 × Fin d => psTrunc m (F p.2)) ≫ x' m = jptG t' (𝟙 (Sp S)) d x' m (0 : Fin 2) * jptG t' (𝟙 (Sp S)) d x' m (1 : Fin 2))) ∧ ∀ act : 𝓞 E → Fin d → PS S 1 d, (∀ m (b : 𝓞 E), x m ≫ t.act.act b = homAt x0 (jetSubstP m fun p : Fin 1 × Fin d => psTrunc m (act b p.2)) ≫ x m) ↔ (∀ m (b : 𝓞 E), x' m ≫ t'.act.act b = homAt (𝟙 (Sp S)) (jetSubstP m fun p : Fin 1 × Fin d => psTrunc m (act b p.2)) ≫ x' m) := by
  intro E _ _ _ H X0 t S _ x0 t' mp w _ d x x' hx
  obtain rfl : x = fun m => algPtPush mp.cart _ (x' m) :=
    funext fun m => Over.OverMorphism.ext ((hx m).symm.trans (algPtPush_left mp.cart _ (x' m)).symm)
  refine ⟨forall_congr' fun m => ?_, fun F => forall_congr' fun m => ?_,
    fun act => forall_congr' fun m => forall_congr' fun b => ?_⟩
  · rw [← (algPtPush_injective mp.cart _).eq_iff, map_one, algPtPush_homAt]
  · rw [← (algPtPush_injective mp.cart _).eq_iff, map_mul, algPtPush_homAt]
    simp only [jptG, algPtPush_homAt]
  · rw [← (algPtPush_injective mp.cart _).eq_iff, algPtPush_homAt,
      algPtPush_comp mp.cart _ _ (mp.act b)]

end GlobalTheory
