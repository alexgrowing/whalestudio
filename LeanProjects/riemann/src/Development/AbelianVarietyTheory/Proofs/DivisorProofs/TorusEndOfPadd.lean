import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Counterexamples.UniformisationSurvey.NeTopOfAdmissibleBase

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Mum

def ActsAs {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
    {A : PolAV (Sp (FractionRing R))} {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G]
    (U : UnifPre I D A G) (b : D.toPre.P.A ⟶ D.toPre.P.A) (h : D.toPre.X → D.toPre.X) (g : G ⟶ G) : Prop :=
  ∀ e : ℕ, (Over.pullback (thick R I e)).map g ≫ (U.gt e).q = (U.gt e).q ≫ (Over.pullback (thick R I e)).map b ∧
    ∃ t : splitTorus (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) D.toPre.X ⟶ splitTorus _ D.toPre.X,
      TorusEndOf D.toPre.X h t ∧ (U.gt e).i ≫ (Over.pullback (thick R I e)).map g = t ≫ (U.gt e).i

theorem pull_padd {S S' : Scheme.{0}} (f : S' ⟶ S) {T G : Over S} [GrpObj G] (a b : T ⟶ G) :
    (Over.pullback f).map (padd G a b) = padd _ ((Over.pullback f).map a) ((Over.pullback f).map b) := by
  simp [padd, Functor.Monoidal.lift_μ_assoc]

theorem comp_padd' {S : Scheme.{0}} {T T' G : Over S} [GrpObj G] (x : T ⟶ T') (a b : T' ⟶ G) :
    x ≫ padd G a b = padd G (x ≫ a) (x ≫ b) := by
  rw [padd, padd, comp_lift_assoc]

theorem padd_comp_hom {S : Scheme.{0}} {X Y T : Over S} [GrpObj X] [GrpObj Y] (f f' : T ⟶ X) (h : X ⟶ Y) [IsMonHom h] :
    padd X f f' ≫ h = padd Y (f ≫ h) (f' ≫ h) := by
  rw [padd, padd, Category.assoc, IsMonHom.mul_hom, ← Category.assoc, lift_map]

theorem torusEndOf_padd {S : Scheme.{0}} {X : Type} [AddCommGroup X] {h h' : X → X}
    {t t' : splitTorus S X ⟶ splitTorus S X} (ht : TorusEndOf X h t) (ht' : TorusEndOf X h' t') :
    TorusEndOf X (h + h') (padd _ t t') := by
  rw [GlobalTheory.LinearUnifCheck.torusEndOf_iff] at ht ht' ⊢
  intro χ
  have hc : ∀ x, (charUnit S X x).val =
      (GlobalTheory.splitTorusPointsEquiv S X (splitTorus S X) (𝟙 _) (Multiplicative.ofAdd x)).val := fun x =>
    ((GlobalTheory.splitTorusPointsEquiv_val S X _ (𝟙 _) x).trans (SplitTorusHom.appTop_id _)).symm
  have hp : padd (splitTorus S X) t t' = t * t' := rfl
  rw [hp, ← GlobalTheory.splitTorusPointsEquiv_val, map_mul, MonoidHom.mul_apply, Units.val_mul,
    GlobalTheory.splitTorusPointsEquiv_val, GlobalTheory.splitTorusPointsEquiv_val, ht, ht', hc, hc, hc, Pi.add_apply, ofAdd_add,
    map_mul, Units.val_mul]

theorem actsAs_padd {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
    {A : PolAV (Sp (FractionRing R))} {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G]
    (U : UnifPre I D A G) {b b' : D.toPre.P.A ⟶ D.toPre.P.A} {h h' : D.toPre.X → D.toPre.X} {g g' : G ⟶ G}
    (hg : ActsAs U b h g) (hg' : ActsAs U b' h' g') : ActsAs U (padd _ b b') (h + h') (padd G g g') := by
  intro e
  obtain ⟨q1, t, ht, i1⟩ := hg e
  obtain ⟨q2, t', ht', i2⟩ := hg' e
  have := (U.gt e).q_hom
  have := (U.gt e).i_hom
  refine ⟨?_, padd _ t t', torusEndOf_padd ht ht', ?_⟩
  · rw [pull_padd, pull_padd, padd_comp_hom, q1, q2, comp_padd']
  · rw [pull_padd, comp_padd', i1, i2, padd_comp_hom]

theorem actsAs_comp {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
    {A : PolAV (Sp (FractionRing R))} {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G]
    (U : UnifPre I D A G) {b b' : D.toPre.P.A ⟶ D.toPre.P.A} {h h' : D.toPre.X → D.toPre.X} {g g' : G ⟶ G}
    (hg : ActsAs U b h g) (hg' : ActsAs U b' h' g') : ActsAs U (b ≫ b') (h ∘ h') (g ≫ g') := by
  intro e
  obtain ⟨q1, t, ht, i1⟩ := hg e
  obtain ⟨q2, t', ht', i2⟩ := hg' e
  refine ⟨?_, t ≫ t', GlobalTheory.LinearUnifCheck.torusEndOf_comp ht ht', ?_⟩
  · rw [Functor.map_comp, Category.assoc, q2, ← Category.assoc, q1, Category.assoc, ← Functor.map_comp]
  · rw [Functor.map_comp, ← Category.assoc, i1, Category.assoc, i2, Category.assoc]

theorem actsAs_id {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
    {A : PolAV (Sp (FractionRing R))} {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G]
    (U : UnifPre I D A G) : ActsAs U (𝟙 _) id (𝟙 G) := by
  intro e
  refine ⟨by simp, 𝟙 _, ?_, by simp⟩
  rw [GlobalTheory.LinearUnifCheck.torusEndOf_iff]; intro χ; simp

end GlobalTheory.Mum
