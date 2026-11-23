import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThickTransComp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.Published

namespace FormalAlgebraisation

def Morphisms : Prop :=
  ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R), IsAdicComplete I R →
    ∀ (X Z : Over (Spec (CommRingCat.of R))), IsProper X.hom →
      IsSeparated Z.hom → LocallyOfFiniteType Z.hom → QuasiCompact Z.hom →
    ∀ (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))))
      (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left) (b : ∀ e, (Y e).left ⟶ X.left),
      (∀ e, IsPullback (b e) (Y e).hom X.hom (thick R I e)) → (∀ e, β e ≫ b (e + 1) = b e) →
    ∀ f : ∀ e, (Y e).left ⟶ Z.left,
      (∀ e, f e ≫ Z.hom = (Y e).hom ≫ thick R I e) → (∀ e, β e ≫ f (e + 1) = f e) →
      ∃! g : X ⟶ Z, ∀ e, b e ≫ g.left = f e

def Schemes : Prop :=
  ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R), IsAdicComplete I R →
    ∀ (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))))
      (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left),
      (∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e)) →
      (∀ e, IsProper (Y e).hom) →
    ∀ N : ∀ e, LB (Y e).left, (∀ e, (N e).IsLB) → (∀ e, LBIso (N e) ((N (e + 1)).pull (β e))) →
      RelAmple (Y 0) (N 0) →
      ∃ (X : Over (Spec (CommRingCat.of R))) (M : LB X.left) (b : ∀ e, (Y e).left ⟶ X.left),
        IsProper X.hom ∧ M.IsLB ∧ RelAmple X M ∧
        (∀ e, IsPullback (b e) (Y e).hom X.hom (thick R I e)) ∧ (∀ e, β e ≫ b (e + 1) = b e) ∧
        ∀ e, LBIso (N e) (M.pull (b e))

end FormalAlgebraisation

def FormalAlgebraisation : Prop :=
  FormalAlgebraisation.Morphisms ∧ FormalAlgebraisation.Schemes

namespace FormalAlgebraisation

variable {R : Type} [CommRing R] [IsNoetherianRing R] {I : Ideal R}

theorem Morphisms.existsUnique_thick (H : Morphisms) (hI : IsAdicComplete I R)
    (X Z : Over (Spec (CommRingCat.of R))) [hX : IsProper X.hom] [hZ : IsProper Z.hom]
    (f : ∀ e, (thickObj R I e X).left ⟶ Z.left)
    (hf : ∀ e, f e ≫ Z.hom = pullback.fst X.hom (thick R I e) ≫ X.hom)
    (hc : ∀ e, thickMap R I e X ≫ f (e + 1) = f e) :
    ∃! g : X ⟶ Z, ∀ e, pullback.fst X.hom (thick R I e) ≫ g.left = f e :=
  H R I hI X Z hX inferInstance inferInstance inferInstance (fun e => thickObj R I e X)
    (fun e => thickMap R I e X) (fun e => pullback.fst X.hom (thick R I e))
    (fun _ => IsPullback.of_hasPullback _ _)
    (fun _ => (pullback.lift_fst _ _ _).trans (Category.comp_id _)) f
    (fun e => (hf e).trans pullback.condition) hc

theorem Morphisms.hom_ext (H : Morphisms) (hI : IsAdicComplete I R)
    {X Z : Over (Spec (CommRingCat.of R))} [IsProper X.hom] [IsProper Z.hom] {g g' : X ⟶ Z}
    (h : ∀ e, pullback.fst X.hom (thick R I e) ≫ g.left = pullback.fst X.hom (thick R I e) ≫ g'.left) :
    g = g' :=
  (H.existsUnique_thick hI X Z (fun e => pullback.fst X.hom (thick R I e) ≫ g'.left)
    (fun e => by rw [Category.assoc, Over.w])
    (fun e => by
      rw [← Category.assoc]
      exact congrArg (· ≫ g'.left) ((pullback.lift_fst _ _ _).trans (Category.comp_id _)))).unique
    h (fun _ => rfl)

theorem Morphisms.exists_iso (H : Morphisms) (hI : IsAdicComplete I R)
    {X X' : Over (Spec (CommRingCat.of R))} [hX : IsProper X.hom] [hX' : IsProper X'.hom]
    {Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))}
    {β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left} {b : ∀ e, (Y e).left ⟶ X.left}
    {b' : ∀ e, (Y e).left ⟶ X'.left}
    (hb : ∀ e, IsPullback (b e) (Y e).hom X.hom (thick R I e)) (hβ : ∀ e, β e ≫ b (e + 1) = b e)
    (hb' : ∀ e, IsPullback (b' e) (Y e).hom X'.hom (thick R I e))
    (hβ' : ∀ e, β e ≫ b' (e + 1) = b' e) :
    ∃ g : X ≅ X', (∀ e, b e ≫ g.hom.left = b' e) ∧
      ∀ g' : X ⟶ X', (∀ e, b e ≫ g'.left = b' e) → g' = g.hom := by
  obtain ⟨g, hg, hu⟩ := H R I hI X X' hX inferInstance inferInstance inferInstance Y β b hb hβ b'
    (fun e => (hb' e).w) hβ'
  obtain ⟨k, hk, -⟩ := H R I hI X' X hX' inferInstance inferInstance inferInstance Y β b' hb' hβ' b
    (fun e => (hb e).w) hβ
  refine ⟨⟨g, k, ?_, ?_⟩, hg, hu⟩
  · exact (H R I hI X X hX inferInstance inferInstance inferInstance Y β b hb hβ b
      (fun e => (hb e).w) hβ).unique
      (fun e => by rw [Over.comp_left, ← Category.assoc, hg, hk]) (fun e => Category.comp_id _)
  · exact (H R I hI X' X' hX' inferInstance inferInstance inferInstance Y β b' hb' hβ' b'
      (fun e => (hb' e).w) hβ').unique
      (fun e => by rw [Over.comp_left, ← Category.assoc, hk, hg]) (fun e => Category.comp_id _)

end FormalAlgebraisation

end GlobalTheory.Published
