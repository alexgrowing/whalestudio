import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatFrameApply
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.TanBaseChange

open MonoidalCategory CartesianMonoidalCategory MonObj

attribute [local instance] Over.cartesianMonoidalCategory

theorem spMap_comp_spMap' {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] (f : R' →+* R'')
    (g : R →+* R') : spMap f ≫ spMap g = spMap (f.comp g) := by
  unfold spMap
  rw [← Spec.map_comp]
  rfl

theorem dualMap_comp_algebraMap {S T : Type} [CommRing S] [CommRing T] (ψ : S →+* T) :
    (Formalism.L2.Pj.dualMap ψ).comp (algebraMap S (DualNumber S)) = (algebraMap T (DualNumber T)).comp ψ := by
  ext s <;> simp [Formalism.L2.Pj.dualMap, TrivSqZeroExt.algebraMap_eq_inl]

theorem fstHom_comp_dualMap {S T : Type} [CommRing S] [CommRing T] (ψ : S →+* T) :
    (TrivSqZeroExt.fstHom T T T).toRingHom.comp (Formalism.L2.Pj.dualMap ψ) =
      ψ.comp (TrivSqZeroExt.fstHom S S S).toRingHom := by
  ext s <;> simp [Formalism.L2.Pj.dualMap, TrivSqZeroExt.algebraMap_eq_inl]

theorem dualMap_comp_epsMul' {S T : Type} [CommRing S] [CommRing T] (ψ : S →+* T) (a : S) :
    (Formalism.L2.Pj.dualMap ψ).comp (epsMul a) = (epsMul (ψ a)).comp (Formalism.L2.Pj.dualMap ψ) := by
  ext s <;> simp [Formalism.L2.Pj.dualMap, epsMul, TrivSqZeroExt.algebraMap_eq_inl]

theorem list_prod_comp' {X0 : Scheme.{0}} {G : Over X0} [MonObj G] {T T' : Over X0} (f : T' ⟶ T)
    (L : List (T ⟶ G)) : (L.map (f ≫ ·)).prod = f ≫ L.prod := by
  induction L with
  | nil => simp [Hom.one_def]
  | cons a L ih => simp only [List.map_cons, List.prod_cons, ih, Hom.mul_def, comp_lift_assoc]

theorem tan_comb_baseChange : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) (t : SAB H X) (S S' : Type) [CommRing S] [CommRing S'] (φ : S →+* S') (x : Sp S ⟶ X) (x' : Sp S' ⟶ X), spMap φ ≫ x = x' → (∀ v : Sp (DualNumber S) ⟶ t.G.left, IsTanAtG t x v → IsTanAtG t x' (spMap (dualMap φ) ≫ v)) ∧ ∀ (m : ℕ) (v : Fin m → (Sp (DualNumber S) ⟶ t.G.left)) (cf : Fin m → S) (w : Sp (DualNumber S) ⟶ t.G.left), IsCombAtG t x v cf w → IsCombAtG t x' (fun i => spMap (dualMap φ) ≫ v i) (fun i => φ (cf i)) (spMap (dualMap φ) ≫ w) := by
  intro E _ _ _ H X t S S' _ _ φ x x' hx
  subst hx
  refine ⟨fun v hv => ?_, fun m v cf w h => ?_⟩
  · obtain ⟨h1, h2⟩ := hv
    refine ⟨?_, ?_⟩
    · rw [Category.assoc, h1, ← Category.assoc, spMap_comp_spMap', dualMap_comp_algebraMap, ← spMap_comp_spMap',
        Category.assoc]
    · rw [← Category.assoc, spMap_comp_spMap', fstHom_comp_dualMap, ← spMap_comp_spMap', Category.assoc, h2]
      have e : (Over.homMk (spMap φ) rfl : Over.mk (spMap φ ≫ x) ⟶ Over.mk x) ≫ (1 : Over.mk x ⟶ t.G) = 1 := by
        simp [Hom.one_def]
      rw [← e, Over.comp_left]
      rfl
  · obtain ⟨u, hu, hp⟩ := h
    let q : tEpsG (spMap φ ≫ x) ⟶ tEpsG x := Over.homMk (spMap (Formalism.L2.Pj.dualMap φ)) (by
      show spMap (Formalism.L2.Pj.dualMap φ) ≫ spMap (algebraMap S (DualNumber S)) ≫ x =
        spMap (algebraMap S' (DualNumber S')) ≫ spMap φ ≫ x
      rw [← Category.assoc, ← Category.assoc, spMap_comp_spMap', spMap_comp_spMap', dualMap_comp_algebraMap])
    refine ⟨fun i => q ≫ u i, fun i => ?_, ?_⟩
    · show spMap (Formalism.L2.Pj.dualMap φ) ≫ (u i).left = _
      rw [hu i, ← Category.assoc, spMap_comp_spMap', dualMap_comp_epsMul', ← spMap_comp_spMap', Category.assoc]
    · have e : List.ofFn (fun i => q ≫ u i) = (List.ofFn u).map (q ≫ ·) := by
        rw [List.map_ofFn]
        rfl
      rw [e, list_prod_comp', Over.comp_left, hp]
      rfl

end GlobalTheory.TanBaseChange
