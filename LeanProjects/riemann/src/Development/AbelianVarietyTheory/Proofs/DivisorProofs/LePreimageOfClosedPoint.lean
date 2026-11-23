import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechGluingOfKodairaSpencerRelation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslateUnique
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsTanBasisOfUniqueCombination
open AlgebraicGeometry CategoryTheory Limits NumberField MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj

set_option autoImplicit false

noncomputable section

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.VertSpanZero

theorem le_preimage_of_closedPoint {Z : Scheme.{0}} {R : Type} [CommRing R] [IsLocalRing R] (y : Sp R ⟶ Z)
    (V : Z.Opens) (h : y.base (IsLocalRing.closedPoint R) ∈ V) : ⊤ ≤ y ⁻¹ᵁ V := by
  intro p _
  exact ((IsLocalRing.specializes_closedPoint p).map y.continuous).mem_open V.isOpen h

theorem snd_valR_epsMul {Z : Scheme.{0}} {S : Type} [CommRing S] (T : Sp (DualNumber S) ⟶ Z) (O : Z.Opens)
    (h : ⊤ ≤ T ⁻¹ᵁ O) (a : S) (f : Γ(Z, O)) :
    (valR (spMap (epsMul a) ≫ T) O f).snd = a * (valR T O f).snd := by
  rw [GlobalTheory.Points.valR_spMap_comp (epsMul a) T O h f]
  simp [epsMul]

theorem epsMul_comp_algebraMap {S : Type} [CommRing S] (a : S) :
    (epsMul a).comp (algebraMap S (DualNumber S)) = algebraMap S (DualNumber S) := by
  ext x <;> simp [epsMul, TrivSqZeroExt.algebraMap_eq_inl]

theorem fst_comp_epsMul {S : Type} [CommRing S] (a : S) :
    (TrivSqZeroExt.fstHom S S S).toRingHom.comp (epsMul a) = (TrivSqZeroExt.fstHom S S S).toRingHom := by
  ext x <;> simp [epsMul]

theorem epsMul_zero' {S : Type} [CommRing S] :
    epsMul (0 : S) = (algebraMap S (DualNumber S)).comp (TrivSqZeroExt.fstHom S S S).toRingHom := by
  ext x <;> simp [epsMul, TrivSqZeroExt.algebraMap_eq_inl]

end GlobalTheory.VertSpanZero

namespace GlobalTheory.VertSpanZero

theorem spMap_fst_algebraMap (S : Type) [CommRing S] :
    spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ spMap (algebraMap S (DualNumber S)) = 𝟙 _ := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← Spec.map_id]
  congr 1

theorem spMap_comp_eq {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  show Spec.map (CommRingCat.ofHom (g.comp f)) = Spec.map (CommRingCat.ofHom g) ≫ Spec.map (CommRingCat.ofHom f)
  rw [CommRingCat.ofHom_comp, Spec.map_comp]

def redOver {X : Scheme.{0}} {S : Type} [CommRing S] (x : Sp S ⟶ X) : Over.mk x ⟶ tEpsG x :=
  Over.homMk (spMap (TrivSqZeroExt.fstHom S S S).toRingHom) (by
    change _ ≫ spMap (algebraMap S (DualNumber S)) ≫ x = x
    rw [← Category.assoc, spMap_fst_algebraMap, Category.id_comp])

theorem redOver_comp_prod {X : Scheme.{0}} {G : Over X} [GrpObj G] {S : Type} [CommRing S] (x : Sp S ⟶ X)
    (l : List (tEpsG x ⟶ G)) (hl : ∀ u ∈ l, redOver x ≫ u = 1) : redOver x ≫ l.prod = 1 := by
  induction l with
  | nil => exact MonObj.comp_one _
  | cons u l ih =>
    rw [List.prod_cons, MonObj.comp_mul, hl u List.mem_cons_self,
      ih fun u' h => hl u' (List.mem_cons_of_mem _ h), _root_.mul_one]

theorem red_mul_prod {X : Scheme.{0}} {G : Over X} [GrpObj G] {S : Type} [CommRing S] (g : Sp S ⟶ G.left)
    (g' : tEpsG (g ≫ G.hom) ⟶ G) (hg' : g'.left = spMap (algebraMap S (DualNumber S)) ≫ g) {n : ℕ}
    (u : Fin n → (tEpsG (g ≫ G.hom) ⟶ G))
    (hu : ∀ a, spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ (u a).left = (1 : Over.mk (g ≫ G.hom) ⟶ G).left) :
    spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ (g' * (List.ofFn u).prod).left = g := by
  have h1 : redOver (g ≫ G.hom) ≫ (List.ofFn u).prod = 1 := by
    refine redOver_comp_prod _ _ fun w hw => ?_
    obtain ⟨a, rfl⟩ := (List.mem_ofFn' u w).1 hw
    exact Over.OverMorphism.ext (hu a)
  change (redOver (g ≫ G.hom) ≫ (g' * (List.ofFn u).prod)).left = g
  rw [MonObj.comp_mul, h1, _root_.mul_one]
  change spMap _ ≫ g'.left = g
  rw [hg', ← Category.assoc, spMap_fst_algebraMap, Category.id_comp]

end GlobalTheory.VertSpanZero
