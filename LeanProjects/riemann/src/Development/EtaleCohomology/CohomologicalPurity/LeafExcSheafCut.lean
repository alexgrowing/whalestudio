import Development.EtaleCohomology.CohomologicalPurity.LeafExcPf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity

def LeafFreeCok : Prop := ∀ (R : Type) [CommRing R] {A' B' A B : PSh} (i' : A' ⟶ B') (i : A ⟶ B) (a : A' ⟶ A)
  (b : B' ⟶ B) (w : i' ≫ b = a ≫ i),
  (∀ (T : Scheme.{0}) (y : B'.obj (op T)) (x : A.obj (op T)), i.app (op T) x = b.app (op T) y →
    ∃ x' : A'.obj (op T), i'.app (op T) x' = y) →
  (∀ (T : Scheme.{0}) (y : B.obj (op T)), ∃ S ∈ Scheme.etaleTopology T, ∀ ⦃V : Scheme.{0}⦄ (g : V ⟶ T), S g →
    (∃ x : A.obj (op V), i.app (op V) x = B.map g.op y) ∨ ∃ y' : B'.obj (op V), b.app (op V) y' = B.map g.op y) →
  (∀ (T : Scheme.{0}) (y₁ y₂ : B'.obj (op T)), b.app (op T) y₁ = b.app (op T) y₂ →
    ∃ S ∈ Scheme.etaleTopology T, ∀ ⦃V : Scheme.{0}⦄ (g : V ⟶ T), S g →
      B'.map g.op y₁ = B'.map g.op y₂ ∨ ∃ x : A.obj (op V), i.app (op V) x = b.app (op V) (B'.map g.op y₁)) →
  IsIso (cokernel.map ((free R).map i') ((free R).map i) ((free R).map a) ((free R).map b)
    (by rw [← Functor.map_comp, ← Functor.map_comp, w]))

def LeafSurjGeo : Prop := ∀ {X' X Z : Scheme.{0}} (f : X' ⟶ X) [Etale f] (ι' : Z ⟶ X') (ι : Z ⟶ X)
  [IsClosedImmersion ι], IsPullback ι' (𝟙 Z) f ι → ∀ (U : X.Opens), (U : Set X) = (Set.range ι)ᶜ →
  ∀ {T : Scheme.{0}} (t : T ⟶ X), ∃ S ∈ Scheme.etaleTopology T, ∀ ⦃V : Scheme.{0}⦄ (g : V ⟶ T), S g →
    (∃ x : V ⟶ U.toScheme, x ≫ U.ι = g ≫ t) ∨ ∃ y : V ⟶ X', y ≫ f = g ≫ t

def LeafInjGeo : Prop := ∀ {X' X Z : Scheme.{0}} (f : X' ⟶ X) [Etale f] (ι' : Z ⟶ X') (ι : Z ⟶ X)
  [IsClosedImmersion ι], IsPullback ι' (𝟙 Z) f ι → ∀ (U : X.Opens), (U : Set X) = (Set.range ι)ᶜ →
  ∀ {T : Scheme.{0}} (y₁ y₂ : T ⟶ X'), y₁ ≫ f = y₂ ≫ f →
    ∃ S ∈ Scheme.etaleTopology T, ∀ ⦃V : Scheme.{0}⦄ (g : V ⟶ T), S g →
      g ≫ y₁ = g ≫ y₂ ∨ ∃ x : V ⟶ U.toScheme, x ≫ U.ι = (g ≫ y₁) ≫ f

theorem excSheaf_cart_preimage {X' X T : Scheme.{0}} (f : X' ⟶ X) (U : X.Opens) (y : T ⟶ X') (x : T ⟶ U.toScheme)
    (hx : x ≫ U.ι = y ≫ f) : ∃ x' : T ⟶ (f ⁻¹ᵁ U).toScheme, x' ≫ (f ⁻¹ᵁ U).ι = y :=
  ⟨(isPullback_morphismRestrict f U).lift x y hx, (isPullback_morphismRestrict f U).lift_snd _ _ _⟩

theorem LeafExcSheaf_of (hF : LeafFreeCok) (hS : LeafSurjGeo) (hI : LeafInjGeo) : LeafExcSheaf := by
  intro R _ X' X Z f _ ι' ι _ hp U' U hU h
  subst h
  exact hF R (yoneda.map (f ⁻¹ᵁ U).ι) (yoneda.map U.ι) (yoneda.map (f.resLE U (f ⁻¹ᵁ U) le_rfl)) (yoneda.map f)
    (by rw [← Functor.map_comp, ← Functor.map_comp, Scheme.Hom.resLE_comp_ι])
    (fun T y x hx => excSheaf_cart_preimage f U y x hx) (fun T y => hS f ι' ι hp U hU y)
    (fun T y₁ y₂ h => hI f ι' ι hp U hU y₁ y₂ h)

end LateralTheory.CohomologicalPurity
