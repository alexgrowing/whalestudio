import Development.EtaleCohomology.EtaleSheaves.LeafChartRing

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex GlobalTheory.EtC

namespace LateralTheory.E.LeafExcRingPf
open LateralTheory.E.t_E6Cut

example {X : Scheme.{0}} (p : ℕ) (T : Scheme.{0}) : Sx (sch.obj X) p T = (T ⟶ X) := rfl
example {X Y : Scheme.{0}} (f : X ⟶ Y) (p : ℕ) (T : Scheme.{0}) (u : Sx (sch.obj X) p T) :
  sxMap (sch.map f) u = (show T ⟶ X from u) ≫ f := rfl
example {X : Scheme.{0}} (p : ℕ) {V T : Scheme.{0}} (k : V ⟶ T) (u : Sx (sch.obj X) p T) :
  sxRes k u = k ≫ (show T ⟶ X from u) := rfl

instance monoSch {X Y : Scheme.{0}} (f : X ⟶ Y) [Mono f] : Mono (sch.map f) := by
  have h1 : ∀ n, Mono ((sch.map f).app n) := fun n => by
    have h2 : ∀ T, Mono (((sch.map f).app n).app T) := fun T => by
      rw [CategoryTheory.mono_iff_injective]
      intro u v h
      exact (cancel_mono f).1 h
    exact NatTrans.mono_of_mono_app _
  exact NatTrans.mono_of_mono_app _

theorem preim_eq {B W : Type} [CommRing B] [CommRing W] (α : B →+* W) (I : Ideal B)
    (U : (Spec (CommRingCat.of B)).Opens) (U' : (Spec (CommRingCat.of W)).Opens)
    (hU : IsCompl' I U) (hU' : IsCompl' (I.map α) U') : U' = Spec.map (CommRingCat.ofHom α) ⁻¹ᵁ U := by
  ext x
  change x ∈ U' ↔ (Spec.map (CommRingCat.ofHom α)) x ∈ U
  rw [hU', hU, Ideal.map_le_iff_le_comap]
  rfl

def LeafCov1 : Prop := ∀ {B W : Type} [CommRing B] [CommRing W] (α : B →+* W) (I : Ideal B), α.Etale → QIso α I →
  ∀ (U : (Spec (CommRingCat.of B)).Opens), IsCompl' I U → ∀ (T : Scheme.{0}) (y : T ⟶ Spec (CommRingCat.of B)),
  EtLoc T fun V k => (∃ u : V ⟶ (U : Scheme.{0}), u ≫ U.ι = k ≫ y) ∨
    ∃ a : V ⟶ Spec (CommRingCat.of W), a ≫ Spec.map (CommRingCat.ofHom α) = k ≫ y

def LeafCov2 : Prop := ∀ {B W : Type} [CommRing B] [CommRing W] (α : B →+* W) (I : Ideal B), α.Etale → QIso α I →
  ∀ (U : (Spec (CommRingCat.of B)).Opens), IsCompl' I U → ∀ (T : Scheme.{0}) (a b : T ⟶ Spec (CommRingCat.of W)),
  a ≫ Spec.map (CommRingCat.ofHom α) = b ≫ Spec.map (CommRingCat.ofHom α) →
  EtLoc T fun V k => k ≫ a = k ≫ b ∨
    ∃ u : V ⟶ (U : Scheme.{0}), u ≫ U.ι = k ≫ a ≫ Spec.map (CommRingCat.ofHom α)

def LeafPb : Prop := ∀ (R : Type) [CommRing R] (F : Shv R) (c : ℤ) {X Y : Scheme.{0}} (g : Y ⟶ X) (U : X.Opens),
  Conn R F c (pullback.snd (sch.map U.ι) (sch.map g)) ↔ Conn R F c (sch.map (g ⁻¹ᵁ U).ι)

theorem LeafExcRing_of (hE : LeafExc) (hC1 : LeafCov1) (hC2 : LeafCov2) (hP : LeafPb) : LeafExcRing := by
  intro hA1 R _ F c B W _ _ α I hα hQ U U' hU hU'
  obtain rfl := preim_eq α I U U' hU hU'
  refine (hE hA1 R F c (sch.map U.ι) (sch.map (Spec.map (CommRingCat.ofHom α))) ?_ ?_).trans (hP R F c _ U)
  · intro p T y
    exact hC1 α I hα hQ U hU T y
  · intro p T a b h
    exact hC2 α I hα hQ U hU T a b h

end LateralTheory.E.LeafExcRingPf
