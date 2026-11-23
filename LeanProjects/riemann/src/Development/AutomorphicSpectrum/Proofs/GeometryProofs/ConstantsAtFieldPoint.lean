import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.LevelSectionsExactKernelLocusOpen
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ClopenCondOnto
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Development.AutomorphicSpectrum.PublishedTheorems.Geometry₂.GagaSections
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsGenericFlag
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.StalkClosedPointToGermTop
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.ConstVal

def constGerm {X : Scheme.{0}} {O : Type} [CommRing O] (s : X ⟶ Spec (CommRingCat.of O)) (x : X) (o : O) :
    X.presheaf.stalk x :=
  (X.presheaf.germ ⊤ x trivial).hom (s.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom o))

theorem genMap_constGerm {X : Scheme.{0}} {Ω O : Type} [Field Ω] [CommRing O] (f : O →+* Ω)
    (ξ : Spec (CommRingCat.of Ω) ⟶ X) (s : X ⟶ Spec (CommRingCat.of O))
    (hs : ξ ≫ s = Spec.map (CommRingCat.ofHom f)) (p : Cpt ξ) (o : O) :
    genMap ξ p (constGerm s p.1 o) = f o := by
  letI : Algebra O Ω := f.toAlgebra
  exact ConstReg.genMap_germ_const ξ s hs p o

theorem genMap_self {X : Scheme.{0}} {F : Type} [Field F] (z : Spec (CommRingCat.of F) ⟶ X)
    (x : X.presheaf.stalk (genPt z)) :
    genMap z ⟨genPt z, specializes_rfl⟩ x = (Scheme.stalkClosedPointTo z).hom x := by
  have e₀ : X.presheaf.stalkSpecializes (specializes_rfl (x := genPt z)) ≫ Scheme.stalkClosedPointTo z =
      Scheme.stalkClosedPointTo z := by
    rw [TopCat.Presheaf.stalkSpecializes_refl]
    exact Category.id_comp _
  exact congrArg (fun q => q.hom x) e₀

def closedMap {X : Scheme.{0}} {F : Type} [Field F] (z : Spec (CommRingCat.of F) ⟶ X) :
    X.presheaf.stalk (centre z) →+* F :=
  (Scheme.stalkClosedPointTo z).hom

theorem closedPoint_constGerm {X : Scheme.{0}} {F O : Type} [Field F] [CommRing O] (f : O →+* F)
    (z : Spec (CommRingCat.of F) ⟶ X) (s : X ⟶ Spec (CommRingCat.of O))
    (hs : z ≫ s = Spec.map (CommRingCat.ofHom f)) (o : O) :
    closedMap z (constGerm s (centre z) o) = f o :=
  (genMap_self z _).symm.trans (genMap_constGerm f z s hs ⟨genPt z, specializes_rfl⟩ o)

theorem isUnit_constGerm {X : Scheme.{0}} {F O : Type} [Field F] [CommRing O] (f : O →+* F)
    (z : Spec (CommRingCat.of F) ⟶ X) (s : X ⟶ Spec (CommRingCat.of O))
    (hs : z ≫ s = Spec.map (CommRingCat.ofHom f)) (o : O) (ho : f o ≠ 0) :
    IsUnit (constGerm s (centre z) o) := by
  have h1 : IsUnit (closedMap z (constGerm s (centre z) o)) := by
    rw [closedPoint_constGerm f z s hs o]
    exact ho.isUnit
  haveI : IsLocalHom (closedMap z) := inferInstanceAs (IsLocalHom (Scheme.stalkClosedPointTo z).hom)
  exact isUnit_of_map_unit (closedMap z) _ h1

theorem map_frac {A L K O : Type} [CommRing A] [CommRing L] [Field K] [CommRing O] (β : O →+* K) (g : O → A)
    (φ : A →+* L) (e : K →+* L) (h : ∀ o, φ (g o) = e (β o)) {a b : O} {k : K} (hk : k * β b = β a)
    (u : Aˣ) (hu : (u : A) = g b) : φ (g a * ↑u⁻¹) = e k := by
  have hw : e (β b) * φ ↑u⁻¹ = 1 := by
    rw [← h b, ← hu, ← map_mul, u.mul_inv, map_one]
  rw [map_mul, h a, ← hk, map_mul, _root_.mul_assoc, hw, _root_.mul_one]

theorem valAt_of_frac {X : Scheme.{0}} {K Ω F O : Type} [Field K] [Field Ω] [Field F] [CommRing O]
    (β : O →+* K) (inc : K →+* Ω) (βF : K →+* F)
    (ξ : Spec (CommRingCat.of Ω) ⟶ X) (z : Spec (CommRingCat.of F) ⟶ X)
    (s : X ⟶ Spec (CommRingCat.of O))
    (hξ : ξ ≫ s = Spec.map (CommRingCat.ofHom (inc.comp β)))
    (hz : z ≫ s = Spec.map (CommRingCat.ofHom (βF.comp β)))
    (hfr : ∀ x : K, ∃ a b : O, β b ≠ 0 ∧ x * β b = β a)
    (h : genPt ξ ⤳ centre z) (k : K) : ValAt ξ z (inc k) (βF k) := by
  obtain ⟨a, b, hb, hk⟩ := hfr k
  obtain ⟨u, hu⟩ := isUnit_constGerm (βF.comp β) z s hz b ((map_ne_zero βF).2 hb)
  have e₁ : genMap ξ ⟨centre z, h⟩ (constGerm s (centre z) a * ↑u⁻¹) = inc k :=
    map_frac β (constGerm s (centre z)) (genMap ξ ⟨centre z, h⟩) inc
      (fun o => genMap_constGerm (inc.comp β) ξ s hξ ⟨centre z, h⟩ o) hk u hu
  have e₂ : closedMap z (constGerm s (centre z) a * ↑u⁻¹) = βF k :=
    map_frac β (constGerm s (centre z)) (closedMap z) βF
      (fun o => closedPoint_constGerm (βF.comp β) z s hz o) hk u hu
  exact ⟨h, _, e₁, e₂⟩

theorem constants_compose_structure {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
    {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} (Y : Model Xo c β)
    {R : Type} [CommRing R] (w : Sp R ⟶ Xo.XF c) (f : c.F →+* R) (hw : w ≫ pullback.snd _ _ = spMap f) :
    (w ≫ Y.j) ≫ Y.s = Spec.map (CommRingCat.ofHom (f.comp β)) := by
  have h1 : (w ≫ Y.j) ≫ Y.s = (w ≫ pullback.snd _ _) ≫ spMap β := by
    simp only [Model.j, Category.assoc]
    rw [pullback.condition, ← Category.assoc Y.jQ, Y.jQ_over]
  rw [h1, hw, CommRingCat.ofHom_comp, Spec.map_comp]

theorem valAt_inc : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (U : Set (Xo.XF c)) (Z : CptOver Y U) (F : Type) [Field F] (βF : c.F →+* F) (y : Sp F ⟶ Xo.XF c), (∀ x : c.F, ∃ a b : O, β b ≠ 0 ∧ x * β b = β a) → y ≫ pullback.snd _ _ = spMap βF → genPt (Z.ξ₀ ≫ Y.j) ⤳ centre (y ≫ Y.j) → ∀ k : c.F, ValAt (Z.ξ₀ ≫ Y.j) (y ≫ Y.j) (Z.inc k) (βF k) := by
  intro E _ _ _ H D l Xo c O _ β Y U Z F _ βF y hfr hy hsp k
  exact valAt_of_frac β Z.inc βF (Z.ξ₀ ≫ Y.j) (y ≫ Y.j) Y.s (constants_compose_structure Y _ _ Z.over_inc)
    (constants_compose_structure Y _ _ hy) hfr hsp k

end GlobalTheory.CompanionTheory.Ar.Flat.ConstVal
