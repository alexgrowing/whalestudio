import Mathlib
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.OpensRangeChartYSupOpensRangeChartZ
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.AddXYZOrChordXYZOrOriginXYZNeZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.EigLatBasis
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.WeierstrassCurve GlobalTheory.AddLaw

namespace GlobalTheory.CoordFn

theorem isIso_appLE_of_opensRange {X Y : Scheme.{0}} (f : X ⟶ Y) [IsOpenImmersion f]
    (U : Y.Opens) (hU : f.opensRange = U) (h : ⊤ ≤ f ⁻¹ᵁ U) : IsIso (f.appLE U ⊤ h) := by
  subst hU
  have h1 : IsIso (f.app f.opensRange) := Scheme.Hom.isIso_app f _ le_rfl
  have h2 : (⊤ : X.Opens) = f ⁻¹ᵁ f.opensRange := le_antisymm h le_top
  have h3 : IsIso (homOfLE h) := by
    have : homOfLE h = eqToHom h2 := rfl
    rw [this]; infer_instance
  rw [Scheme.Hom.appLE]
  infer_instance

theorem appLE_SpecMap_comp {Y : Scheme.{0}} {A B : CommRingCat.{0}} (f : Spec B ⟶ Y) (g : B ⟶ A)
    (U : Y.Opens) (h : ⊤ ≤ f ⁻¹ᵁ U) (p : Spec A ⟶ Y) (hp : p = Spec.map g ≫ f)
    (h' : ⊤ ≤ p ⁻¹ᵁ U) :
    p.appLE U ⊤ h' ≫ (Scheme.ΓSpecIso A).hom = f.appLE U ⊤ h ≫ (Scheme.ΓSpecIso B).hom ≫ g := by
  subst hp
  have e1 : (Spec.map g).appTop = (Spec.map g).appLE ⊤ ⊤ le_top :=
    Scheme.Hom.app_eq_appLE (Spec.map g)
  have e2 := Scheme.Hom.appLE_comp_appLE (Spec.map g) f U ⊤ ⊤ h le_top
  rw [← Scheme.ΓSpecIso_naturality, e1, ← Category.assoc, e2]

theorem appLE_structure {Y : Scheme.{0}} {A B : CommRingCat.{0}} (f : Spec B ⟶ Y) (g : A ⟶ B)
    (U : Y.Opens) (h : ⊤ ≤ f ⁻¹ᵁ U) (t : Y ⟶ Spec A) (ht : f ≫ t = Spec.map g) :
    (Scheme.ΓSpecIso A).inv ≫ t.appLE ⊤ U le_top ≫ f.appLE U ⊤ h ≫ (Scheme.ΓSpecIso B).hom = g := by
  have e2 := Scheme.Hom.appLE_comp_appLE f t ⊤ U ⊤ le_top h
  have e1 : ∀ (q : Spec B ⟶ Spec A) (hq : ⊤ ≤ q ⁻¹ᵁ ⊤), q = Spec.map g →
      q.appLE ⊤ ⊤ hq = (Spec.map g).appTop := by
    rintro _ _ rfl
    exact (Scheme.Hom.app_eq_appLE (Spec.map g)).symm
  rw [← Category.assoc (t.appLE ⊤ U le_top), e2, e1 _ _ ht, Scheme.ΓSpecIso_naturality,
    Iso.inv_hom_id_assoc]

theorem top_le_preimage {R : Type} [CommRing R] (W : WeierstrassCurve R) (i : Fin 3) :
    ⊤ ≤ awayChart W i ⁻¹ᵁ coordOpen W i := by
  rw [← opensRange_awayChart, Scheme.Hom.preimage_opensRange]

theorem surjective_eval₂Hom_awayCoord {R : Type} [CommRing R] (W : WeierstrassCurve R)
    (i : Fin 3) :
    Function.Surjective (MvPolynomial.eval₂Hom (awayConst W i) (awayCoord W i)) := by
  intro x
  obtain ⟨n, a, ha, rfl⟩ :=
    HomogeneousLocalization.Away.mk_surjective (grading W) (coord_mem W i) x
  rw [← evalHom_awayCoord]
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
  exact ⟨p, rfl⟩

theorem exists_coordFn : ∀ (R : Type) [CommRing R] (W : WeierstrassCurve R), ∃ c : ∀ i j : Fin 3, Γ(scheme W, coordOpen W i), (∀ (i j : Fin 3) (A : Type) [CommRing A] (ρ : R →+* A) (P : Fin 3 → A) (hP : IsUnimodularSol (W.map ρ) P) (h : ⊤ ≤ ptHom W ρ P hP ⁻¹ᵁ coordOpen W i), (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom (((ptHom W ρ P hP).appLE (coordOpen W i) ⊤ h).hom (c i j)) * P i = P j) ∧ ∀ i, Function.Surjective (MvPolynomial.eval₂Hom (((toSpec W).appLE ⊤ (coordOpen W i) le_top).hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom) (c i)) := by
  intro R _ W
  let φ : ∀ i : Fin 3, Γ(scheme W, coordOpen W i) ⟶ CommRingCat.of (AwayRing W i) := fun i =>
    (awayChart W i).appLE (coordOpen W i) ⊤ (top_le_preimage W i) ≫ (Scheme.ΓSpecIso _).hom
  have hφ : ∀ i, Function.Bijective (φ i).hom := fun i => by
    have := isIso_appLE_of_opensRange (awayChart W i) _ (opensRange_awayChart W i)
      (top_le_preimage W i)
    have : IsIso (φ i) := by dsimp only [φ]; infer_instance
    exact ConcreteCategory.bijective_of_isIso (φ i)
  choose c hc using fun i j => (hφ i).2 (awayCoord W i j)
  refine ⟨c, ?_, ?_⟩
  · intro i j A _ ρ P hP h
    have hi : IsUnit (P i) := by
      rw [ptHom_preimage_coordOpen] at h
      have h1 : PrimeSpectrum.basicOpen (P i) = ⊤ := top_le_iff.mp h
      by_contra hn
      obtain ⟨m, hm, hx⟩ := exists_max_ideal_of_mem_nonunits hn
      have : (⟨m, hm.isPrime⟩ : PrimeSpectrum A) ∈ PrimeSpectrum.basicOpen (P i) := by
        rw [h1]; trivial
      exact this hx
    have e := appLE_SpecMap_comp (awayChart W i)
      (CommRingCat.ofHom (awayEval W i ρ P hP.equation hi)) (coordOpen W i)
      (top_le_preimage W i) _ (ptHom_eq_awayChart W i ρ P hP hi) h
    have e2 := congrArg (fun k => k.hom (c i j)) e
    have e3 : (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom
        (((ptHom W ρ P hP).appLE (coordOpen W i) ⊤ h).hom (c i j)) =
        awayEval W i ρ P hP.equation hi ((φ i).hom (c i j)) := e2
    rw [e3, hc, awayEval_awayCoord_mul]
  · intro i
    have e := appLE_structure (awayChart W i) (CommRingCat.ofHom (awayConst W i)) (coordOpen W i)
      (top_le_preimage W i) (toSpec W) (awayChart_toSpec W i)
    have key : (φ i).hom.comp (MvPolynomial.eval₂Hom
        (((toSpec W).appLE ⊤ (coordOpen W i) le_top).hom.comp
          (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom) (c i)) =
        MvPolynomial.eval₂Hom (awayConst W i) (awayCoord W i) := by
      refine MvPolynomial.ringHom_ext (fun r => ?_) (fun j => ?_)
      · rw [RingHom.comp_apply, MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_C]
        exact congrArg (fun k => k.hom r) e
      · rw [RingHom.comp_apply, MvPolynomial.eval₂Hom_X', MvPolynomial.eval₂Hom_X', hc]
    intro y
    obtain ⟨p, hp⟩ := surjective_eval₂Hom_awayCoord W i ((φ i).hom y)
    exact ⟨p, (hφ i).1 ((RingHom.congr_fun key p).trans hp)⟩

end GlobalTheory.CoordFn
