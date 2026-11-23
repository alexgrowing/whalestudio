import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.JetGlue

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory

namespace ReciprocityTheory.ChartRestriction.G.TB.JGPf

universe u

theorem specMap_stalkCongr {X : Scheme.{u}} {x y : X} (e : x = y) :
    Spec.map (X.presheaf.stalkCongr (Inseparable.of_eq e)).hom ≫ X.fromSpecStalk x = X.fromSpecStalk y := by
  subst e
  simp

set_option maxHeartbeats 1000000 in

theorem ext_of_fromSpecStalk {Y X : Scheme.{u}} (f g : Y ⟶ X)
    (h : ∀ y, Y.fromSpecStalk y ≫ f = Y.fromSpecStalk y ≫ g) : f = g := by
  have hb : ∀ y, f y = g y := fun y => by
    have := congr($(h y) (IsLocalRing.closedPoint (Y.presheaf.stalk y)))
    change f (Y.fromSpecStalk y (IsLocalRing.closedPoint _)) = g (Y.fromSpecStalk y (IsLocalRing.closedPoint _)) at this
    rwa [Scheme.fromSpecStalk_closedPoint] at this
  have hbase : f.base = g.base := by ext y; exact hb y
  have hs : ∀ y, f.stalkMap y = (X.presheaf.stalkCongr (Inseparable.of_eq (hb y))).hom ≫ g.stalkMap y := by
    intro y
    apply Spec.map_injective
    rw [← cancel_mono (X.fromSpecStalk (f y))]
    rw [Scheme.SpecMap_stalkMap_fromSpecStalk, Spec.map_comp, Category.assoc, specMap_stalkCongr (hb y),
      Scheme.SpecMap_stalkMap_fromSpecStalk, h y]
  refine Scheme.Hom.ext' (LocallyRingedSpace.Hom.ext' ?_)
  have := SheafedSpace.hom_stalk_ext _ _ hbase hs
  exact congrArg InducedCategory.Hom.hom this

theorem comp_eq {A B C D : Scheme.{u}} (u : A ⟶ B) (v : B ⟶ C) (f g : C ⟶ D) (h : v ≫ f = v ≫ g) :
    (u ≫ v) ≫ f = (u ≫ v) ≫ g := by
  rw [Category.assoc, Category.assoc, h]

theorem jetGlue : JetGlueSt := by
  intro S _ κ _ m X f g h
  apply ext_of_fromSpecStalk
  intro y
  classical
  have hy := y.isPrime
  let 𝔭 : Ideal S := y.asIdeal.comap (algebraMap S (JetRing S κ m))
  have : 𝔭.IsPrime := Ideal.comap_isPrime _ _
  let ψ := (Scheme.ΓSpecIso (CommRingCat.of (JetRing S κ m))).inv ≫
    (Spec (CommRingCat.of (JetRing S κ m))).presheaf.germ ⊤ y trivial
  have hM : ∀ a : Algebra.algebraMapSubmonoid (JetRing S κ m) 𝔭.primeCompl, IsUnit (ψ.hom a) := by
    rintro ⟨a, ⟨s, hs, rfl⟩⟩
    refine (Scheme.mem_basicOpen _ ((Scheme.ΓSpecIso (CommRingCat.of (JetRing S κ m))).inv.hom
      (algebraMap S (JetRing S κ m) s)) y trivial).1 ?_
    rw [basicOpen_eq_of_affine]
    exact (PrimeSpectrum.mem_basicOpen _ _).2 hs
  let φ := IsLocalization.lift (S := JetLoc S κ m 𝔭) hM
  have hfac : ψ = CommRingCat.ofHom (algebraMap (JetRing S κ m) (JetLoc S κ m 𝔭)) ≫ CommRingCat.ofHom φ := by
    refine CommRingCat.hom_ext (RingHom.ext fun a => ?_)
    simp [φ]
  have e : (Spec (CommRingCat.of (JetRing S κ m))).fromSpecStalk y =
      Spec.map (CommRingCat.ofHom φ) ≫ Spec.map (CommRingCat.ofHom (algebraMap (JetRing S κ m) (JetLoc S κ m 𝔭))) := by
    rw [Spec.fromSpecStalk_eq, ← Spec.map_comp, ← hfac]
  rw [e]
  exact comp_eq _ _ f g (h 𝔭)

end ReciprocityTheory.ChartRestriction.G.TB.JGPf
