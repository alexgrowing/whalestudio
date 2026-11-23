import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GermSys
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeAt
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ValAtCompLocalHomStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.Ar.Flat.CPoint

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.CPoint.PointVal

variable {X : Scheme.{0}} {Ω : Type} [Field Ω]

def baseFn {O : Type} [CommRing O] (s : X ⟶ Sp O) (o : O) : Γ(X, ⊤) :=
  s.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom o)

set_option backward.isDefEq.respectTransparency false in

theorem baseFn_value {O R : Type} [CommRing O] [CommRing R] [IsLocalRing R] (s : X ⟶ Sp O) (f : Sp R ⟶ X)
    (φ : O →+* R) (hf : f ≫ s = spMap φ) (o : O) :
    (Scheme.stalkClosedPointTo f).hom (X.presheaf.germ ⊤ (centre f) trivial (baseFn s o)) = φ o := by
  have e : X.presheaf.germ ⊤ (f (IsLocalRing.closedPoint R)) trivial ≫ Scheme.stalkClosedPointTo f =
      f.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of R)).hom := by
    rw [Scheme.germ_stalkClosedPointTo]
    simp [Iso.trans_hom, Scheme.Hom.appTop]
  have e2 : (Scheme.ΓSpecIso (CommRingCat.of O)).inv ≫ s.appTop ≫ f.appTop ≫
      (Scheme.ΓSpecIso (CommRingCat.of R)).hom = CommRingCat.ofHom φ := by
    rw [← Category.assoc s.appTop, ← Scheme.Hom.comp_appTop, hf, Scheme.ΓSpecIso_naturality,
      Iso.inv_hom_id_assoc]
  rw [← e] at e2
  exact congrArg (fun q => q.hom o) e2

set_option backward.isDefEq.respectTransparency false in

theorem genMap_germ (ξ : Sp Ω ⟶ X) (p : Cpt ξ) (g : Γ(X, ⊤)) :
    genMap ξ p (X.presheaf.germ ⊤ p.1 trivial g) =
      (Scheme.stalkClosedPointTo ξ).hom (X.presheaf.germ ⊤ (genPt ξ) trivial g) := by
  have e := TopCat.Presheaf.germ_stalkSpecializes X.presheaf (U := ⊤) (x := genPt ξ) (y := p.1) trivial p.2
  have e2 := congrArg (fun q => (q ≫ Scheme.stalkClosedPointTo ξ).hom g) e
  exact e2

set_option backward.isDefEq.respectTransparency false in

theorem genMap_specializes (ξ : Sp Ω ⟶ X) (p q : Cpt ξ) (h : p.1 ⤳ q.1) (s : X.presheaf.stalk q.1) :
    genMap ξ p ((X.presheaf.stalkSpecializes h).hom s) = genMap ξ q s := by
  have e := TopCat.Presheaf.stalkSpecializes_comp X.presheaf p.2 h
  have e2 := congrArg (fun r => (r ≫ Scheme.stalkClosedPointTo ξ).hom s) e
  exact e2

theorem exists_inv {A L₁ L₂ : Type} [CommRing A] [Field L₁] [Field L₂] (f₁ : A →+* L₁) (f₂ : A →+* L₂)
    (hl : ∀ b, IsUnit (f₂ b) → IsUnit b) (g : A) (a₁ : L₁) (a₂ : L₂) (ha : a₂ ≠ 0)
    (h₁ : f₁ g = a₁⁻¹) (h₂ : f₂ g = a₂⁻¹) : ∃ u, f₁ u = a₁ ∧ f₂ u = a₂ := by
  obtain ⟨g, rfl⟩ := hl g (by rw [h₂]; exact (inv_ne_zero ha).isUnit)
  refine ⟨(g⁻¹ : Aˣ), ?_, ?_⟩
  · have := map_units_inv f₁.toMonoidHom g
    refine this.trans ?_
    show (f₁ g)⁻¹ = _
    rw [h₁, inv_inv]
  · have := map_units_inv f₂.toMonoidHom g
    refine this.trans ?_
    show (f₂ g)⁻¹ = _
    rw [h₂, inv_inv]

def valMap (ξ : Sp Ω ⟶ X) (p : Cpt ξ) (hi : Function.Injective (genMap ξ p)) {R : Type} [CommRing R]
    (ev : X.presheaf.stalk p.1 →+* R) : regAt ξ p →+* R :=
  ev.comp (RingEquiv.ofBijective (genMap ξ p).rangeRestrict
    ⟨fun _ _ h => hi (congrArg Subtype.val h), (genMap ξ p).rangeRestrict_surjective⟩).symm.toRingHom

theorem valMap_genMap (ξ : Sp Ω ⟶ X) (p : Cpt ξ) (hi : Function.Injective (genMap ξ p)) {R : Type} [CommRing R]
    (ev : X.presheaf.stalk p.1 →+* R) (s : X.presheaf.stalk p.1) (h : genMap ξ p s ∈ regAt ξ p) :
    valMap ξ p hi ev ⟨genMap ξ p s, h⟩ = ev s := by
  have : (RingEquiv.ofBijective (genMap ξ p).rangeRestrict
      ⟨fun _ _ h => hi (congrArg Subtype.val h), (genMap ξ p).rangeRestrict_surjective⟩).symm
      ⟨genMap ξ p s, h⟩ = s := by
    rw [RingEquiv.symm_apply_eq]
    rfl
  show ev _ = ev s
  exact congrArg ev this

variable {O F V K : Type} [CommRing O] [Field F] [CommRing V] [IsLocalRing V] [Field K] [Algebra V K]

theorem exists_germ (ξ : Sp Ω ⟶ X) (s : X ⟶ Sp O) (inc : F →+* Ω) (β : O →+* F) (βK : F →+* K) (y : Sp K ⟶ X)
    (hξ : ξ ≫ s = spMap (inc.comp β)) (hy : y ≫ s = spMap (βK.comp β)) (h₁ : genPt ξ ⤳ centre y) (x : F)
    (hx : x ∈ β.range ∨ x⁻¹ ∈ β.range) :
    ∃ u : X.presheaf.stalk (centre y), genMap ξ ⟨_, h₁⟩ u = inc x ∧ (Scheme.stalkClosedPointTo y).hom u = βK x := by
  have key : ∀ o : O, genMap ξ ⟨_, h₁⟩ (X.presheaf.germ ⊤ (centre y) trivial (baseFn s o)) = inc (β o) ∧
      (Scheme.stalkClosedPointTo y).hom (X.presheaf.germ ⊤ (centre y) trivial (baseFn s o)) = βK (β o) := by
    intro o
    refine ⟨?_, baseFn_value s y (βK.comp β) hy o⟩
    exact (genMap_germ ξ ⟨_, h₁⟩ (baseFn s o)).trans (baseFn_value s ξ (inc.comp β) hξ o)
  by_cases h0 : x = 0
  · subst h0
    exact ⟨0, (map_zero _).trans (map_zero inc).symm,
      (map_zero (Scheme.stalkClosedPointTo y).hom).trans (map_zero βK).symm⟩
  rcases hx with ⟨o, rfl⟩ | ⟨o, ho⟩
  · exact ⟨_, key o⟩
  obtain ⟨k1, k2⟩ := key o
  rw [ho] at k1 k2
  exact exists_inv (genMap ξ ⟨_, h₁⟩) (Scheme.stalkClosedPointTo y).hom
    (fun b hb => (Scheme.isLocalHom_stalkClosedPointTo' y).map_nonunit b hb) _ (inc x) (βK x) ((map_ne_zero βK).2 h0)
    (k1.trans (map_inv₀ inc x)) (k2.trans (map_inv₀ βK x))

theorem val_abs (ξ : Sp Ω ⟶ X) (hg : IsCptGen ξ) (s : X ⟶ Sp O) (inc : F →+* Ω) (β : O →+* F) (βK : F →+* K)
    (y : Sp K ⟶ X) (z : Sp V ⟶ X) (hξ : ξ ≫ s = spMap (inc.comp β)) (hy : y ≫ s = spMap (βK.comp β))
    (hz : spMap (algebraMap V K) ≫ z = y) (h₁ : genPt ξ ⤳ centre y)
    (hF : ∀ x : F, x ∈ β.range ∨ x⁻¹ ∈ β.range) :
    ∃ (h₂ : genPt ξ ⤳ centre z) (ψ : regAt ξ ⟨_, h₁⟩ →+* K),
      centre y ⤳ centre z ∧ regAt ξ ⟨_, h₂⟩ ≤ regAt ξ ⟨_, h₁⟩ ∧
      (∀ a : regAt ξ ⟨_, h₁⟩, ValAt ξ y (a : Ω) (ψ a)) ∧
      (∀ (a : Ω) (r : K), ValAt ξ y a r → ∃ h, ψ ⟨a, h⟩ = r) ∧
      (∀ (a : Ω) (h : a ∈ regAt ξ ⟨_, h₁⟩), a ∈ regAt ξ ⟨_, h₂⟩ → ψ ⟨a, h⟩ ∈ (algebraMap V K).range) ∧
      ∀ x : F, ∃ h : inc x ∈ regAt ξ ⟨_, h₁⟩, ψ ⟨_, h⟩ = βK x := by
  have hsp : centre y ⤳ centre z := by
    subst hz
    exact (IsLocalRing.specializes_closedPoint _).map z.continuous
  have h₂ : genPt ξ ⤳ centre z := h₁.trans hsp
  let ψ : regAt ξ ⟨_, h₁⟩ →+* K := valMap ξ ⟨_, h₁⟩ (hg.inj _) (Scheme.stalkClosedPointTo y).hom
  have c3 : ∀ a : regAt ξ ⟨_, h₁⟩, ValAt ξ y (a : Ω) (ψ a) := by
    rintro ⟨_, s', rfl⟩
    exact ⟨h₁, s', rfl, (valMap_genMap ξ ⟨_, h₁⟩ (hg.inj _) _ s' _).symm⟩
  have c4 : ∀ (a : Ω) (r : K), ValAt ξ y a r → ∃ h, ψ ⟨a, h⟩ = r := by
    rintro a r ⟨h, s', rfl, rfl⟩
    exact ⟨⟨s', rfl⟩, valMap_genMap ξ ⟨_, h₁⟩ (hg.inj _) _ s' _⟩
  refine ⟨h₂, ψ, hsp, ?_, c3, c4, ?_, ?_⟩
  · rintro _ ⟨s', rfl⟩
    refine ⟨(X.presheaf.stalkSpecializes hsp).hom s', ?_⟩
    exact genMap_specializes ξ ⟨_, h₁⟩ ⟨_, h₂⟩ hsp s'
  · rintro a h ⟨s', rfl⟩
    have v : ValAt ξ z (genMap ξ ⟨_, h₂⟩ s') ((Scheme.stalkClosedPointTo z).hom s') := ⟨h₂, s', rfl, rfl⟩
    have v' := GlobalTheory.T.valAt_comp_local_hom X Ω ξ V K (algebraMap V K) z _ _ v (by rw [hz]; exact h₁)
    rw [hz] at v'
    obtain ⟨h', e⟩ := c4 _ _ v'
    exact ⟨_, e.symm⟩
  · intro x
    obtain ⟨u, e1, e2⟩ := exists_germ ξ s inc β βK y hξ hy h₁ x (hF x)
    obtain ⟨h, e⟩ := c4 _ _ (⟨h₁, u, e1, e2⟩ : ValAt ξ y (inc x) (βK x))
    exact ⟨h, e⟩

end GlobalTheory.CompanionTheory.Ar.Flat.CPoint.PointVal

namespace GlobalTheory.CompanionTheory.Ar.Flat.CPoint

theorem point_val : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (β : O →+* c.F) (Y : Model Xo c β) (U : Set (Xo.XF c)) (Z : CptOver Y U) (p : Nat.Primes) (κ : c.F →+* ℂ_[p]) (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K] (j : K →+* ℂ_[p]) (βK : c.F →+* K) (y : Sp K ⟶ Xo.XF c) (z : Sp V ⟶ Y.X),
    Function.Injective β → (∀ x : c.F, ‖κ x‖ ≤ 1 ↔ x ∈ β.range) → (∀ a : K, ‖j a‖ ≤ 1 ↔ a ∈ (algebraMap V K).range) →
    j.comp βK = κ → y ≫ pullback.snd _ _ = spMap βK → Set.range y ⊆ U → spMap (algebraMap V K) ≫ z = y ≫ Y.j →
    ∃ (h₁ : genPt (Z.ξ₀ ≫ Y.j) ⤳ centre (y ≫ Y.j)) (h₂ : genPt (Z.ξ₀ ≫ Y.j) ⤳ centre z)
      (ψ : regAt (Z.ξ₀ ≫ Y.j) ⟨_, h₁⟩ →+* K),
      centre (y ≫ Y.j) ⤳ centre z ∧ regAt (Z.ξ₀ ≫ Y.j) ⟨_, h₂⟩ ≤ regAt (Z.ξ₀ ≫ Y.j) ⟨_, h₁⟩ ∧
      (∀ a : regAt (Z.ξ₀ ≫ Y.j) ⟨_, h₁⟩, ValAt (Z.ξ₀ ≫ Y.j) (y ≫ Y.j) (a : Z.Ω) (ψ a)) ∧
      (∀ (a : Z.Ω) (r : K), ValAt (Z.ξ₀ ≫ Y.j) (y ≫ Y.j) a r → ∃ h, ψ ⟨a, h⟩ = r) ∧
      (∀ (a : Z.Ω) (h : a ∈ regAt (Z.ξ₀ ≫ Y.j) ⟨_, h₁⟩), a ∈ regAt (Z.ξ₀ ≫ Y.j) ⟨_, h₂⟩ →
        ψ ⟨a, h⟩ ∈ (algebraMap V K).range) ∧
      ∀ x : c.F, ∃ h : Z.inc x ∈ regAt (Z.ξ₀ ≫ Y.j) ⟨_, h₁⟩, ψ ⟨_, h⟩ = βK x := by
  intro E _ _ _ H D l Xo c O _ _ _ β Y U Z p κ V K _ _ _ _ _ _ j βK y z hβ hκ hj hjk hy hU hz
  have hsj : Y.j ≫ Y.s = pullback.snd _ _ ≫ spMap β := by
    rw [Model.j, Category.assoc, pullback.condition, ← Category.assoc, Y.jQ_over]
  have hξ : (Z.ξ₀ ≫ Y.j) ≫ Y.s = spMap (Z.inc.comp β) := by
    rw [Category.assoc, hsj, ← Category.assoc, Z.over_inc, ← Spec.map_comp]
    rfl
  have hy' : (y ≫ Y.j) ≫ Y.s = spMap (βK.comp β) := by
    rw [Category.assoc, hsj, ← Category.assoc, hy, ← Spec.map_comp]
    rfl
  have h₁ : genPt (Z.ξ₀ ≫ Y.j) ⤳ centre (y ≫ Y.j) :=
    ((Z.closure _).1 (hU ⟨IsLocalRing.closedPoint K, rfl⟩)).map Y.j.continuous
  have hF : ∀ x : c.F, x ∈ β.range ∨ x⁻¹ ∈ β.range := by
    intro x
    by_cases h : ‖κ x‖ ≤ 1
    · exact Or.inl ((hκ x).1 h)
    · refine Or.inr ((hκ _).1 ?_)
      rw [map_inv₀, norm_inv]
      exact inv_le_one_of_one_le₀ (not_le.1 h).le
  obtain ⟨h₂, ψ, r⟩ := PointVal.val_abs (Z.ξ₀ ≫ Y.j) Z.gen Y.s Z.inc β βK (y ≫ Y.j) z hξ hy' hz h₁ hF
  exact ⟨h₁, h₂, ψ, r⟩

end GlobalTheory.CompanionTheory.Ar.Flat.CPoint
