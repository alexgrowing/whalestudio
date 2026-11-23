import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHodgeLine
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCompCompareGeneric
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsExcisionNbhdAway

noncomputable section

open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.OrVert

namespace GlobalTheory.CompanionTheory.Ar.OrArch

theorem isLocalRing_of_value {Ω : Type} [Field Ω] (W : Subring Ω) (φ : W →+* ℂ)
    (hW : ∀ a : W, φ a ≠ 0 → IsUnit a) : IsLocalRing W := by
  haveI : Nontrivial W := φ.domain_nontrivial
  refine IsLocalRing.of_nonunits_add fun a b ha hb hu => ?_
  have h0 : ∀ c : W, c ∈ nonunits W → φ c = 0 := fun c hc => by_contra fun h => hc (hW c h)
  have := hu.map φ
  rw [map_add, h0 a ha, h0 b hb, add_zero] at this
  exact not_isUnit_zero this

theorem exists_stalkHom {X : Scheme.{0}} {Ω₁ Ω : Type} [Field Ω₁] [Field Ω]
    (ξ : Spec (CommRingCat.of Ω₁) ⟶ X) (i : Ω₁ →+* Ω) (W : Subring Ω) (φ : W →+* ℂ)
    (z : Spec (CommRingCat.of ℂ) ⟶ X) (hz : genPt ξ ⤳ centre z)
    (hv : ∀ (a : Ω₁) (r : ℂ), ValAt ξ z a r → ∃ h : i a ∈ W, φ ⟨_, h⟩ = r) :
    ∃ σ : X.presheaf.stalk (centre z) →+* W, (∀ s, (σ s : Ω) = i (genMap ξ ⟨centre z, hz⟩ s)) ∧
      ∀ s, φ (σ s) = (Scheme.stalkClosedPointTo z).hom s := by
  have hm : ∀ s, ValAt ξ z (genMap ξ ⟨centre z, hz⟩ s) ((Scheme.stalkClosedPointTo z).hom s) :=
    fun s => ⟨hz, s, rfl, rfl⟩
  exact ⟨(i.comp (genMap ξ ⟨centre z, hz⟩)).codRestrict W fun s => (hv _ _ (hm s)).1,
    fun _ => rfl, fun s => (hv _ _ (hm s)).2⟩

theorem isLocalHom_of_value {X : Scheme.{0}} {Ω : Type} [Field Ω] (W : Subring Ω) (φ : W →+* ℂ)
    (z : Spec (CommRingCat.of ℂ) ⟶ X) (σ : X.presheaf.stalk (centre z) →+* W)
    (hσ : ∀ s, φ (σ s) = (Scheme.stalkClosedPointTo z).hom s) : IsLocalHom σ :=
  ⟨fun s hs => GlobalTheory.CompanionTheory.Ar.CxVal.isUnit s (by rw [← hσ]; exact (hs.map φ).ne_zero)⟩

theorem domBy_of_stalkHom {X : Scheme.{0}} {Ω₁ Ω : Type} [Field Ω₁] [Field Ω]
    (ξ : Spec (CommRingCat.of Ω₁) ⟶ X) (i : Ω₁ →+* Ω) (q : Cpt ξ) (W : Subring Ω) (V : ValuationSubring Ω)
    (hWV : W ≤ V.toSubring) (hloc : IsLocalHom (Subring.inclusion hWV))
    (σ : X.presheaf.stalk q.1 →+* W) (hl : IsLocalHom σ) (hσ : ∀ s, (σ s : Ω) = i (genMap ξ q s)) :
    DomBy V.toSubring i ξ q := by
  refine ⟨?_, ?_⟩
  · rintro _ ⟨s, rfl⟩
    rw [← hσ]
    exact hWV (σ s).2
  · rintro _ ⟨s, rfl⟩ h0 hinv
    have hi : i (genMap ξ q s) ≠ 0 := (map_ne_zero i).2 h0
    have hu : IsUnit (Subring.inclusion hWV (σ s)) := by
      refine IsUnit.of_mul_eq_one (⟨_, hinv⟩ : V.toSubring) (Subtype.ext ?_)
      change ((σ s : W) : Ω) * (i (genMap ξ q s))⁻¹ = 1
      rw [hσ, mul_inv_cancel₀ hi]
    obtain ⟨u, rfl⟩ := isUnit_of_map_unit σ s (isUnit_of_map_unit (Subring.inclusion hWV) _ hu)
    exact ⟨(u⁻¹ : (X.presheaf.stalk q.1)ˣ).val, map_units_inv (genMap ξ q) u⟩

theorem point_closed {X Y : Scheme.{0}} (x : X) (f : X ⟶ Y) {R : Type} [CommRing R] [IsLocalRing R]
    (σ : X.presheaf.stalk x →+* R) (hl : IsLocalHom σ) :
    (spMap σ ≫ X.fromSpecStalk x ≫ f) (IsLocalRing.closedPoint R) = f x := by
  have : IsLocalHom (CommRingCat.ofHom σ).hom := hl
  change f (X.fromSpecStalk x (Spec.map (CommRingCat.ofHom σ) (IsLocalRing.closedPoint R))) = f x
  rw [Spec_closedPoint, Scheme.fromSpecStalk_closedPoint]

theorem spec_stalkHom {X : Scheme.{0}} {Ω₁ Ω : Type} [Field Ω₁] [Field Ω]
    (ξ : Spec (CommRingCat.of Ω₁) ⟶ X) (i : Ω₁ →+* Ω) (q : Cpt ξ) (W : Subring Ω)
    (σ : X.presheaf.stalk q.1 →+* W) (hσ : ∀ s, (σ s : Ω) = i (genMap ξ q s)) :
    spMap W.subtype ≫ spMap σ ≫ X.fromSpecStalk q.1 = spMap i ≫ ξ := by
  have e : W.subtype.comp σ = i.comp (genMap ξ q) := RingHom.ext hσ
  have e2 : spMap W.subtype ≫ spMap σ = spMap i ≫ spMap (genMap ξ q) :=
    (LieTangent.spec_comp σ W.subtype).trans
      ((congrArg (fun g => Spec.map (CommRingCat.ofHom g)) e).trans (LieTangent.spec_comp _ _).symm)
  rw [← Category.assoc, e2, Category.assoc]
  exact congrArg (spMap i ≫ ·) (LieTangent.spec_genMap ξ q)

theorem exists_common_point : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S S₀ : Finset ℕ) (Ω Ω₀ : Type) [Field Ω] [Field Ω₀] (K K₀ : Type) [Fintype K] [Fintype K₀] (J : K → Type) (J₀ : K₀ → Type) (y : (Σ k, J k) → Ω) (y₀ : (Σ k, J₀ k) → Ω₀) (𝔐 : HodgeCpt Y S y) (𝔐₀ : HodgeCpt Y S₀ y₀) (i : Ω₀ →+* Ω) (W : Subring Ω) (φ : W →+* ℂ) (z₁ : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X) (z₂ : Spec (CommRingCat.of ℂ) ⟶ 𝔐₀.X), 𝔐.ξ ≫ 𝔐.f = spMap i ≫ 𝔐₀.ξ ≫ 𝔐₀.f → (∀ a : W, φ a ≠ 0 → IsUnit a) → (∀ (a : Ω) (r : ℂ), ValAt 𝔐.ξ z₁ a r → ∃ h : a ∈ W, φ ⟨a, h⟩ = r) → (∀ (a : Ω₀) (r : ℂ), ValAt 𝔐₀.ξ z₂ a r → ∃ h : i a ∈ W, φ ⟨_, h⟩ = r) → ∃ (σ₁ : 𝔐.X.presheaf.stalk (centre z₁) →+* W) (σ₂ : 𝔐₀.X.presheaf.stalk (centre z₂) →+* W), (∀ s, (σ₁ s : Ω) = genMap 𝔐.ξ ⟨centre z₁, 𝔐.all _⟩ s) ∧ (∀ s, (σ₂ s : Ω) = i (genMap 𝔐₀.ξ ⟨centre z₂, 𝔐₀.all _⟩ s)) ∧ (∀ s, φ (σ₁ s) = (Scheme.stalkClosedPointTo z₁).hom s) ∧ (∀ s, φ (σ₂ s) = (Scheme.stalkClosedPointTo z₂).hom s) ∧ spMap σ₁ ≫ 𝔐.X.fromSpecStalk (centre z₁) ≫ 𝔐.f = spMap σ₂ ≫ 𝔐₀.X.fromSpecStalk (centre z₂) ≫ 𝔐₀.f := by
  intro E _ _ _ H D l Xo c Y S S₀ Ω Ω₀ _ _ K K₀ _ _ J J₀ y y₀ 𝔐 𝔐₀ i W φ z₁ z₂ hξ hW h₁ h₂
  haveI := isLocalRing_of_value W φ hW
  obtain ⟨σ₁, a₁, b₁⟩ := exists_stalkHom 𝔐.ξ (RingHom.id Ω) W φ z₁ (𝔐.all _) h₁
  obtain ⟨σ₂, a₂, b₂⟩ := exists_stalkHom 𝔐₀.ξ i W φ z₂ (𝔐₀.all _) h₂
  refine ⟨σ₁, σ₂, a₁, a₂, b₁, b₂, ?_⟩
  have l₁ := isLocalHom_of_value W φ z₁ σ₁ b₁
  have l₂ := isLocalHom_of_value W φ z₂ σ₂ b₂
  obtain ⟨V, hV⟩ := (LocalSubring.mk W).exists_le_valuationSubring
  obtain ⟨hWV, hloc⟩ := LocalSubring.le_def.1 hV
  have hc : 𝔐.f (centre z₁) = 𝔐₀.f (centre z₂) :=
    image_eq_of_domBy E H D l Xo c Y S S₀ Ω Ω₀ K K₀ J J₀ y y₀ 𝔐 𝔐₀ i hξ V ⟨centre z₁, 𝔐.all _⟩ ⟨centre z₂, 𝔐₀.all _⟩
      (domBy_of_stalkHom 𝔐.ξ (RingHom.id Ω) ⟨centre z₁, 𝔐.all _⟩ W V hWV hloc σ₁ l₁ a₁)
      (domBy_of_stalkHom 𝔐₀.ξ i ⟨centre z₂, 𝔐₀.all _⟩ W V hWV hloc σ₂ l₂ a₂)
  refine LieTangent.ext_of_injective (R := W) (φ := W.subtype) Subtype.val_injective ?_ ?_
  · exact (point_closed _ 𝔐.f σ₁ l₁).trans (hc.trans (point_closed _ 𝔐₀.f σ₂ l₂).symm)
  · have e₁ := spec_stalkHom 𝔐.ξ (RingHom.id Ω) ⟨centre z₁, 𝔐.all _⟩ W σ₁ a₁
    have e₂ := spec_stalkHom 𝔐₀.ξ i ⟨centre z₂, 𝔐₀.all _⟩ W σ₂ a₂
    have hid : spMap (RingHom.id Ω) = 𝟙 _ := by simp [spMap]
    rw [hid, Category.id_comp] at e₁
    have f₁ := congrArg (· ≫ 𝔐.f) e₁
    have f₂ := congrArg (· ≫ 𝔐₀.f) e₂
    simp only [Category.assoc] at f₁ f₂
    exact f₁.trans (hξ.trans f₂.symm)

end GlobalTheory.CompanionTheory.Ar.OrArch
