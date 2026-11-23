import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidCoords
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShimuraObjectPullbackCompCancel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EssFiniteTypePreimageFromSpecStalk

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UCanon.BaseSch

theorem spMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  simp [spMap, CommRingCat.ofHom_comp, Spec.map_comp]

theorem spMap_injective {A B : Type} [CommRing A] [CommRing B] {f g : A →+* B} (h : spMap f = spMap g) :
    f = g := by
  have := congrArg CommRingCat.Hom.hom (Spec.map_injective h)
  simpa using this

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem lowMap_eq {l : Geo.Tor.Level H} (c : Coeff l) {A : Type} [CommRing A] (b : c.F →+* A) :
    lowMap c b = spMap b ≫ lowMap c (RingHom.id c.F) := by
  simp only [lowMap, RingHom.id_comp]
  rw [← spMap_comp']

theorem objMap_congr {D : Datum H} {l : Geo.Tor.Level H} {S S' : Scheme.{0}} {s : S ⟶ Sp (KA l)}
    {s' : S' ⟶ Sp (KA l)} {o : Obj D l (baseKA l) s} {o' : Obj D l (baseKA l) s'} {f f' : S' ⟶ S} (h : f = f')
    (m : ObjMap o' o f) : ∃ m' : ObjMap o' o f', m'.toSABMap.φ = m.toSABMap.φ := by
  subst h
  exact ⟨m, rfl⟩

theorem exists_section_pull {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {q : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G q φ) (σ : 𝟙_ (Over S) ⟶ G) :
    ∃ σ' : 𝟙_ (Over S') ⟶ G', σ'.left ≫ φ = q ≫ σ.left := by
  have hw : (q ≫ σ.left) ≫ G.hom = 𝟙 S' ≫ q := by
    rw [Category.assoc, Over.w σ]
    simp
  refine ⟨Over.homMk (h.1.lift (q ≫ σ.left) (𝟙 S') hw) (by simpa using h.1.lift_snd _ _ hw), ?_⟩
  simp

theorem hom_ext_pull {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {q : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G q φ) {T : Over S'} (σ₁ σ₂ : T ⟶ G')
    (e : σ₁.left ≫ φ = σ₂.left ≫ φ) : σ₁ = σ₂ := by
  ext1
  exact h.1.hom_ext e (by rw [Over.w σ₁, Over.w σ₂])

theorem pull_mul {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {q : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G q φ) (σ₁ σ₂ : 𝟙_ (Over S') ⟶ G') (τ₁ τ₂ : 𝟙_ (Over S) ⟶ G)
    (h₁ : σ₁.left ≫ φ = q ≫ τ₁.left) (h₂ : σ₂.left ≫ φ = q ≫ τ₂.left) :
    (σ₁ * σ₂).left ≫ φ = q ≫ (τ₁ * τ₂).left := by
  let Q : Over.mk ((𝟙_ (Over S')).hom ≫ q) ⟶ 𝟙_ (Over S) := Over.homMk q (by simp)
  have e := h.2 (𝟙_ (Over S')) σ₁ σ₂ (Q ≫ τ₁) (Q ≫ τ₂) (by simp [Q, h₁]) (by simp [Q, h₂])
  rw [← e, ← MonObj.comp_mul]
  simp [Q]

theorem sec_comp_eq {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} (f : S' ⟶ S) (φ : G'.left ⟶ G.left)
    (hw : φ ≫ G.hom = G'.hom ≫ f) (σ : 𝟙_ (Over S') ⟶ G') (τ : 𝟙_ (Over S) ⟶ G) :
    (σ.left ≫ φ) ≫ G.hom = (f ≫ τ.left) ≫ G.hom := by
  rw [Category.assoc, hw, Category.assoc, Over.w τ, ← Category.assoc, Over.w σ]
  simp

end GlobalTheory.UCanon.BaseSch

namespace GlobalTheory.UCanon.BaseSch

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

set_option maxHeartbeats 800000 in

theorem of_homScheme (D' : Datum H) {l : Geo.Tor.Level H} (c : Coeff l) (X : Type) [AddCommGroup X] [Module (𝓞 E) X]
    (Cs : Scheme.{0}) (g : Cs ⟶ Sp c.F)
    (oC : Obj D' (LowDat.lowLevel l) (baseKA (LowDat.lowLevel l)) (g ≫ lowMap c (RingHom.id c.F)))
    (u : X → (𝟙_ (Over Cs) ⟶ oC.t.G)) (N : ℕ) (hsm : SmoothOfRelativeDimension N g)
    (hex : ∀ (V : Type) [CommRing V] [IsReduced V] (bV : c.F →+* V) (o' : LowObj D' c bV)
      (x : X → (𝟙_ (Over (Sp V)) ⟶ o'.t.G)), (∀ y z, x (y + z) = x y * x z) →
      (∀ (a : 𝓞 E) y, x (a • y) = x y ≫ o'.t.act.act a) → ∃ (v : Sp V ⟶ Cs) (m : ObjMap o' oC v),
        v ≫ g = spMap bV ∧ ∀ y, (x y).left ≫ m.toSABMap.φ = v ≫ (u y).left)
    (huniq : ∀ (A : Type) [CommRing A] [IsReduced A] (v₁ v₂ : Sp A ⟶ Cs), v₁ ≫ g = v₂ ≫ g →
      ∀ (s' : Sp A ⟶ Sp (KA (LowDat.lowLevel l))) (o'' : Obj D' (LowDat.lowLevel l) (baseKA (LowDat.lowLevel l)) s')
        (m₁ : ObjMap o'' oC v₁) (m₂ : ObjMap o'' oC v₂) (z : X → (Sp A ⟶ o''.t.G.left)),
        s' = v₁ ≫ g ≫ lowMap c (RingHom.id c.F) → (∀ y, z y ≫ m₁.toSABMap.φ = v₁ ≫ (u y).left) →
        (∀ y, z y ≫ m₂.toSABMap.φ = v₂ ≫ (u y).left) → v₁ = v₂)
    (heps : ∀ (k : Type) [Field k] (v : Sp (DualNumber k) ⟶ Cs) (s' : Sp (DualNumber k) ⟶ Sp (KA (LowDat.lowLevel l)))
      (o'' : Obj D' (LowDat.lowLevel l) (baseKA (LowDat.lowLevel l)) s') (m₁ : ObjMap o'' oC v)
      (m₂ : ObjMap o'' oC (constPt v)) (z : X → (Sp (DualNumber k) ⟶ o''.t.G.left)),
      s' = v ≫ g ≫ lowMap c (RingHom.id c.F) → (∀ y, z y ≫ m₁.toSABMap.φ = v ≫ (u y).left) →
      (∀ y, z y ≫ m₂.toSABMap.φ = constPt v ≫ (u y).left) → v = constPt v)
    (hadd : ∀ y z, u (y + z) = u y * u z) (hlin : ∀ (a : 𝓞 E) y, u (a • y) = u y ≫ oC.t.act.act a)
    (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (bV : c.F →+* V) (o' : LowObj D' c bV)
    (x : X → (𝟙_ (Over (Sp V)) ⟶ o'.t.G)) (hx : ∀ y z, x (y + z) = x y * x z)
    (hxl : ∀ (a : 𝓞 E) y, x (a • y) = x y ≫ o'.t.act.act a) :
    ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsRegularLocalRing W) (b : c.F →+* W) (o : LowObj D' c b)
      (x₀ : X → (𝟙_ (Over (Sp W)) ⟶ o.t.G)) (θ₀ : W →+* V) (m : ObjMap o' o (spMap θ₀)),
      b.EssFiniteType ∧ (∀ y z, x₀ (y + z) = x₀ y * x₀ z) ∧ (∀ (a : 𝓞 E) y, x₀ (a • y) = x₀ y ≫ o.t.act.act a) ∧
      IsLocalHom θ₀ ∧ θ₀.comp b = bV ∧ (∀ y, (x y).left ≫ m.toSABMap.φ = spMap θ₀ ≫ (x₀ y).left) ∧
      ((∀ (A : Type) [CommRing A] [IsReduced A] (f₁ f₂ : W →+* A), f₁.comp b = f₂.comp b →
        ∀ (o'' : LowObj D' c (f₁.comp b)) (m₁ : ObjMap o'' o (spMap f₁)) (m₂ : ObjMap o'' o (spMap f₂))
          (z : X → (Sp A ⟶ o''.t.G.left)), (∀ y, z y ≫ m₁.toSABMap.φ = spMap f₁ ≫ (x₀ y).left) →
          (∀ y, z y ≫ m₂.toSABMap.φ = spMap f₂ ≫ (x₀ y).left) → (∀ y, z y ≫ o''.t.G.hom = 𝟙 _) → f₁ = f₂) ∧
        (∀ (k : Type) [Field k] (f : W →+* DualNumber k) (o'' : LowObj D' c (f.comp b)) (m₁ : ObjMap o'' o (spMap f))
          (m₂ : ObjMap o'' o (spMap (GlobalTheory.RigChart.constHom f))) (z : X → (Sp (DualNumber k) ⟶ o''.t.G.left)),
          (∀ y, z y ≫ m₁.toSABMap.φ = spMap f ≫ (x₀ y).left) →
          (∀ y, z y ≫ m₂.toSABMap.φ = spMap (GlobalTheory.RigChart.constHom f) ≫ (x₀ y).left) →
          (∀ y, z y ≫ o''.t.G.hom = 𝟙 _) → f = GlobalTheory.RigChart.constHom f)) ∧
      (letI := ((residue W).comp b).toAlgebra
        ∃ a t : ℕ, ringKrullDim W = a ∧ Algebra.trdeg c.F (ResidueField W) = t ∧ a + t = N) := by
  obtain ⟨v, m0, hvg, hvx⟩ := hex V bV o' x hx hxl
  obtain ⟨hreg, b, hqb, hft, hdim⟩ :=
    GlobalTheory.SmoothStalk.stalk_regular_essFiniteType_dim c.F Cs g N hsm (v (closedPoint V))
  haveI : IsDomain (Cs.presheaf.stalk (v (closedPoint V))) := ReciprocityTheory.AnForm.R.isDomain_of_isRegularLocalRing
  obtain ⟨q, hq⟩ : ∃ q, q = Cs.fromSpecStalk (v (closedPoint V)) := ⟨_, rfl⟩
  rw [← hq] at hqb
  have hs : lowMap c b = q ≫ g ≫ lowMap c (RingHom.id c.F) := by
    rw [lowMap_eq c b, ← hqb, Category.assoc]
  obtain ⟨o, ⟨mq⟩⟩ := (obj_pull_comp_cancel (D := D') (l := LowDat.lowLevel l)).1
    (g ≫ lowMap c (RingHom.id c.F)) oC q (lowMap c b) hs
  have hsec := fun y => exists_section_pull mq.toSABMap.cart (u y)
  choose x₀ hx₀ using hsec
  set θ₀ : Cs.presheaf.stalk (v (closedPoint V)) →+* V := (Scheme.stalkClosedPointTo v).hom with hθ₀
  have hθq : spMap θ₀ ≫ q = v := by
    rw [hq]
    simpa [hθ₀, spMap] using Scheme.Spec_stalkClosedPointTo_fromSpecStalk v
  have hθb : θ₀.comp b = bV := by
    apply spMap_injective
    rw [spMap_comp', ← hqb, ← Category.assoc, hθq, hvg]
  obtain ⟨m0', hm0'⟩ := objMap_congr hθq.symm m0
  obtain ⟨n, hn⟩ := ((obj_pull_comp_cancel (D := D') (l := LowDat.lowLevel l)).2 _ _ _ oC o o' q (spMap θ₀) mq).2 m0'
  have hmono : ∀ {T : Scheme.{0}} (a₁ a₂ : T ⟶ Sp (Cs.presheaf.stalk (v (closedPoint V)))), a₁ ≫ q = a₂ ≫ q → a₁ = a₂ :=
    fun a₁ a₂ h => by rw [hq] at h; exact (cancel_mono _).1 h
  refine ⟨Cs.presheaf.stalk (v (closedPoint V)), inferInstance, inferInstance, hreg, b, o, x₀, θ₀, n, hft, ?_, ?_, ?_, hθb, ?_, ⟨?_, ?_⟩, hdim⟩
  · intro y z
    apply hom_ext_pull mq.toSABMap.cart
    rw [hx₀, hadd, pull_mul mq.toSABMap.cart _ _ _ _ (hx₀ y) (hx₀ z)]
  · intro a y
    apply hom_ext_pull mq.toSABMap.cart
    rw [hx₀, hlin, Over.comp_left, Over.comp_left, Category.assoc, mq.toSABMap.act a, reassoc_of% (hx₀ y)]
  · exact inferInstance
  · intro y
    refine mq.toSABMap.cart.1.hom_ext ?_ ?_
    · rw [Category.assoc, ← hn, hm0', hvx, Category.assoc, hx₀, ← Category.assoc, hθq]
    · exact sec_comp_eq _ _ n.toSABMap.cart.1.w (x y) (x₀ y)
  · intro A _ _ f₁ f₂ hf o'' m₁ m₂ z hz₁ hz₂ _
    obtain ⟨k₁, hk₁⟩ := ((obj_pull_comp_cancel (D := D') (l := LowDat.lowLevel l)).2 _ _ _ oC o o'' q (spMap f₁) mq).1 m₁
    obtain ⟨k₂, hk₂⟩ := ((obj_pull_comp_cancel (D := D') (l := LowDat.lowLevel l)).2 _ _ _ oC o o'' q (spMap f₂) mq).1 m₂
    have hg : ∀ f : Cs.presheaf.stalk (v (closedPoint V)) →+* A, (spMap f ≫ q) ≫ g = spMap (f.comp b) := fun f => by
      rw [Category.assoc, hqb, spMap_comp']
    have e := huniq A (spMap f₁ ≫ q) (spMap f₂ ≫ q) (by rw [hg, hg, hf]) _ o'' k₁ k₂ z
      (by rw [lowMap_eq c (f₁.comp b), ← hg, Category.assoc])
      (fun y => by rw [hk₁, ← Category.assoc, hz₁, Category.assoc, hx₀, Category.assoc])
      (fun y => by rw [hk₂, ← Category.assoc, hz₂, Category.assoc, hx₀, Category.assoc])
    exact spMap_injective (hmono _ _ e)
  · intro k _ f o'' m₁ m₂ z hz₁ hz₂ _
    obtain ⟨k₁, hk₁⟩ := ((obj_pull_comp_cancel (D := D') (l := LowDat.lowLevel l)).2 _ _ _ oC o o'' q (spMap f) mq).1 m₁
    obtain ⟨k₂, hk₂⟩ := ((obj_pull_comp_cancel (D := D') (l := LowDat.lowLevel l)).2 _ _ _ oC o o'' q
      (spMap (GlobalTheory.RigChart.constHom f)) mq).1 m₂
    have hc : spMap (GlobalTheory.RigChart.constHom f) ≫ q = constPt (spMap f ≫ q) := by
      simp only [constPt, GlobalTheory.RigChart.constHom, spMap_comp', Category.assoc]
    obtain ⟨k₂', hk₂'⟩ := objMap_congr hc k₂
    have e := heps k (spMap f ≫ q) _ o'' k₁ k₂' z
      (by rw [lowMap_eq c (f.comp b), spMap_comp', ← hqb]; simp only [Category.assoc])
      (fun y => by rw [hk₁, ← Category.assoc, hz₁, Category.assoc, hx₀, Category.assoc])
      (fun y => by rw [hk₂', hk₂, ← Category.assoc, hz₂, Category.assoc, hx₀, ← Category.assoc, hc])
    rw [← hc] at e
    exact spMap_injective (hmono _ _ e)

end GlobalTheory.UCanon.BaseSch

namespace GlobalTheory.UCanon.BaseSch

theorem exists_baseSch_of_homScheme (hcs : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D' : Datum H) {l : Geo.Tor.Level H} (c : Coeff l) (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Free ℤ X] [Module.Finite ℤ X], ∃ (Cs : Scheme.{0}) (g : Cs ⟶ Sp c.F) (oC : Obj D' (LowDat.lowLevel l) (baseKA (LowDat.lowLevel l)) (g ≫ lowMap c (RingHom.id c.F))) (u : X → (𝟙_ (Over Cs) ⟶ oC.t.G)), SmoothOfRelativeDimension (D'.dim + Module.finrank (𝓞 E) X * (Module.finrank ℚ E / 2 * (D'.p + D'.q))) g ∧ (∀ y z, u (y + z) = u y * u z) ∧ (∀ (a : 𝓞 E) y, u (a • y) = u y ≫ oC.t.act.act a) ∧ (∀ (V : Type) [CommRing V] [IsReduced V] (bV : c.F →+* V) (o' : LowObj D' c bV) (x : X → (𝟙_ (Over (Sp V)) ⟶ o'.t.G)), (∀ y z, x (y + z) = x y * x z) → (∀ (a : 𝓞 E) y, x (a • y) = x y ≫ o'.t.act.act a) → ∃ (v : Sp V ⟶ Cs) (m : ObjMap o' oC v), v ≫ g = spMap bV ∧ ∀ y, (x y).left ≫ m.toSABMap.φ = v ≫ (u y).left) ∧ (∀ (A : Type) [CommRing A] [IsReduced A] (v₁ v₂ : Sp A ⟶ Cs), v₁ ≫ g = v₂ ≫ g → ∀ (s' : Sp A ⟶ Sp (KA (LowDat.lowLevel l))) (o'' : Obj D' (LowDat.lowLevel l) (baseKA (LowDat.lowLevel l)) s') (m₁ : ObjMap o'' oC v₁) (m₂ : ObjMap o'' oC v₂) (z : X → (Sp A ⟶ o''.t.G.left)), s' = v₁ ≫ g ≫ lowMap c (RingHom.id c.F) → (∀ y, z y ≫ m₁.toSABMap.φ = v₁ ≫ (u y).left) → (∀ y, z y ≫ m₂.toSABMap.φ = v₂ ≫ (u y).left) → v₁ = v₂) ∧ (∀ (k : Type) [Field k] (v : Sp (DualNumber k) ⟶ Cs) (s' : Sp (DualNumber k) ⟶ Sp (KA (LowDat.lowLevel l))) (o'' : Obj D' (LowDat.lowLevel l) (baseKA (LowDat.lowLevel l)) s') (m₁ : ObjMap o'' oC v) (m₂ : ObjMap o'' oC (constPt v)) (z : X → (Sp (DualNumber k) ⟶ o''.t.G.left)), s' = v ≫ g ≫ lowMap c (RingHom.id c.F) → (∀ y, z y ≫ m₁.toSABMap.φ = v ≫ (u y).left) → (∀ y, z y ≫ m₂.toSABMap.φ = constPt v ≫ (u y).left) → v = constPt v)) : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D' : Datum H) {l : Geo.Tor.Level H} (c : Coeff l) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (bV : c.F →+* V) (o' : LowObj D' c bV) (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Free ℤ X] [Module.Finite ℤ X] (x : X → (𝟙_ (Over (Sp V)) ⟶ o'.t.G)), (∀ y z, x (y + z) = x y * x z) → (∀ (a : 𝓞 E) y, x (a • y) = x y ≫ o'.t.act.act a) → ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsRegularLocalRing W) (b : c.F →+* W) (o : LowObj D' c b) (x₀ : X → (𝟙_ (Over (Sp W)) ⟶ o.t.G)) (θ₀ : W →+* V) (m : ObjMap o' o (spMap θ₀)), b.EssFiniteType ∧ (∀ y z, x₀ (y + z) = x₀ y * x₀ z) ∧ (∀ (a : 𝓞 E) y, x₀ (a • y) = x₀ y ≫ o.t.act.act a) ∧ IsLocalHom θ₀ ∧ θ₀.comp b = bV ∧ (∀ y, (x y).left ≫ m.toSABMap.φ = spMap θ₀ ≫ (x₀ y).left) ∧ ((∀ (A : Type) [CommRing A] [IsReduced A] (f₁ f₂ : W →+* A), f₁.comp b = f₂.comp b → ∀ (o'' : LowObj D' c (f₁.comp b)) (m₁ : ObjMap o'' o (spMap f₁)) (m₂ : ObjMap o'' o (spMap f₂)) (z : X → (Sp A ⟶ o''.t.G.left)), (∀ y, z y ≫ m₁.toSABMap.φ = spMap f₁ ≫ (x₀ y).left) → (∀ y, z y ≫ m₂.toSABMap.φ = spMap f₂ ≫ (x₀ y).left) → (∀ y, z y ≫ o''.t.G.hom = 𝟙 _) → f₁ = f₂) ∧ (∀ (k : Type) [Field k] (f : W →+* DualNumber k) (o'' : LowObj D' c (f.comp b)) (m₁ : ObjMap o'' o (spMap f)) (m₂ : ObjMap o'' o (spMap (GlobalTheory.RigChart.constHom f))) (z : X → (Sp (DualNumber k) ⟶ o''.t.G.left)), (∀ y, z y ≫ m₁.toSABMap.φ = spMap f ≫ (x₀ y).left) → (∀ y, z y ≫ m₂.toSABMap.φ = spMap (GlobalTheory.RigChart.constHom f) ≫ (x₀ y).left) → (∀ y, z y ≫ o''.t.G.hom = 𝟙 _) → f = GlobalTheory.RigChart.constHom f)) ∧ (letI := ((residue W).comp b).toAlgebra; ∃ a t : ℕ, ringKrullDim W = a ∧ Algebra.trdeg c.F (ResidueField W) = t ∧ a + t = D'.dim + Module.finrank (𝓞 E) X * (Module.finrank ℚ E / 2 * (D'.p + D'.q))) := by
  intro E _ _ _ H D' l c V _ _ _ bV o' X _ _ _ _ x hx hxl
  obtain ⟨Cs, g, oC, u, hsm, hadd, hlin, hex, huniq, heps⟩ := hcs D' c X
  exact of_homScheme D' c X Cs g oC u _ hsm hex huniq heps hadd hlin V bV o' x hx hxl

end GlobalTheory.UCanon.BaseSch
