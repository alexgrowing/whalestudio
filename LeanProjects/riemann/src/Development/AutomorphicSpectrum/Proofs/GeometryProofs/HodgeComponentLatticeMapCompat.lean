import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHodgeLine
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsExcisionNbhdAway
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelPullbackCorrespondence
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieLatticeDominantCompat

noncomputable section

open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.SingVal

open LiePull LieTangent

section Abstract

open MonObj

variable {S : Scheme.{0}} {G : Over S} [GrpObj G] {Ω : Type} [Field Ω] {L V : Type} [AddCommGroup L] [Module Ω L]
  [AddCommGroup V] [Module ℂ V] {ξ : Sp Ω ⟶ S} {z : Sp ℂ ⟶ S}

def extSub (W : Subring Ω) {x : Sp W ⟶ S} (hx : spMap W.subtype ≫ x = ξ) (N : LieModel G ξ L) : Submodule W L where
  carrier := {e | ∃ v, Ext W.subtype x N e v}
  add_mem' := fun ⟨_, hv⟩ ⟨_, hv'⟩ => ⟨_, hv.mul hx hv'⟩
  zero_mem' := ⟨_, Ext.zero hx⟩
  smul_mem' c _ := fun ⟨_, hv⟩ => ⟨_, hv.smul c⟩

theorem exists_val (W : Subring Ω) (φ : W →+* ℂ) {x : Sp W ⟶ S} (hz : spMap φ ≫ x = z) (N : LieModel G ξ L)
    (Nz : LieModel G z V) :
    ∃ val : L → V, ∀ e v, Ext W.subtype x N e v → Nz.pt (val e) = epsBase φ hz ≫ v := by
  classical
  have key : ∀ e, ∃ w, ∀ v, Ext W.subtype x N e v → Nz.pt w = epsBase φ hz ≫ v := by
    intro e
    by_cases h : ∃ v, Ext W.subtype x N e v
    · obtain ⟨v, hv⟩ := h
      obtain ⟨w, hw⟩ := Nz.onto _ (isTanAt_base φ hz hv.1)
      exact ⟨w, fun v' hv' => by rw [hw, hv.unique Subtype.val_injective hv']⟩
    · exact ⟨0, fun v hv => (h ⟨v, hv⟩).elim⟩
  choose val hval using key
  exact ⟨val, hval⟩

theorem exists_lat_val (W : Subring Ω) (φ : W →+* ℂ) {x : Sp W ⟶ S} (hx : spMap W.subtype ≫ x = ξ)
    (hz : spMap φ ≫ x = z) (N : LieModel G ξ L) (Nz : LieModel G z V) :
    ∃ (Lm : Submodule W L) (val : L → V), val 0 = 0 ∧ (∀ e ∈ Lm, ∀ e' ∈ Lm, val (e + e') = val e + val e') ∧
      (∀ a : W, ∀ e ∈ Lm, val ((a : Ω) • e) = φ a • val e) ∧
      ∀ e v, Ext W.subtype x N e v → e ∈ Lm ∧ Nz.pt (val e) = epsBase φ hz ≫ v := by
  obtain ⟨val, hval⟩ := exists_val W φ hz N Nz
  refine ⟨extSub W hx N, val, ?_, ?_, ?_, fun e v h => ⟨⟨v, h⟩, hval e v h⟩⟩
  · apply Nz.inj
    rw [hval 0 1 (Ext.zero hx), LieModel.pt_zero, comp_one]
  · rintro e ⟨v, hv⟩ e' ⟨v', hv'⟩
    apply Nz.inj
    rw [hval _ _ (hv.mul hx hv'), Nz.add, hval _ _ hv, hval _ _ hv', comp_mul]
  · rintro a e ⟨v, hv⟩
    apply Nz.inj
    have h1 := hval _ _ (hv.smul a)
    refine h1.trans ?_
    rw [LieModel.pt_smul, hval _ _ hv]
    have e1 : epsBase φ hz ≫ epsScale x a = epsScale z (φ a) ≫ epsBase φ hz := base_scale φ hz a
    have e2 : LieEx.hom x (a • (LinearMap.id : W →ₗ[W] W)) = epsScale x a := rfl
    rw [e2, ← Category.assoc, e1, Category.assoc]

theorem spMap_dual_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (a : A →+* B) (b : B →+* C)
    {T : Scheme.{0}} (t : Sp (DualNumber A) ⟶ T) :
    spMap (dualMap (b.comp a)) ≫ t = spMap (dualMap b) ≫ spMap (dualMap a) ≫ t := by
  rw [← dualMap_comp]
  exact (congrArg (· ≫ t) (spec_comp (dualMap a) (dualMap b)).symm).trans (Category.assoc _ _ _)

theorem assoc_three {P Q R T U : Scheme.{0}} (a : P ⟶ Q) (b : Q ⟶ R) (c : R ⟶ T) (d : T ⟶ U) :
    (a ≫ b ≫ c) ≫ d = a ≫ b ≫ c ≫ d := by
  simp only [Category.assoc]

theorem ext_of_tan {X' : Scheme.{0}} {G' : Over X'} [GrpObj G'] {f : X' ⟶ S} {ψ : G'.left ⟶ G.left}
    (hG : IsGrpPullback G' G f ψ) {A B : Type} [CommRing A] [CommRing B] {g : A →+* Ω} {y : Sp B ⟶ X'} (σ : B →+* A)
    {h : B →+* Ω} {x : Sp A ⟶ S} (hxy : x = (spMap σ ≫ y) ≫ f) (hσ : g.comp σ = h) {N : LieModel G ξ L} {e : L}
    {v : epsAt y ⟶ G'} (hv : IsTanAt G' y v)
    (he : (N.pt e).left = spMap (dualMap h) ≫ v.left ≫ ψ) :
    ∃ u : epsAt x ⟶ G, Ext g x N e u ∧ u.left = spMap (dualMap σ) ≫ v.left ≫ ψ := by
  subst hxy
  subst hσ
  refine ⟨LieMove.pushEps hG (epsBase σ rfl ≫ v), ⟨(LieMove.tan_iff hG _).1 (isTanAt_base σ rfl hv), ?_⟩,
    Category.assoc _ _ _⟩
  refine he.trans ?_
  have e1 : spMap (dualMap (g.comp σ)) = spMap (dualMap g) ≫ spMap (dualMap σ) := by
    rw [← dualMap_comp]
    exact (spec_comp _ _).symm
  rw [e1, Category.assoc]
  rfl

end Abstract

theorem value_map : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S S₀ : Finset ℕ) (Ω Ω₀ : Type) [Field Ω] [Field Ω₀] (K K₀ : Type) [Fintype K] [Fintype K₀] (J : K → Type) (J₀ : K₀ → Type) (y : (Σ k, J k) → Ω) (y₀ : (Σ k, J₀ k) → Ω₀) (𝔐 : HodgeCpt Y S y) (𝔐₀ : HodgeCpt Y S₀ y₀) (i : Ω₀ →+* Ω) (ι : 𝔐₀.Li →+ 𝔐.Li) (W : Subring Ω) (φ : W →+* ℂ) (z₁ : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X) (z₂ : Spec (CommRingCat.of ℂ) ⟶ 𝔐₀.X) (σ₁ : 𝔐.X.presheaf.stalk (centre z₁) →+* W) (σ₂ : 𝔐₀.X.presheaf.stalk (centre z₂) →+* W), 𝔐.ξ ≫ 𝔐.f = spMap i ≫ 𝔐₀.ξ ≫ 𝔐₀.f → (∀ (e : 𝔐₀.Li) (e' : 𝔐.Li), (𝔐.M.pt e').left ≫ 𝔐.m.φ = spMap (dualMap i) ≫ (𝔐₀.M.pt e).left ≫ 𝔐₀.m.φ ↔ e' = ι e) → (∀ s, (σ₁ s : Ω) = genMap 𝔐.ξ ⟨centre z₁, 𝔐.all _⟩ s) → (∀ s, (σ₂ s : Ω) = i (genMap 𝔐₀.ξ ⟨centre z₂, 𝔐₀.all _⟩ s)) → (∀ s, φ (σ₁ s) = (Scheme.stalkClosedPointTo z₁).hom s) → (∀ s, φ (σ₂ s) = (Scheme.stalkClosedPointTo z₂).hom s) → spMap σ₁ ≫ 𝔐.X.fromSpecStalk (centre z₁) ≫ 𝔐.f = spMap σ₂ ≫ 𝔐₀.X.fromSpecStalk (centre z₂) ≫ 𝔐₀.f → ∀ (Vz : Type) [AddCommGroup Vz] [Module ℂ Vz] (MR : LieModel 𝔐.t.G z₁ Vz), ∃ (Lm : Submodule W 𝔐.Li) (val : 𝔐.Li → Vz), val 0 = 0 ∧ (∀ e ∈ Lm, ∀ e' ∈ Lm, val (e + e') = val e + val e') ∧ (∀ a : W, ∀ e ∈ Lm, val ((a : Ω) • e) = φ a • val e) ∧ (∀ (e : 𝔐.Li) (v : epsAt z₁ ⟶ 𝔐.t.G), 𝔐.M.ValAt z₁ e v → e ∈ Lm ∧ v = MR.pt (val e)) ∧ ∀ (e₀ : 𝔐₀.Li) (v₀ : epsAt z₂ ⟶ 𝔐₀.t.G), 𝔐₀.M.ValAt z₂ e₀ v₀ → ι e₀ ∈ Lm ∧ (MR.pt (val (ι e₀))).left ≫ 𝔐.m.φ = v₀.left ≫ 𝔐₀.m.φ := by
  intro E _ _ _ H D l Xo c Y S S₀ Ω Ω₀ _ _ K K₀ _ _ J J₀ y y₀ 𝔐 𝔐₀ i ι W φ z₁ z₂ σ₁ σ₂ hgen hι hσ₁ hσ₂ hφ₁ hφ₂ hxx
    Vz _ _ MR
  have hG := 𝔐.m.cart
  have hG₀ := 𝔐₀.m.cart
  have s₁ : W.subtype.comp σ₁ = genMap 𝔐.ξ ⟨centre z₁, 𝔐.all _⟩ := RingHom.ext hσ₁
  have s₂ : W.subtype.comp σ₂ = i.comp (genMap 𝔐₀.ξ ⟨centre z₂, 𝔐₀.all _⟩) := RingHom.ext hσ₂
  have t₁ : φ.comp σ₁ = (Scheme.stalkClosedPointTo z₁).hom := RingHom.ext hφ₁
  have t₂ : φ.comp σ₂ = (Scheme.stalkClosedPointTo z₂).hom := RingHom.ext hφ₂
  obtain ⟨x, hx₁⟩ : ∃ x : Sp W ⟶ Y.X, x = (spMap σ₁ ≫ 𝔐.X.fromSpecStalk (centre z₁)) ≫ 𝔐.f := ⟨_, rfl⟩
  have hx₂ : x = (spMap σ₂ ≫ 𝔐₀.X.fromSpecStalk (centre z₂)) ≫ 𝔐₀.f := by
    rw [hx₁, Category.assoc, Category.assoc, hxx]
  have hx : spMap W.subtype ≫ x = 𝔐.ξ ≫ 𝔐.f := by
    rw [hx₁, ← Category.assoc, ← Category.assoc, spec_comp, s₁]
    exact congrArg (· ≫ 𝔐.f) (spec_genMap 𝔐.ξ ⟨centre z₁, 𝔐.all _⟩)
  have hz : spMap φ ≫ x = z₁ ≫ 𝔐.f := by
    rw [hx₁, ← Category.assoc, ← Category.assoc, spec_comp, t₁]
    exact congrArg (· ≫ 𝔐.f) (spec_centre z₁)
  obtain ⟨Lm, val, h0, hadd, hsm, hext⟩ := exists_lat_val W φ hx hz (LieMove.pushModel hG 𝔐.M)
    (LieMove.pushModel hG MR)
  refine ⟨Lm, val, h0, hadd, hsm, ?_, ?_⟩
  · intro e v hv
    obtain ⟨h, v', hv', hl⟩ := hv
    obtain ⟨u, hu, hul⟩ := ext_of_tan (N := LieMove.pushModel hG 𝔐.M) (e := e) hG σ₁ hx₁ s₁ hv'.1
      (by
        show (𝔐.M.pt e).left ≫ _ = _
        rw [hv'.2]
        exact Category.assoc _ _ _)
    obtain ⟨hm, hpt⟩ := hext e u hu
    refine ⟨hm, LieMove.pushEps_inj hG (Eq.trans ?_ hpt.symm)⟩
    have e3 : v.left = spMap (dualMap φ) ≫ spMap (dualMap σ₁) ≫ v'.left := by
      rw [hl, ← t₁]
      exact spMap_dual_comp _ _ _
    apply Over.OverMorphism.ext
    show v.left ≫ _ = spMap (dualMap φ) ≫ u.left
    rw [hul, e3]
    exact assoc_three _ _ _ _
  · intro e₀ v₀ hv
    obtain ⟨h, v', hv', hl⟩ := hv
    have hι' := (hι e₀ (ι e₀)).2 rfl
    obtain ⟨u, hu, hul⟩ := ext_of_tan (N := LieMove.pushModel hG 𝔐.M) (e := ι e₀) hG₀ σ₂ hx₂ s₂ hv'.1
      (by
        show (𝔐.M.pt (ι e₀)).left ≫ _ = _
        rw [hι', hv'.2, spMap_dual_comp]
        exact congrArg (_ ≫ ·) (Category.assoc _ _ _))
    obtain ⟨hm, hpt⟩ := hext _ u hu
    refine ⟨hm, ?_⟩
    have e3 : v₀.left = spMap (dualMap φ) ≫ spMap (dualMap σ₂) ≫ v'.left := by
      rw [hl, ← t₂]
      exact spMap_dual_comp _ _ _
    refine (congrArg (fun q => q.left) hpt).trans ?_
    show spMap (dualMap φ) ≫ u.left = _
    rw [hul, e3]
    exact (assoc_three _ _ _ _).symm

end GlobalTheory.CompanionTheory.Ar.SingVal
