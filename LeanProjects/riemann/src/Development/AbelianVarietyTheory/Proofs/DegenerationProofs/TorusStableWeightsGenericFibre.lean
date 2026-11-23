import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.IsNormalSchemeSp
import Development.AbelianVarietyTheory.Definitions.Degenerations.IsAffineSplitTorusLeft
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfTorusBased
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsScalMulEqZero
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PullPullAndSplitPull
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorusCutByInvariantRatiosField
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ GlobalTheory.ZJ.SplitPull

noncomputable section
namespace GlobalTheory.ZJ.GenericWt

theorem open_rep {R : Type} [CommRing R] [IsNoetherianRing R] (X : Over (Sp R)) [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] (V : X.left.Opens) :
    ∃ (Z : Over (Sp R)) (z : Z ⟶ X), LocallyOfFiniteType Z.hom ∧ QuasiCompact Z.hom ∧ ⊤ ≤ z.left ⁻¹ᵁ V ∧
      ∀ (Y : Over (Sp R)) (y : Y ⟶ X), ⊤ ≤ y.left ⁻¹ᵁ V → ∃ φ : Y ⟶ Z, φ ≫ z = y := by
  have : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  refine ⟨Over.mk (V.ι ≫ X.hom), Over.homMk V.ι rfl, inferInstanceAs (LocallyOfFiniteType (V.ι ≫ X.hom)),
    inferInstanceAs (QuasiCompact (V.ι ≫ X.hom)), V.ι_preimage_self.ge, fun Y y h => ?_⟩
  have h' : Set.range y.left ⊆ Set.range V.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨x, rfl⟩
    exact h trivial
  refine ⟨Over.homMk (IsOpenImmersion.lift V.ι y.left h') ?_, Over.OverMorphism.ext (IsOpenImmersion.lift_fac _ _ h')⟩
  change _ ≫ V.ι ≫ X.hom = _
  rw [IsOpenImmersion.lift_fac_assoc, Over.w]

theorem zero_rep {S : Scheme.{0}} (X : Over S) [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] {J : Type}
    (p q : J → Γ(X.left, ⊤)) :
    ∃ (Z : Over S) (z : Z ⟶ X), LocallyOfFiniteType Z.hom ∧ QuasiCompact Z.hom ∧
      (∀ i, z.left.appTop.hom (p i) = z.left.appTop.hom (q i)) ∧
      ∀ (Y : Over S) (y : Y ⟶ X), (∀ i, y.left.appTop.hom (p i) = y.left.appTop.hom (q i)) →
        ∃ φ : Y ⟶ Z, φ ≫ z = y := by
  let A : Over S := Over.mk (𝔸(J; S) ↘ S)
  have : IsSeparated A.hom := inferInstanceAs (IsSeparated (𝔸(J; S) ↘ S))
  let f : X ⟶ A := Over.homMk (AffineSpace.homOfVector X.hom p) (AffineSpace.homOfVector_over _ _)
  let g : X ⟶ A := Over.homMk (AffineSpace.homOfVector X.hom q) (AffineSpace.homOfVector_over _ _)
  have key : ∀ (Y : Over S) (y : Y ⟶ X), y ≫ f = y ≫ g ↔
      ∀ i, y.left.appTop.hom (p i) = y.left.appTop.hom (q i) := by
    intro Y y
    have e : ∀ (v : J → Γ(X.left, ⊤)) i,
        (y.left ≫ AffineSpace.homOfVector X.hom v).appTop.hom (AffineSpace.coord S i) = y.left.appTop.hom (v i) := by
      intro v i
      rw [Scheme.Hom.comp_appTop]
      exact congrArg y.left.appTop.hom (AffineSpace.homOfVector_appTop_coord X.hom v i)
    constructor
    · intro h i
      have h' : y.left ≫ AffineSpace.homOfVector X.hom p = y.left ≫ AffineSpace.homOfVector X.hom q :=
        congrArg (fun k : Y ⟶ A => k.left) h
      rw [← e p, ← e q, h']
    · intro h
      have h' : y.left ≫ AffineSpace.homOfVector X.hom p = y.left ≫ AffineSpace.homOfVector X.hom q :=
        AffineSpace.hom_ext (by simp) fun i => (e p i).trans ((h i).trans (e q i).symm)
      exact Over.OverMorphism.ext h'
  have : IsClosedImmersion (equalizer.ι f g).left := inferInstance
  refine ⟨equalizer f g, equalizer.ι f g, ?_, ?_, (key _ _).1 (equalizer.condition f g), fun Y y h =>
    ⟨equalizer.lift y ((key _ _).2 h), equalizer.lift_ι _ _⟩⟩
  · rw [← Over.w (equalizer.ι f g)]; infer_instance
  · rw [← Over.w (equalizer.ι f g)]; infer_instance

section Spread
variable {R : Type} [CommRing R] [IsDomain R] [IsNoetherianRing R] (X : Over (Sp R))
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] {Sg : Set (Sp R)} (hD : Dense Sg)
include hD

theorem spread_open (V : X.left.Opens)
    (H : ∀ x ∈ Sg, ∃ (K : Type) (_ : Field K) (t : Sp K ⟶ Sp R), Set.range t = {x} ∧
      ∀ (T : Over (Sp K)) (φ : Over.mk (T.hom ≫ t) ⟶ X), ⊤ ≤ φ.left ⁻¹ᵁ V)
    (T : Over (Sp (FractionRing R))) (φ : Over.mk (T.hom ≫ Out.jK R) ⟶ X) : ⊤ ≤ φ.left ⁻¹ᵁ V := by
  obtain ⟨a, ha0, ha⟩ := (generic_of_dense_fibres R X Sg hD).2.2 V fun y hy => by
    obtain ⟨K, _, t, ht, h⟩ := H _ hy
    have : y ∈ Set.range (pullback.fst X.hom t) := by
      rw [Scheme.Pullback.range_fst, ht]
      rfl
    obtain ⟨y', rfl⟩ := this
    exact h (Over.mk (pullback.snd X.hom t)) (Over.homMk (pullback.fst X.hom t) pullback.condition)
      (Set.mem_univ y')
  intro y _
  refine ha _ fun h => ha0 ?_
  have e : X.hom (φ.left y) = Out.jK R (T.hom y) := by
    rw [← Scheme.Hom.comp_apply, Over.w φ]
    rfl
  rw [e] at h
  have h' : algebraMap R (FractionRing R) a ∈ (T.hom y).asIdeal := h
  have hb : (T.hom y).asIdeal = ⊥ := @Ideal.eq_bot_of_prime _ _ _ (T.hom y).isPrime
  rw [hb, Ideal.mem_bot] at h'
  exact (IsFractionRing.injective R (FractionRing R)) (h'.trans (map_zero _).symm)

theorem spread_eq (u v : Γ(X.left, ⊤))
    (H : ∀ x ∈ Sg, ∃ (K : Type) (_ : Field K) (t : Sp K ⟶ Sp R), Set.range t = {x} ∧
      ∀ (T : Over (Sp K)) (φ : Over.mk (T.hom ≫ t) ⟶ X), φ.left.appTop.hom u = φ.left.appTop.hom v)
    (T : Over (Sp (FractionRing R))) (φ : Over.mk (T.hom ≫ Out.jK R) ⟶ X) :
    φ.left.appTop.hom u = φ.left.appTop.hom v := by
  obtain ⟨a, ha0, ha⟩ := (generic_of_dense_fibres R X Sg hD).2.1 (u - v) fun x hx => by
    obtain ⟨K, _, t, ht, h⟩ := H _ hx
    refine ⟨K, inferInstance, t, ht, ?_⟩
    rw [map_sub, sub_eq_zero]
    exact h (Over.mk (pullback.snd X.hom t)) (Over.homMk (pullback.fst X.hom t) pullback.condition)
  have h := congrArg φ.left.appTop.hom ha
  rw [map_mul, map_zero, map_sub, GenericEq.appTop_scal, Over.w φ] at h
  have hu : IsUnit (Out.scal (T.hom ≫ Out.jK R) a) := by
    rw [← GenericEq.appTop_scal]
    refine IsUnit.map _ ?_
    have n := congrArg (fun k => k.hom a)
      (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap R (FractionRing R))))
    simp only [CommRingCat.hom_comp, RingHom.comp_apply] at n
    refine Eq.subst n (IsUnit.map _ ?_)
    exact IsUnit.mk0 _ ((map_ne_zero_iff _ (IsFractionRing.injective R (FractionRing R))).2 ha0)
  exact sub_eq_zero.1 (hu.mul_right_eq_zero.1 h)

end Spread

section Points
variable {S : Scheme.{0}} {H : Over S} [GrpObj H] (C : Charts H.left) (a a' : {i // C.wt i = C.c₀})

def Stab (Y : Over S) : Prop :=
  ∀ k g : Y ⟶ H, C.InK a k → ⊤ ≤ g.left ⁻¹ᵁ C.W a' → ⊤ ≤ (k * g).left ⁻¹ᵁ C.W a'

def Idn (u : Γ(H.left, C.W a)) (v : Γ(H.left, C.W a')) (Y : Over S) : Prop :=
  ∀ k g : Y ⟶ H, C.InK a k → ∀ (hk : ⊤ ≤ k.left ⁻¹ᵁ C.W a) (h₁ : ⊤ ≤ (1 : Y ⟶ H).left ⁻¹ᵁ C.W a)
    (hg : ⊤ ≤ g.left ⁻¹ᵁ C.W a') (hkg : ⊤ ≤ (k * g).left ⁻¹ᵁ C.W a'),
    ((k * g).left.appLE _ ⊤ hkg).hom v * ((1 : Y ⟶ H).left.appLE _ ⊤ h₁).hom u =
      (k.left.appLE _ ⊤ hk).hom u * (g.left.appLE _ ⊤ hg).hom v

variable {C a a'}

theorem le_comp {Y Y' : Over S} {X : Over S} (φ : Y' ⟶ Y) {k : Y ⟶ X} {k' : Y' ⟶ X} (e : k' = φ ≫ k)
    {V : X.left.Opens} (h : ⊤ ≤ k.left ⁻¹ᵁ V) : ⊤ ≤ k'.left ⁻¹ᵁ V := by
  subst e
  exact φ.left.preimage_mono h

theorem ev_comp {Y Y' : Over S} {X : Over S} (φ : Y' ⟶ Y) {k : Y ⟶ X} {k' : Y' ⟶ X} (e : k' = φ ≫ k)
    {V : X.left.Opens} (h : ⊤ ≤ k.left ⁻¹ᵁ V) (h' : ⊤ ≤ k'.left ⁻¹ᵁ V) (u : Γ(X.left, V)) :
    φ.left.appTop.hom ((k.left.appLE V ⊤ h).hom u) = (k'.left.appLE V ⊤ h').hom u :=
  appTop_appLE _ _ _ (by rw [e]; rfl) V h h' u

theorem inK_comp {Y Y' : Over S} (φ : Y' ⟶ Y) {k : Y ⟶ H} (h : C.InK a k) : C.InK a (φ ≫ k) := by
  obtain ⟨h, h₁, e⟩ := h
  refine ⟨le_comp φ rfl h, le_comp φ (MonObj.comp_one φ).symm h₁, fun j hj => ?_⟩
  rw [← ev_comp φ rfl h, ← ev_comp φ (MonObj.comp_one φ).symm h₁, e j hj]

theorem one_le (h : ⊤ ≤ eSec H ⁻¹ᵁ C.W a) (Y : Over S) : ⊤ ≤ (1 : Y ⟶ H).left ⁻¹ᵁ C.W a :=
  (toUnit Y).left.preimage_mono h

end Points

theorem exists_universal {R : Type} [CommRing R] [IsNoetherianRing R] {G : Over (Sp R)} [GrpObj G]
    [LocallyOfFiniteType G.hom] [QuasiCompact G.hom] (C : Charts G.left) (a a' : {i // C.wt i = C.c₀})
    (he : ⊤ ≤ eSec G ⁻¹ᵁ C.W a) :
    ∃ (Z : Over (Sp R)) (k₀ g₀ : Z ⟶ G), LocallyOfFiniteType Z.hom ∧ QuasiCompact Z.hom ∧ C.InK a k₀ ∧
      ⊤ ≤ g₀.left ⁻¹ᵁ C.W a' ∧ ∀ (Y : Over (Sp R)) (k g : Y ⟶ G), C.InK a k → ⊤ ≤ g.left ⁻¹ᵁ C.W a' →
        ∃ φ : Y ⟶ Z, k = φ ≫ k₀ ∧ g = φ ≫ g₀ := by
  have : LocallyOfFiniteType (G ⊗ G).hom :=
    inferInstanceAs (LocallyOfFiniteType (pullback.fst G.hom G.hom ≫ G.hom))
  have : QuasiCompact (G ⊗ G).hom := inferInstanceAs (QuasiCompact (pullback.fst G.hom G.hom ≫ G.hom))
  obtain ⟨Z₁, z₁, _, _, h₁, u₁⟩ := open_rep (G ⊗ G) ((fst G G).left ⁻¹ᵁ C.W a ⊓ (snd G G).left ⁻¹ᵁ C.W a')
  have hk : ⊤ ≤ (z₁ ≫ fst G G).left ⁻¹ᵁ C.W a := fun x hx => (h₁ hx).1
  have hg : ⊤ ≤ (z₁ ≫ snd G G).left ⁻¹ᵁ C.W a' := fun x hx => (h₁ hx).2
  obtain ⟨Z₂, z₂, _, _, h₂, u₂⟩ := zero_rep Z₁ (J := {j // C.wt j = C.c₀})
    (fun j => ((z₁ ≫ fst G G).left.appLE _ ⊤ hk).hom (C.r a j.1))
    (fun j => ((1 : Z₁ ⟶ G).left.appLE _ ⊤ (one_le he Z₁)).hom (C.r a j.1))
  refine ⟨Z₂, z₂ ≫ z₁ ≫ fst G G, z₂ ≫ z₁ ≫ snd G G, inferInstance, inferInstance,
    ⟨le_comp z₂ rfl hk, one_le he _, fun j hj => ?_⟩, le_comp z₂ rfl hg, ?_⟩
  · rw [← ev_comp z₂ rfl hk, ← ev_comp z₂ (MonObj.comp_one z₂).symm (one_le he Z₁)]
    exact h₂ ⟨j, hj⟩
  · rintro Y k g ⟨h, h', e⟩ hg'
    obtain ⟨φ, hφ⟩ := u₁ Y (lift k g) fun x hx => by
      constructor
      · exact (show ⊤ ≤ (lift k g ≫ fst G G).left ⁻¹ᵁ C.W a by rwa [lift_fst]) hx
      · exact (show ⊤ ≤ (lift k g ≫ snd G G).left ⁻¹ᵁ C.W a' by rwa [lift_snd]) hx
    have e₁ : k = φ ≫ z₁ ≫ fst G G := by rw [← Category.assoc, hφ, lift_fst]
    have e₂ : g = φ ≫ z₁ ≫ snd G G := by rw [← Category.assoc, hφ, lift_snd]
    obtain ⟨ψ, rfl⟩ := u₂ Y φ fun j => by
      rw [ev_comp φ e₁ hk h, ev_comp φ (MonObj.comp_one φ).symm (one_le he Z₁) h']
      exact e j.1 j.2
    exact ⟨ψ, by simpa using e₁, by simpa using e₂⟩

section Spread
variable {R : Type} [CommRing R] [IsDomain R] [IsNoetherianRing R] {G : Over (Sp R)} [GrpObj G]
  [LocallyOfFiniteType G.hom] [QuasiCompact G.hom] {C : Charts G.left} {a a' : {i // C.wt i = C.c₀}}
  (he : ⊤ ≤ eSec G ⁻¹ᵁ C.W a) {Sg : Set (Sp R)} (hD : Dense Sg)
include he hD

theorem stab_generic
    (H : ∀ x ∈ Sg, ∃ (K : Type) (_ : Field K) (t : Sp K ⟶ Sp R), Set.range t = {x} ∧
      ∀ T : Over (Sp K), Stab C a a' (Over.mk (T.hom ≫ t)))
    (T : Over (Sp (FractionRing R))) : Stab C a a' (Over.mk (T.hom ≫ Out.jK R)) := by
  obtain ⟨Z, k₀, g₀, _, _, hk, hg, u⟩ := exists_universal C a a' he
  intro k g hk' hg'
  obtain ⟨φ, rfl, rfl⟩ := u _ k g hk' hg'
  rw [← MonObj.comp_mul]
  refine spread_open Z hD ((k₀ * g₀).left ⁻¹ᵁ C.W a') (fun x hx => ?_) T φ
  obtain ⟨K, _, t, ht, h⟩ := H x hx
  refine ⟨K, inferInstance, t, ht, fun T ψ => ?_⟩
  have := h T _ _ (inK_comp ψ hk) (le_comp ψ rfl hg)
  rwa [← MonObj.comp_mul] at this

theorem idn_generic (p : Γ(G.left, C.W a)) (v : Γ(G.left, C.W a'))
    (H : ∀ x ∈ Sg, ∃ (K : Type) (_ : Field K) (t : Sp K ⟶ Sp R), Set.range t = {x} ∧
      ∀ T : Over (Sp K), Idn C a a' p v (Over.mk (T.hom ≫ t)))
    (T : Over (Sp (FractionRing R))) : Idn C a a' p v (Over.mk (T.hom ≫ Out.jK R)) := by
  obtain ⟨Z, k₀, g₀, _, _, hk, hg, u⟩ := exists_universal C a a' he
  obtain ⟨Z₁, z, _, _, hz, u₁⟩ := open_rep Z ((k₀ * g₀).left ⁻¹ᵁ C.W a')
  have hm : ⊤ ≤ ((z ≫ k₀) * (z ≫ g₀)).left ⁻¹ᵁ C.W a' := by
    rw [← MonObj.comp_mul]; exact hz
  have hk₁ := inK_comp z hk
  have hg₁ := le_comp z rfl hg
  intro k g hk' h₁ h₂ hg' h₃
  obtain ⟨φ, rfl, rfl⟩ := u _ k g hk' hg'
  obtain ⟨ψ, rfl⟩ := u₁ _ φ (by rw [← MonObj.comp_mul] at h₃; exact h₃)
  have key := spread_eq Z₁ hD
    ((((z ≫ k₀) * (z ≫ g₀)).left.appLE _ ⊤ hm).hom v * ((1 : Z₁ ⟶ G).left.appLE _ ⊤ (one_le he _)).hom p)
    (((z ≫ k₀).left.appLE _ ⊤ hk₁.1).hom p * ((z ≫ g₀).left.appLE _ ⊤ hg₁).hom v) (fun x hx => by
      obtain ⟨K, _, t, ht, h⟩ := H x hx
      refine ⟨K, inferInstance, t, ht, fun T χ => ?_⟩
      have e := (MonObj.comp_mul χ (z ≫ k₀) (z ≫ g₀)).symm
      rw [map_mul, map_mul, ev_comp χ e hm (le_comp χ e hm),
        ev_comp χ (MonObj.comp_one χ).symm (one_le he _) (one_le he _),
        ev_comp χ rfl hk₁.1 (le_comp χ rfl hk₁.1), ev_comp χ rfl hg₁ (le_comp χ rfl hg₁)]
      exact h T _ _ (inK_comp χ hk₁) _ _ _ _) T ψ
  rwa [map_mul, map_mul, ev_comp ψ (by rw [MonObj.comp_mul, Category.assoc, Category.assoc]) hm h₃,
    ev_comp ψ (MonObj.comp_one ψ).symm (one_le he _) h₂, ev_comp ψ (Category.assoc _ _ _) hk₁.1 h₁,
    ev_comp ψ (Category.assoc _ _ _) hg₁ hg'] at key

end Spread

section Push
variable {S S' : Scheme.{0}} {f : S' ⟶ S} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G']
  {F : G'.left ⟶ G.left} [IsAffineHom F] (hF : IsGrpPullback G' G f F) {C : Charts G.left}
  {a a' : {i // C.wt i = C.c₀}} {T : Over S'}

theorem push_surjective : Function.Surjective (pushHom hF T) := fun c =>
  ⟨Over.homMk (hF.1.lift c.left T.hom (Over.w c)) (hF.1.lift_snd _ _ _),
    Over.OverMorphism.ext (hF.1.lift_fst _ _ _)⟩

theorem le_push {k : T ⟶ G'} {k' : Over.mk (T.hom ≫ f) ⟶ G} (e : k' = pushHom hF T k) (V : G.left.Opens) :
    ⊤ ≤ k.left ⁻¹ᵁ F ⁻¹ᵁ V ↔ ⊤ ≤ k'.left ⁻¹ᵁ V := by
  subst e
  rfl

theorem ev_push {k : T ⟶ G'} {k' : Over.mk (T.hom ≫ f) ⟶ G} (e : k' = pushHom hF T k) {V : G.left.Opens}
    (h : ⊤ ≤ k.left ⁻¹ᵁ F ⁻¹ᵁ V) (h' : ⊤ ≤ k'.left ⁻¹ᵁ V) (u : Γ(G.left, V)) :
    (k.left.appLE (F ⁻¹ᵁ V) ⊤ h).hom ((F.app V).hom u) = (k'.left.appLE V ⊤ h').hom u :=
  appLE_app _ F _ (by rw [e]; rfl) V h h' u

theorem inK_push (k : T ⟶ G') : (C.pull F).InK a k ↔ C.InK a (pushHom hF T k) := by
  have e := (map_one (pushHom hF T)).symm
  constructor
  · rintro ⟨h, h₁, w⟩
    exact ⟨h, (le_push hF e _).1 h₁, fun j hj =>
      (ev_push hF rfl h h _).symm.trans ((w j hj).trans (ev_push hF e h₁ _ _))⟩
  · rintro ⟨h, h₁, w⟩
    exact ⟨h, (le_push hF e _).2 h₁, fun j hj =>
      (ev_push hF rfl h h _).trans ((w j hj).trans (ev_push hF e _ h₁ _).symm)⟩

include hF in
theorem stab_push : Stab (C.pull F) a a' T ↔ Stab C a a' (Over.mk (T.hom ≫ f)) := by
  constructor
  · intro h k g hk hg
    obtain ⟨k, rfl⟩ := push_surjective hF k
    obtain ⟨g, rfl⟩ := push_surjective hF g
    exact (le_push hF (map_mul _ k g).symm _).1 (h k g ((inK_push hF k).2 hk) hg)
  · intro h k g hk hg
    exact (le_push hF (map_mul _ k g).symm _).2 (h _ _ ((inK_push hF k).1 hk) hg)

include hF in
theorem idn_push (u : Γ(G.left, C.W a)) (v : Γ(G.left, C.W a')) :
    Idn (C.pull F) a a' ((F.app _).hom u) ((F.app _).hom v) T ↔ Idn C a a' u v (Over.mk (T.hom ≫ f)) := by
  have e := (map_one (pushHom hF T)).symm
  constructor
  · intro h k g hk h₁ h₂ h₃ h₄
    obtain ⟨k, rfl⟩ := push_surjective hF k
    obtain ⟨g, rfl⟩ := push_surjective hF g
    have m := (map_mul (pushHom hF T) k g).symm
    rw [← ev_push hF m ((le_push hF m _).2 h₄), ← ev_push hF e ((le_push hF e _).2 h₂),
      ← ev_push hF (k := k) rfl h₁, ← ev_push hF (k := g) rfl h₃]
    exact h k g ((inK_push hF k).2 hk) _ _ _ _
  · intro h k g hk h₁ h₂ h₃ h₄
    have m := (map_mul (pushHom hF T) k g).symm
    have := h _ (pushHom hF T g) ((inK_push hF k).1 hk) h₁ ((le_push hF e _).1 h₂) h₃ ((le_push hF m _).1 h₄)
    rw [← ev_push hF m h₄, ← ev_push hF e h₂] at this
    exact this.trans (congrArg₂ (· * ·) (ev_push hF rfl h₁ h₁ u).symm (ev_push hF rfl h₃ h₃ v).symm)

include hF in
theorem based_pull {d : ℕ} {c : Fin d → C.Cl} {j : Fin d → C.I} (h : C.Based c a j) : (C.pull F).Based c a j := by
  have e : eSec G' ≫ F = (f : (𝟙_ (Over S')).left ⟶ (𝟙_ (Over S)).left) ≫ eSec G := by
    have e := congrArg (fun z => z.left) (map_one (pushHom hF (𝟙_ (Over S'))))
    have e₁ : (1 : 𝟙_ (Over S') ⟶ G') = η[G'] := by
      rw [Hom.one_def]; simp
    rw [e₁] at e
    refine e.trans ?_
    show (toUnit _ ≫ η[G]).left = _
    simp [eSec]
  have key : ∀ V : G.left.Opens, ⊤ ≤ eSec G ⁻¹ᵁ V → ⊤ ≤ eSec G' ⁻¹ᵁ F ⁻¹ᵁ V := fun V hV => by
    rw [← Scheme.Hom.comp_preimage, e]
    exact f.preimage_mono hV
  refine ⟨key _ h.1, fun n => ⟨(h.2 n).1, ?_⟩⟩
  have := key _ (h.2 n).2
  rwa [Scheme.preimage_basicOpen] at this

end Push

section Torus
variable {S : Scheme.{0}} {H : Over S} [GrpObj H] {C : Charts H.left} {a a' : {i // C.wt i = C.c₀}} {d : ℕ}
  {j : Fin d → C.I} {i : splitTorus S (Fin d → ℤ) ⟶ H} (hi : C.KerIs a j i)
include hi

theorem stable_iff : Stable i (C.W a') ↔ ∀ Y, Stab C a a' Y := by
  constructor
  · intro h Y k g hk hg
    obtain ⟨t, rfl⟩ := (hi.2.1 Y k).1 hk
    exact h Y t g hg
  · intro h Y t g hg
    exact h Y _ g ((hi.2.1 Y _).2 ⟨t, rfl⟩) hg

theorem hasWt_zero_iff (v : Γ(H.left, C.W a')) : HasWt i (C.W a') v 0 ↔ ∀ Y, Idn C a a' 1 v Y := by
  constructor
  · intro h Y k g hk h₁ h₂ h₃ h₄
    obtain ⟨t, rfl⟩ := (hi.2.1 Y k).1 hk
    rw [h Y t g h₃ h₄, charUnit_zero_val, map_one, map_one, map_one, _root_.mul_one]
  · intro h Y t g h₃ h₄
    obtain ⟨h₁, h₂, w⟩ := (hi.2.1 Y _).2 ⟨t, rfl⟩
    have := h Y _ g ⟨h₁, h₂, w⟩ h₁ h₂ h₃ h₄
    rw [map_one, map_one, _root_.mul_one] at this
    rwa [charUnit_zero_val, map_one]

theorem hasWt_single_iff {c : Fin d → C.Cl} (hb : C.Based c a j) (n : Fin d) (v : Γ(H.left, C.W a')) :
    HasWt i (C.W a') v (Pi.single n 1) ↔ ∀ Y, Idn C a a' (C.r a (j n)) v Y := by
  constructor
  · intro h Y k g hk h₁ h₂ h₃ h₄
    obtain ⟨t, rfl⟩ := (hi.2.1 Y k).1 hk
    rw [h Y t g h₃ h₄, hi.2.2 Y t n h₁ h₂]
    ring
  · intro h Y t g h₃ h₄
    obtain ⟨h₁, h₂, w⟩ := (hi.2.1 Y _).2 ⟨t, rfl⟩
    have := h Y _ g ⟨h₁, h₂, w⟩ h₁ h₂ h₃ h₄
    rw [hi.2.2 Y t n h₁ h₂] at this
    have hu : IsUnit (((1 : Y ⟶ H).left.appLE _ ⊤ h₂).hom (C.r a (j n))) := by
      refine Y.left.toRingedSpace.isUnit_of_isUnit_germ _ _ fun y hy => (Y.left.mem_basicOpen _ y hy).1 ?_
      exact (Scheme.basicOpen_appLE (1 : Y ⟶ H).left ⊤ _ h₂ (C.r a (j n))).ge
        ⟨hy, (toUnit Y).left.preimage_mono (hb.2 n).2 hy⟩
    refine hu.mul_right_cancel (this.trans ?_)
    ring

end Torus

theorem stable_and_hasWt_generic : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] [Smooth G.hom] [IsSeparated G.hom] [QuasiCompact G.hom] (C : Charts G.left) (d : ℕ) (c : Fin d → C.Cl) (Sg : Set (Sp R)) [IsAffineHom (pullback.fst G.hom (Out.jK R))], Dense Sg → C.SplitOn c Sg → ∀ (a) (j : Fin d → C.I), C.Based c a j → ∀ i : splitTorus (Sp (FractionRing R)) (Fin d → ℤ) ⟶ ((Over.pullback (Out.jK R)).obj G), Charts.KerIs (H := ((Over.pullback (Out.jK R)).obj G)) (C.pull (pullback.fst G.hom (Out.jK R))) a j i → (∀ a', Stable i ((C.pull (pullback.fst G.hom (Out.jK R))).W a')) ∧ (∀ a' j', C.wt j' = C.c₀ → HasWt i ((C.pull (pullback.fst G.hom (Out.jK R))).W a') ((C.pull (pullback.fst G.hom (Out.jK R))).r a' j') 0) ∧ ∀ a' j' n, C.wt j' = c n → HasWt i ((C.pull (pullback.fst G.hom (Out.jK R))).W a') ((C.pull (pullback.fst G.hom (Out.jK R))).r a' j') (Pi.single n 1) := by
  intro R _ _ _ G _ _ _ _ _ C d c Sg _ hD hS a j hb i hi
  have hF := isGrpPullback_pullback G (Out.jK R)
  have fib : ∀ x ∈ Sg, ∃ (K : Type) (_ : Field K) (t : Sp K ⟶ Sp R), Set.range t = {x} ∧ ∀ T : Over (Sp K),
      (∀ a', Stab C a a' (Over.mk (T.hom ≫ t))) ∧
      (∀ a' j', C.wt j' = C.c₀ → Idn C a a' 1 (C.r a' j') (Over.mk (T.hom ≫ t))) ∧
      ∀ a' j' n, C.wt j' = c n → Idn C a a' (C.r a (j n)) (C.r a' j') (Over.mk (T.hom ≫ t)) := by
    intro x hx
    obtain ⟨K, _, t, _, ht, hc, i', hT⟩ := hS x hx
    have hF' := isGrpPullback_pullback G t
    have hb' := based_pull hF' hb
    have : Smooth ((Over.pullback t).obj G).hom := inferInstanceAs (Smooth (pullback.snd G.hom t))
    have : IsSeparated ((Over.pullback t).obj G).hom := inferInstanceAs (IsSeparated (pullback.snd G.hom t))
    have : QuasiCompact ((Over.pullback t).obj G).hom := inferInstanceAs (QuasiCompact (pullback.snd G.hom t))
    have hk := GlobalTheory.ZJ.Charts.kerIs_of_torus K ((Over.pullback t).obj G) (C.pull (pullback.fst G.hom t)) d c i' a j hc hT hb'
    refine ⟨K, inferInstance, t, ht, fun T => ⟨fun a' => ?_, fun a' j' h => ?_, fun a' j' n h => ?_⟩⟩
    · exact (stab_push hF').1 ((stable_iff hk).1 (hT.stable a') T)
    · refine (idn_push hF' _ _).1 ?_
      rw [map_one]
      exact (hasWt_zero_iff hk _).1 (hT.inv a' j' h) T
    · exact (idn_push hF' _ _).1 ((hasWt_single_iff hk hb' n _).1 (hT.wt a' j' n h) T)
  refine ⟨fun a' => (stable_iff hi).2 fun T => (stab_push hF).2 (stab_generic hb.1 hD (fun x hx => ?_) T),
    fun a' j' h => (hasWt_zero_iff hi _).2 fun T => ?_,
    fun a' j' n h => (hasWt_single_iff hi (based_pull hF hb) n _).2 fun T =>
      (idn_push hF _ _).2 (idn_generic hb.1 hD _ _ (fun x hx => ?_) T)⟩
  · obtain ⟨K, _, t, ht, w⟩ := fib x hx
    exact ⟨K, inferInstance, t, ht, fun T => (w T).1 a'⟩
  · have := (idn_push hF 1 (C.r a' j')).2 (idn_generic hb.1 hD _ _ (fun x hx => by
      obtain ⟨K, _, t, ht, w⟩ := fib x hx
      exact ⟨K, inferInstance, t, ht, fun T => (w T).2.1 a' j' h⟩) T)
    rw [map_one] at this
    exact this
  · obtain ⟨K, _, t, ht, w⟩ := fib x hx
    exact ⟨K, inferInstance, t, ht, fun T => (w T).2.2 a' j' n h⟩

end GlobalTheory.ZJ.GenericWt
end
