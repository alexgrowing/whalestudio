import Mathlib
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsSchemeOfThickenings
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsAffineOfIsAffinePullbackQuotientOfIsNilpotent
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueTorusCompat
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.InvariantFunctionsDescend
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TorusStableAffineOpenFunctionsWeightGraded
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TorusStableOfSurjective
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsHomOfRingMaps
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.KerAppEqMapAppLEOfIsPullback

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open GlobalTheory.UU GlobalTheory.AffineThickening

noncomputable section
namespace GlobalTheory.TorusQuotientLift

theorem hom_ext_appLE {Y B : Scheme.{0}} (f g : Y ⟶ B)
    (H : ∀ y : Y, ∃ (W : Y.Opens) (V : B.Opens) (hf : W ≤ f ⁻¹ᵁ V) (hg : W ≤ g ⁻¹ᵁ V), y ∈ W ∧ IsAffineOpen V ∧
      f.appLE V W hf = g.appLE V W hg) : f = g := by
  refine Scheme.hom_ext_of_forall f g fun y => ?_
  obtain ⟨W, V, hf, hg, hy, hV, e⟩ := H y
  have key : ∀ (r : Y ⟶ B) (hr : W ≤ r ⁻¹ᵁ V), W.ι ≫ r = W.toSpecΓ ≫ Spec.map (r.appLE V W hr) ≫ hV.fromSpec := by
    intro r hr
    rw [Scheme.Opens.toSpecΓ_SpecMap_appLE_assoc, hV.toSpecΓ_fromSpec, Scheme.Hom.resLE_comp_ι]
  exact ⟨W, hy, by rw [key f hf, key g hg, e]⟩

theorem le_of_preimage_le {Z Y : Scheme.{0}} (i : Z ⟶ Y) [Surjective i] {U V : Y.Opens} (h : i ⁻¹ᵁ U ≤ i ⁻¹ᵁ V) :
    U ≤ V := fun y hy => by
  obtain ⟨z, rfl⟩ := i.surjective y
  exact h hy

theorem exists_preimage_eq {Z Y : Scheme.{0}} (i : Z ⟶ Y) [IsClosedImmersion i] (U : Z.Opens) :
    ∃ V : Y.Opens, i ⁻¹ᵁ V = U := by
  obtain ⟨O, hO, hO'⟩ := i.isClosedEmbedding.isInducing.isOpen_iff.mp U.isOpen
  exact ⟨⟨O, hO⟩, TopologicalSpace.Opens.ext hO'⟩

theorem exists_factor {R T C : Type} [CommRing R] [CommRing T] [CommRing C] (f : R →+* C)
    (hf : Function.Injective f) (g : T →+* C) (h : ∀ t, ∃ r, f r = g t) : ∃ k : T →+* R, ∀ t, f (k t) = g t := by
  choose k hk using h
  exact ⟨⟨⟨⟨k, hf (by rw [hk, map_one, map_one])⟩, fun a b => hf (by simp only [hk, map_mul])⟩,
    hf (by rw [hk, map_zero, map_zero]), fun a b => hf (by simp only [hk, map_add])⟩, hk⟩

abbrev baseMap {A : Type} [CommRing A] {G : Scheme.{0}} (g : G ⟶ Spec (CommRingCat.of A)) (V : G.Opens) :
    A →+* Γ(G, V) := ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ g.appLE ⊤ V le_top).hom

def subPresheaf {G B₀ : Scheme.{0}} (R : ∀ V : G.Opens, Subring Γ(G, V))
    (hres : ∀ (V V' : G.Opens) (h : V' ≤ V), ∀ a ∈ R V, rs h a ∈ R V') (W : B₀.Opens → G.Opens) (hW : Monotone W) :
    B₀.Opensᵒᵖ ⥤ CommRingCat.{0} where
  obj U := .of (R (W U.unop))
  map {V U} i := CommRingCat.ofHom ((rs (hW i.unop.le)).restrict _ _ (hres _ _ _))
  map_id U := by
    ext x
    exact congr($(G.presheaf.map_id (op (W U.unop))).hom x.1)
  map_comp i j := by
    ext x
    exact (rs_rs _ _ _).symm

theorem appLE_rs {Z Y : Scheme.{0}} (f : Z ⟶ Y) {V V' : Y.Opens} {U U' : Z.Opens} (h : V' ≤ V) (h' : U' ≤ U)
    (e : U ≤ f ⁻¹ᵁ V) (e' : U' ≤ f ⁻¹ᵁ V') (a : Γ(Y, V)) :
    (f.appLE V' U' e').hom (rs h a) = rs h' ((f.appLE V U e).hom a) :=
  congr($((f.map_appLE e' (homOfLE h).op).trans (f.appLE_map e (homOfLE h').op).symm).hom a)

set_option backward.isDefEq.respectTransparency false in

theorem exists_quotient {A : Type} [CommRing A] {J : Ideal A} (hJ : IsNilpotent J) {G G₀ B₀ : Scheme.{0}}
    (g : G ⟶ Spec (CommRingCat.of A)) (F : G₀ ⟶ G) [IsClosedImmersion F] [Surjective F]
    (b₀ : B₀ ⟶ Spec (CommRingCat.of (A ⧸ J))) (q₀ : G₀ ⟶ B₀) (hF : F ≫ g = q₀ ≫ b₀ ≫ red J)
    (R : ∀ V : G.Opens, Subring Γ(G, V))
    (hres : ∀ (V V' : G.Opens) (h : V' ≤ V), ∀ a ∈ R V, rs h a ∈ R V')
    (hbase : ∀ V c, (g.appLE ⊤ V le_top).hom c ∈ R V)
    (hinj : ∀ U, Function.Injective (q₀.app U).hom)
    (hdesc : ∀ (U : B₀.Opens) (V : G.Opens) (e : F ⁻¹ᵁ V = q₀ ⁻¹ᵁ U), ∀ a ∈ R V,
      ∃ c, (q₀.app U).hom c = (F.appLE V _ e.ge).hom a)
    (𝒰 : Set B₀.Opens) (haff : ∀ U ∈ 𝒰, IsAffineOpen U) (hbasic : ∀ U ∈ 𝒰, ∀ f : Γ(B₀, U), B₀.basicOpen f ∈ 𝒰)
    (hcov : ∀ b : B₀, ∃ U ∈ 𝒰, b ∈ U)
    (hsurj : ∀ U ∈ 𝒰, ∀ (V : G.Opens) (e : F ⁻¹ᵁ V = q₀ ⁻¹ᵁ U) (c : Γ(B₀, U)),
      ∃ a ∈ R V, (F.appLE V _ e.ge).hom a = (q₀.app U).hom c)
    (hker : ∀ U ∈ 𝒰, ∀ (V : G.Opens) (e : F ⁻¹ᵁ V = q₀ ⁻¹ᵁ U) (a : R V), (F.appLE V _ e.ge).hom a = 0 →
      a ∈ J.map ((baseMap g V).codRestrict (R V) fun _ => hbase V _))
    (hloc : ∀ U ∈ 𝒰, ∀ (V : G.Opens) (_ : F ⁻¹ᵁ V = q₀ ⁻¹ᵁ U) (a : R V) (V' : G.Opens) (h : V' ≤ V),
      V' = G.basicOpen a.1 →
      letI := ((rs h).restrict _ _ (hres _ _ h)).toAlgebra
      IsLocalization.Away a (R V')) :
    ∃ (B : Scheme.{0}) (s : B ⟶ Spec (CommRingCat.of A)) (q : G ⟶ B) (j : B₀ ⟶ B), q ≫ s = g ∧
      IsPullback j b₀ s (red J) ∧ q₀ ≫ j = F ≫ q ∧ ∀ b : B, ∃ V : B.Opens, b ∈ V ∧ j ⁻¹ᵁ V ∈ 𝒰 ∧ IsAffineOpen V ∧
        Function.Injective (q.app V).hom ∧ ∀ a, a ∈ R (q ⁻¹ᵁ V) ↔ ∃ c, (q.app V).hom c = a := by
  choose W hW using fun U : B₀.Opens => exists_preimage_eq F (q₀ ⁻¹ᵁ U)
  have hm : Monotone W := fun U U' h => le_of_preimage_le F (by rw [hW, hW]; exact q₀.preimage_mono h)
  let 𝒜 := subPresheaf R hres W hm
  choose π₀ hπ₀ using fun U : B₀.Opens => exists_factor _ (hinj U)
    ((F.appLE (W U) _ (hW U).ge).hom.comp (R (W U)).subtype) fun a => hdesc U _ (hW U) a.1 a.2
  have hπ : ∀ U (a : R (W U)), (q₀.app U).hom (π₀ U a) = (F.appLE (W U) _ (hW U).ge).hom a.1 := hπ₀
  let π : 𝒜 ⟶ B₀.presheaf :=
    { app U := CommRingCat.ofHom (π₀ U.unop)
      naturality U U' i := by
        ext a
        apply hinj U'.unop
        refine (hπ _ _).trans (Eq.trans ?_ (app_rs q₀ i.unop.le _).symm)
        exact (appLE_rs F (hm i.unop.le) _ _ _ _).trans (congrArg _ (hπ _ a).symm) }
  let inc : ∀ U, 𝒜.obj (op U) ⟶ Γ(G, W U) := fun U => CommRingCat.ofHom (R (W U)).subtype
  let α : ∀ U, A →+* R (W U) := fun U => (baseMap g (W U)).codRestrict (R _) fun _ => hbase _ _
  have hk : ∀ U ∈ 𝒰, RingHom.ker (π₀ U) ≤ J.map (α U) := fun U hU a ha =>
    hker U hU _ (hW U) a (by rw [← hπ, (RingHom.mem_ker).1 ha, map_zero])
  obtain ⟨B, j, _, _, φ, hφ, hφ'⟩ := ThickGlue.exists_scheme_of_thickenings B₀ 𝒰 haff hbasic
    (eq_top_iff.2 fun b _ => TopologicalSpace.Opens.mem_sSup.2 (hcov b)) 𝒜 π
    (fun U hU => ⟨fun c => by
      obtain ⟨a, ha, e⟩ := hsurj U hU _ (hW U) c
      exact ⟨⟨a, ha⟩, hinj U ((hπ U ⟨a, ha⟩).trans e)⟩, by
      obtain ⟨n, hn⟩ := hJ
      have h : J.map (α U) ^ n = ⊥ := by rw [← Ideal.map_pow, hn]; exact Ideal.map_bot
      exact ⟨n, eq_bot_iff.2 ((Ideal.pow_right_mono (hk U hU) n).trans h.le)⟩⟩)
    (fun U hU a => hloc U hU _ (hW U) a _ _ (eq_of_preimage_eq (i := F) (by
      rw [hW, Scheme.preimage_basicOpen, Scheme.preimage_basicOpen]
      refine (congrArg G₀.basicOpen (hπ U a)).trans ?_
      rw [Scheme.basicOpen_appLE, Scheme.preimage_basicOpen, inf_eq_right]
      exact (G₀.basicOpen_le _).trans (hW U).le)))
  have hbas : ∀ (b : B) (O : B.Opens), b ∈ O → ∃ V : B.Opens, j ⁻¹ᵁ V ∈ 𝒰 ∧ b ∈ V ∧ V ≤ O := by
    intro b O hb
    obtain ⟨b, rfl⟩ := j.surjective b
    obtain ⟨U, hU, hbU⟩ := hcov b
    obtain ⟨f, hf, hbf⟩ := (haff U hU).exists_basicOpen_le (V := j ⁻¹ᵁ O) ⟨b, hb⟩ hbU
    obtain ⟨V, hV⟩ := exists_preimage_eq j (B₀.basicOpen f)
    exact ⟨V, hV ▸ hbasic U hU f, hV.ge hbf, le_of_preimage_le j (hV ▸ hf)⟩
  let κ := {V : B.Opens // j ⁻¹ᵁ V ∈ 𝒰}
  let ψ : ∀ k : κ, Γ(B, k.1) ⟶ Γ(G, W (j ⁻¹ᵁ k.1)) := fun k =>
    (φ k.1 k.2).hom ≫ inc _
  have hψ : ∀ (k m : κ) (e : m.1 ≤ k.1), B.presheaf.map (homOfLE e).op ≫ ψ m =
      ψ k ≫ G.presheaf.map (homOfLE (hm (j.preimage_mono e))).op := fun k m e => by
    simp only [ψ]
    rw [← Category.assoc, hφ' _ _ k.2 m.2 e, Category.assoc, Category.assoc]
    rfl
  have hmem : ∀ (x : G₀) (V : B.Opens), F x ∈ W (j ⁻¹ᵁ V) ↔ j (q₀ x) ∈ V := fun x V =>
    SetLike.ext_iff.1 (hW (j ⁻¹ᵁ V)) x
  obtain ⟨q, hq⟩ := RingGlue.exists_hom_of_ring_maps G B κ (fun k => W (j ⁻¹ᵁ k.1)) (fun k => k.1) (fun k => (hφ k.1 k.2).1) ψ
    (fun y => by
      obtain ⟨x, rfl⟩ := F.surjective y
      obtain ⟨V, h, hb, -⟩ := hbas (j (q₀ x)) ⊤ trivial
      exact ⟨⟨V, h⟩, (hmem x V).2 hb⟩)
    (fun k l y hk hl => by
      obtain ⟨x, rfl⟩ := F.surjective y
      obtain ⟨V, h, hb, hle⟩ := hbas (j (q₀ x)) (k.1 ⊓ l.1) ⟨(hmem x _).1 hk, (hmem x _).1 hl⟩
      exact ⟨⟨V, h⟩, _, _, hle.trans inf_le_left, hle.trans inf_le_right, (hmem x V).2 hb,
        hψ k ⟨V, h⟩ _, hψ l ⟨V, h⟩ _⟩)
  choose hq₁ hq₂ using hq
  let β : ∀ U, Γ(Spec (CommRingCat.of A), ⊤) ⟶ 𝒜.obj (op U) := fun U =>
    CommRingCat.ofHom (R := Γ(Spec (CommRingCat.of A), ⊤)) (S := R (W U))
      ((g.appLE ⊤ (W U) le_top).hom.codRestrict (R _) (hbase _))
  have hβ : ∀ (k m : κ) (e : m.1 ≤ k.1), (Spec (CommRingCat.of A)).presheaf.map (homOfLE (le_refl ⊤)).op ≫
      β _ ≫ (φ m.1 m.2).inv = (β _ ≫ (φ k.1 k.2).inv) ≫ B.presheaf.map (homOfLE e).op := fun k m e => by
    rw [← cancel_mono (φ m.1 m.2).hom]
    simp only [Category.assoc]
    rw [hφ' _ _ k.2 m.2 e, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]
    ext c
    exact Subtype.ext (appLE_rs g (le_refl ⊤) (hm (j.preimage_mono e)) _ _ c)
  obtain ⟨s, hs⟩ := RingGlue.exists_hom_of_ring_maps B (Spec (CommRingCat.of A)) κ (fun k => k.1) (fun _ => ⊤) (fun _ => isAffineOpen_top _)
    (fun k => β _ ≫ (φ k.1 k.2).inv)
    (fun b => by
      obtain ⟨V, h, hb, -⟩ := hbas b ⊤ trivial
      exact ⟨⟨V, h⟩, hb⟩)
    (fun k l b hk hl => by
      obtain ⟨V, h, hb, hle⟩ := hbas b (k.1 ⊓ l.1) ⟨hk, hl⟩
      exact ⟨⟨V, h⟩, hle.trans inf_le_left, hle.trans inf_le_right, le_rfl, le_rfl, hb,
        hβ k ⟨V, h⟩ _, hβ l ⟨V, h⟩ _⟩)
  choose hs₁ hs₂ using hs
  have hπ' : ∀ U, π.app (op U) ≫ q₀.app U =
      inc U ≫ F.appLE (W U) _ (hW U).ge := fun U => by
    ext a
    exact hπ U a
  have hsq : q₀ ≫ j = F ≫ q := hom_ext_appLE _ _ fun x => by
    obtain ⟨V, h, hb, -⟩ := hbas (j (q₀ x)) ⊤ trivial
    refine ⟨q₀ ⁻¹ᵁ j ⁻¹ᵁ V, V, le_rfl, (hW _).ge.trans (F.preimage_mono (hq₁ ⟨V, h⟩)), hb, (hφ V h).1, ?_⟩
    rw [← Scheme.Hom.appLE_comp_appLE F q V (W (j ⁻¹ᵁ V)) _ (hq₁ ⟨V, h⟩) (hW _).ge, hq₂ ⟨V, h⟩]
    simp only [ψ, Category.assoc]
    rw [← hπ', ← Category.assoc, (hφ V h).2]
    exact (Scheme.Hom.appLE_eq_app _).trans (Scheme.Hom.comp_app _ _ _)
  have hqs : q ≫ s = g := hom_ext_appLE _ _ fun y => by
    obtain ⟨x, rfl⟩ := F.surjective y
    obtain ⟨V, h, hb, -⟩ := hbas (j (q₀ x)) ⊤ trivial
    refine ⟨W (j ⁻¹ᵁ V), ⊤, le_top, le_top, (hmem x V).2 hb, isAffineOpen_top _, ?_⟩
    rw [← Scheme.Hom.appLE_comp_appLE q s ⊤ V _ (hs₁ ⟨V, h⟩) (hq₁ ⟨V, h⟩), hq₂ ⟨V, h⟩, hs₂ ⟨V, h⟩]
    simp only [ψ, Category.assoc, Iso.inv_hom_id_assoc]
    rfl
  have hjs : j ≫ s = b₀ ≫ red J := hom_ext_appLE _ _ fun b => by
    obtain ⟨V, h, hb, -⟩ := hbas (j b) ⊤ trivial
    refine ⟨j ⁻¹ᵁ V, ⊤, le_top, le_top, hb, isAffineOpen_top _, ?_⟩
    have : Mono (q₀.app (j ⁻¹ᵁ V)) := ConcreteCategory.mono_of_injective _ (hinj _)
    rw [← cancel_mono (q₀.app (j ⁻¹ᵁ V)), Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE,
      Scheme.Hom.appLE_comp_appLE]
    congr 1
    rw [← hF, ← hqs, ← Category.assoc, hsq, Category.assoc]
  refine ⟨B, s, q, j, hqs, isPullback_red_of_ker_app_le_map A J B₀ B j b₀ s ‹_› hjs fun b => ?_, hsq, fun b => ?_⟩
  · obtain ⟨V, h, hb, -⟩ := hbas b ⊤ trivial
    refine ⟨V, hb, (hφ V h).1, fun c hc => ?_⟩
    have h1 : (φ V h).hom.hom c ∈ J.map (α _) := hk _ h (by
      rw [← (hφ V h).2] at hc
      exact hc)
    have h2 := Ideal.mem_map_of_mem (φ V h).inv.hom h1
    rw [Ideal.map_map, ← CommRingCat.comp_apply, Iso.hom_inv_id] at h2
    rw [hs₂ ⟨V, h⟩]
    exact h2
  · obtain ⟨V, h, hb, -⟩ := hbas b ⊤ trivial
    refine ⟨V, hb, h, (hφ V h).1, ?_⟩
    have e : q ⁻¹ᵁ V = W (j ⁻¹ᵁ V) := eq_of_preimage_eq (i := F) (by
      rw [hW, ← Scheme.Hom.comp_preimage, ← hsq, Scheme.Hom.comp_preimage])
    have key : ∀ (V' : G.Opens) (e : q ⁻¹ᵁ V = V'), (Function.Injective (q.appLE V V' e.ge).hom ∧
        ∀ a, a ∈ R V' ↔ ∃ c, (q.appLE V V' e.ge).hom c = a) → Function.Injective (q.app V).hom ∧
          ∀ a, a ∈ R (q ⁻¹ᵁ V) ↔ ∃ c, (q.app V).hom c = a := by
      rintro _ rfl H
      rwa [Scheme.Hom.appLE_eq_app] at H
    refine key _ e ?_
    rw [hq₂ ⟨V, h⟩]
    have hb := ConcreteCategory.bijective_of_isIso (φ V h).hom
    refine ⟨Subtype.val_injective.comp hb.1, fun a => ⟨fun ha => ?_, ?_⟩⟩
    · obtain ⟨c, hc⟩ := hb.2 ⟨a, ha⟩
      exact ⟨c, congrArg Subtype.val hc⟩
    · rintro ⟨c, rfl⟩
      exact ((φ V h).hom.hom c).2

open MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

section Weights
variable {S S' : Scheme.{0}} {X : Type} [AddCommGroup X] {G : Over S} [GrpObj G] {G' : Over S'} [GrpObj G']

def wtSub (i : splitTorus S X ⟶ G) (V : G.left.Opens) (χ : X) : AddSubgroup Γ(G.left, V) where
  carrier := {a | IsWt i V a χ}
  add_mem' := IsWt.add
  zero_mem' := isWt_zero χ
  neg_mem' := fun {a} ha Z t g h₁ h₂ => by rw [map_neg, map_neg, ha Z t g h₁ h₂, mul_neg]

def wtZero (i : splitTorus S X ⟶ G) (V : G.left.Opens) : Subring Γ(G.left, V) :=
  { wtSub i V 0 with
    one_mem' := isWt_one
    mul_mem' := fun ha hb => _root_.add_zero (0 : X) ▸ IsWt.mul ha hb }

def Graded (i : splitTorus S X ⟶ G) (V : G.left.Opens) : Prop :=
  (∀ u : Γ(G.left, V), ∃ a : X →₀ Γ(G.left, V), (∀ χ, IsWt i V (a χ) χ) ∧ u = a.sum fun _ x => x) ∧
    ∀ a : X →₀ Γ(G.left, V), (∀ χ, IsWt i V (a χ) χ) → (a.sum fun _ x => x) = 0 → a = 0

variable {i : splitTorus S X ⟶ G} {i' : splitTorus S' X ⟶ G'} {V : G.left.Opens} {V' : G'.left.Opens}

theorem Graded.map_eq (h : Graded i' V') (p : Γ(G.left, V) →+* Γ(G'.left, V'))
    (hp : ∀ χ x, IsWt i V x χ → IsWt i' V' (p x) χ) {a : X →₀ Γ(G.left, V)} (ha : ∀ χ, IsWt i V (a χ) χ) {χ : X}
    (hy : IsWt i' V' (p (a.sum fun _ x => x)) χ) : p (a χ) = p (a.sum fun _ x => x) := by
  classical
  have := h.2 (a.mapRange p (map_zero p) - Finsupp.single χ (p (a.sum fun _ x => x))) (fun ψ => by
    refine (wtSub i' V' ψ).sub_mem (hp _ _ (ha ψ)) ?_
    rw [Finsupp.single_apply]
    split_ifs with e
    · exact e ▸ hy
    · exact zero_mem _) (by
      rw [Finsupp.sum_sub_index (fun _ _ _ => rfl), Finsupp.sum_single_index rfl,
        Finsupp.sum_mapRange_index (fun _ => rfl), map_finsuppSum, sub_self])
  simpa [sub_eq_zero] using DFunLike.congr_fun this χ

theorem Graded.exists_lift (h₀ : Graded i V) (h : Graded i' V') (p : Γ(G.left, V) →+* Γ(G'.left, V'))
    (hp : ∀ χ x, IsWt i V x χ → IsWt i' V' (p x) χ) (u : Γ(G.left, V)) {χ : X} (hy : IsWt i' V' (p u) χ) :
    ∃ x, IsWt i V x χ ∧ p x = p u := by
  obtain ⟨a, ha, rfl⟩ := h₀.1 u
  exact ⟨a χ, ha χ, h.map_eq p hp ha hy⟩

theorem Graded.mem_map (h : Graded i V) {A : Type} [CommRing A] (J : Ideal A) (α : A →+* wtZero i V)
    (x : wtZero i V) (hx : x.1 ∈ J.map ((wtZero i V).subtype.comp α)) : x ∈ J.map α := by
  classical
  have key : ∀ y ∈ J.map ((wtZero i V).subtype.comp α), ∀ c, ∃ a : X →₀ Γ(G.left, V), (∀ χ, IsWt i V (a χ) χ) ∧
      c * y = (a.sum fun _ x => x) ∧ ∃ z ∈ J.map α, z.1 = a 0 := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨r, hr, rfl⟩ := hy
      intro c
      obtain ⟨a, ha, rfl⟩ := h.1 c
      refine ⟨a.mapRange (· * (α r).1) (zero_mul _), fun χ => ?_, ?_, ⟨a 0, ha 0⟩ * α r,
        Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem α hr), rfl⟩
      · simpa using IsWt.mul (ha χ) (α r).2
      · rw [Finsupp.sum_mapRange_index (fun _ => rfl), Finsupp.sum_mul]
        rfl
    | zero => exact fun c => ⟨0, isWt_zero, by simp, 0, zero_mem _, rfl⟩
    | add y y' _ _ H H' =>
      intro c
      obtain ⟨a, ha, e, z, hz, f⟩ := H c
      obtain ⟨a', ha', e', z', hz', f'⟩ := H' c
      refine ⟨a + a', fun χ => (ha χ).add (ha' χ), ?_, z + z', add_mem hz hz', congrArg₂ (· + ·) f f'⟩
      rw [Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl), mul_add, e, e']
    | smul d y _ H =>
      intro c
      rw [smul_eq_mul, ← _root_.mul_assoc]
      exact H _
  obtain ⟨a, ha, e, z, hz, f⟩ := key _ hx 1
  rw [_root_.one_mul] at e
  have := h.map_eq (RingHom.id _) (fun _ _ h => h) ha (χ := 0) (by rw [← e]; exact x.2)
  rwa [show x = z from Subtype.ext (e.trans (this.symm.trans f.symm))]

theorem Graded.isLocalization (hV : IsAffineOpen V) (h : Graded i V) (a : wtZero i V) (W : G.left.Opens) (hle : W ≤ V)
    (e : W = G.left.basicOpen a.1) (h' : Graded i W) :
    letI := ((rs hle).restrict (wtZero i V) (wtZero i W) fun _ hx => IsWt.res hx hle).toAlgebra
    IsLocalization.Away a (wtZero i W) := by
  letI := ((rs hle).restrict (wtZero i V) (wtZero i W) fun _ hx => IsWt.res hx hle).toAlgebra
  refine IsLocalization.Away.mk a ?_ (fun z => ?_) fun x y hxy => ?_
  · have hu : IsUnit (rs hle a.1) := by
      subst e
      exact RingedSpace.isUnit_res_basicOpen G.left.toRingedSpace a.1
    obtain ⟨u, hu⟩ := hu
    have h1 : IsWt i W u.val 0 := hu ▸ IsWt.res a.2 hle
    have h2 : IsWt i W (u⁻¹).val 0 := by simpa using h1.inv
    exact IsUnit.of_mul_eq_one (⟨_, h2⟩ : wtZero i W) (Subtype.ext (by
      change rs hle a.1 * (u⁻¹).val = 1
      rw [← hu, Units.mul_inv]))
  · obtain ⟨n, y, hy⟩ := exists_eq_pow_mul hV hle a.1 z.1 e
    obtain ⟨x, hx, hx'⟩ := h.exists_lift h' (rs hle) (fun _ _ hx => hx.res hle) y (χ := 0)
      (hy ▸ mul_mem (pow_mem (show rs hle a.1 ∈ wtZero i W from IsWt.res a.2 hle) n) z.2)
    refine ⟨n, ⟨x, hx⟩, Subtype.ext ?_⟩
    change z.1 * rs hle a.1 ^ n = rs hle x
    rw [hx', hy, mul_comm]
  · obtain ⟨n, hn⟩ := exists_pow_mul_eq_zero hV hle a.1 (x.1 - y.1) e (by
      rw [map_sub, sub_eq_zero]; exact congrArg Subtype.val hxy)
    rw [mul_sub, sub_eq_zero] at hn
    exact ⟨n, Subtype.ext hn⟩

theorem isWt_appLE_of_invariant {Y : Scheme.{0}} (r : G.left ⟶ Y)
    (hr : ∀ (Z : Over S) (t : Z ⟶ splitTorus S X) (g : Z ⟶ G), ((t ≫ i) * g).left ≫ r = g.left ≫ r)
    (U : Y.Opens) (h : V ≤ r ⁻¹ᵁ U) (c : Γ(Y, U)) : IsWt i V ((r.appLE U V h).hom c) 0 := fun Z t g h₁ h₂ => by
  rw [← chV_val, chV_zero, Units.val_one, _root_.one_mul, ← CommRingCat.comp_apply, ← CommRingCat.comp_apply,
    Scheme.Hom.appLE_comp_appLE, Scheme.Hom.appLE_comp_appLE]
  simp only [hr Z t g]

theorem act_comp_q (Q : TQ G X) {Z : Over S} (t : Z ⟶ splitTorus S X) (g : Z ⟶ G) :
    ((t ≫ Q.i) * g) ≫ Q.q = g ≫ Q.q := by
  have := Q.q_hom
  rw [MonObj.mul_comp, Category.assoc, Q.isKernel.w, ← Hom.one_def, MonObj.comp_one, _root_.one_mul]

theorem isWt_appLE_of_isGrpPullback {f : S' ⟶ S} {F : G'.left ⟶ G.left} (hF : IsGrpPullback G' G f F)
    (hT : TorusCompat f F i' i) (h : V' ≤ F ⁻¹ᵁ V) (χ : X) (x : Γ(G.left, V)) (hx : IsWt i V x χ) :
    IsWt i' V' ((F.appLE V V' h).hom x) χ := fun Z t g h₁ h₂ => by
  obtain ⟨τ, hτ, hχ, e⟩ := hT
  let t₀ : Over.mk (Z.hom ≫ f) ⟶ splitTorus S X := Over.homMk (t.left ≫ τ) (by
    rw [Category.assoc, hτ, ← Category.assoc, Over.w]; rfl)
  let g₀ : Over.mk (Z.hom ≫ f) ⟶ G := Over.homMk (g.left ≫ F) (by
    rw [Category.assoc, hF.1.w, ← Category.assoc, Over.w]; rfl)
  have m : ((t₀ ≫ i) * g₀).left = ((t ≫ i') * g).left ≫ F := hF.2 Z (t ≫ i') g _ _
    ((Category.assoc _ _ _).trans ((congrArg (t.left ≫ ·) e).trans (Category.assoc _ _ _).symm)) rfl
  have k := hx _ t₀ g₀ (by rw [m]; exact h₁.trans (Scheme.Hom.preimage_mono _ h))
    (h₂.trans (Scheme.Hom.preimage_mono _ h))
  simp only [m] at k
  rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply (F.appLE V V' h), Scheme.Hom.appLE_comp_appLE,
    Scheme.Hom.appLE_comp_appLE, ← hχ]
  exact k

def unitWts (i : splitTorus S X ⟶ G) (V : G.left.Opens) : AddSubgroup X where
  carrier := {χ | ∃ u : Γ(G.left, V)ˣ, IsWt i V u.val χ}
  add_mem' := fun ⟨u, hu⟩ ⟨v, hv⟩ => ⟨u * v, hu.mul hv⟩
  zero_mem' := ⟨1, isWt_one⟩
  neg_mem' := fun ⟨u, hu⟩ => ⟨u⁻¹, hu.inv⟩

theorem unitWts_mono {W : G.left.Opens} (h : W ≤ V) : unitWts i V ≤ unitWts i W :=
  fun _ ⟨u, hu⟩ => ⟨Units.map (rs h).toMonoidHom u, hu.res h⟩

theorem exists_units_hom [Module.Free ℤ X] (h : ∀ χ, χ ∈ unitWts i V) :
    ∃ u : Multiplicative X →* Γ(G.left, V)ˣ, ∀ χ, IsWt i V (u (Multiplicative.ofAdd χ)).val χ := by
  choose v hv using h
  let b := Module.Free.chooseBasis ℤ X
  let l : X →ₗ[ℤ] Additive Γ(G.left, V)ˣ := b.constr ℤ fun k => Additive.ofMul (v (b k))
  refine ⟨AddMonoidHom.toMultiplicativeLeft l.toAddMonoidHom, fun χ => ?_⟩
  change IsWt i V (l χ).toMul.val χ
  let H : AddSubgroup X :=
    { carrier := {χ | IsWt i V (l χ).toMul.val χ}
      add_mem' := fun {a b} ha hb => by
        change IsWt i V (l (a + b)).toMul.val _
        rw [map_add]; exact IsWt.mul ha hb
      zero_mem' := by
        change IsWt i V (l 0).toMul.val _
        rw [map_zero]; exact isWt_one
      neg_mem' := fun {a} ha => by
        change IsWt i V (l (-a)).toMul.val _
        rw [map_neg]; exact IsWt.inv ha }
  have : Submodule.span ℤ (Set.range b) ≤ H.toIntSubmodule := Submodule.span_le.2 (by
    rintro _ ⟨k, rfl⟩
    change IsWt i V (l (b k)).toMul.val _
    rw [Module.Basis.constr_basis]; exact hv _)
  exact this (b.span_eq ▸ Submodule.mem_top)

theorem exists_affine_unitWts [Module.Finite ℤ X] (Q : TQ G X) (b : Q.B.left) :
    ∃ U : Q.B.left.Opens, (IsAffineOpen U ∧ ∀ χ, χ ∈ unitWts Q.i (Q.q.left ⁻¹ᵁ U)) ∧ b ∈ U := by
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := ℤ) (M := X)
  choose V hb hV using Q.loc b
  have hb' : b ∈ s.inf V := by
    refine Finset.inf_induction (p := fun O : Q.B.left.Opens => b ∈ O) trivial (fun _ h _ h' => ⟨h, h'⟩) fun χ _ => hb χ
  obtain ⟨_, ⟨U, hU, rfl⟩, hbU, hle⟩ :=
    Q.B.left.isBasis_affineOpens.exists_subset_of_mem_open hb' (s.inf V).isOpen
  refine ⟨U, ⟨hU, fun χ => ?_⟩, hbU⟩
  have : Submodule.span ℤ (s : Set X) ≤ (unitWts Q.i (Q.q.left ⁻¹ᵁ U)).toIntSubmodule := Submodule.span_le.2
    fun χ hχ => unitWts_mono (Q.q.left.preimage_mono ((show U ≤ s.inf V from hle).trans (Finset.inf_le hχ))) (hV χ)
  exact this (hs ▸ Submodule.mem_top)

end Weights

theorem surjective_and_ker {A : Type} [CommRing A] {J : Ideal A} {Y Z : Scheme.{0}}
    {f : Y ⟶ Spec (CommRingCat.of A)} {i : Z ⟶ Y} {f' : Z ⟶ Spec (CommRingCat.of (A ⧸ J))}
    (h : IsPullback i f' f (red J)) {U : Y.Opens} (hU : IsAffineOpen U) {U' : Z.Opens} (e : i ⁻¹ᵁ U = U') :
    Function.Surjective (i.appLE U U' e.ge).hom ∧ RingHom.ker (i.appLE U U' e.ge).hom = J.map (baseMap f U) := by
  subst e
  have : IsClosedImmersion i := MorphismProperty.of_isPullback h.flip inferInstance
  rw [Scheme.Hom.appLE_eq_app]
  refine ⟨i.app_surjective U hU, ?_⟩
  have hpo := (isIso_pushoutSection_iff h (US := ⊤) (UT := ⊤) (UX := U) (UY := i ⁻¹ᵁ U) le_top
    le_top (by simp)).1 (isIso_pushoutSection_of_isAffineOpen h _ _ _ (isAffineOpen_top _)
      (isAffineOpen_top _) hU)
  have hpo' : IsPushout ((Scheme.ΓSpecIso (.of A)).inv ≫ f.appLE ⊤ U le_top)
      (CommRingCat.ofHom (Ideal.Quotient.mk J)) (i.app U)
      ((Scheme.ΓSpecIso (.of (A ⧸ J))).inv ≫ f'.appLE ⊤ (i ⁻¹ᵁ U) le_top) := by
    refine hpo.of_iso (Scheme.ΓSpecIso _) (Iso.refl _) (Scheme.ΓSpecIso _) (Iso.refl _)
      (by simp) ?_ (by simp [Scheme.Hom.appLE_eq_app]) (by simp)
    rw [← Scheme.ΓSpecIso_naturality]
    congr 1
  rw [PrimeSection.ker_eq_map_of_isPushout hpo' Ideal.Quotient.mk_surjective]
  exact congrArg (Ideal.map _) Ideal.mk_ker

theorem isAffineOpen_of_preimage {A : Type} [CommRing A] {J : Ideal A} (hJ : IsNilpotent J) {Y Z : Scheme.{0}}
    {f : Y ⟶ Spec (CommRingCat.of A)} {i : Z ⟶ Y} {f' : Z ⟶ Spec (CommRingCat.of (A ⧸ J))}
    (h : IsPullback i f' f (red J)) {U : Y.Opens} (hU : IsAffineOpen (i ⁻¹ᵁ U)) : IsAffineOpen U :=
  isAffine_of_isPullback_of_isNilpotent J hJ _ Ideal.Quotient.mk_surjective Ideal.mk_ker
    ((isPullback_morphismRestrict i U).paste_vert h) hU

theorem exists_quotient_scheme : (∀ (A : Type) [CommRing A] (J : Ideal A), IsNilpotent J → ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (G : Over (Spec (CommRingCat.of A))) [GrpObj G] [IsCommMonObj G] (G₀ : Over (Spec (CommRingCat.of (A ⧸ J)))) [GrpObj G₀] (F : G₀.left ⟶ G.left), IsGrpPullback G₀ G (red J) F → ∀ (Q₀ : TQ G₀ X) (i : splitTorus _ X ⟶ G), IsMonHom i → TorusCompat (red J) F Q₀.i i → ∃ (B : Over (Spec (CommRingCat.of A))) (q : G ⟶ B) (j : Q₀.B.left ⟶ B.left), IsPullback j Q₀.B.hom B.hom (red J) ∧ Q₀.q.left ≫ j = F ≫ q.left ∧ IsAffineHom q.left ∧ ∀ b : B.left, ∃ V : B.left.Opens, b ∈ V ∧ IsAffineOpen V ∧ (∀ a : Γ(G.left, q.left ⁻¹ᵁ V), IsWt i _ a 0 ↔ ∃ c, (q.left.app V).hom c = a) ∧ Function.Injective (q.left.app V).hom ∧ (snd (splitTorus _ X) G).left ⁻¹ᵁ (q.left ⁻¹ᵁ V) ≤ ((fst (splitTorus _ X) G ≫ i) * snd _ G).left ⁻¹ᵁ (q.left ⁻¹ᵁ V) ∧ ∃ u : Multiplicative X →* Γ(G.left, q.left ⁻¹ᵁ V)ˣ, ∀ χ, IsWt i _ (u (Multiplicative.ofAdd χ)).val χ) := by
  intro A _ J hJ X _ _ _ G _ _ G₀ _ F hF Q₀ i hi hT
  have : IsClosedImmersion F := MorphismProperty.of_isPullback hF.1.flip inferInstance
  have : Surjective F := MorphismProperty.of_isPullback hF.1.flip (surjective_red hJ)
  have := Q₀.q_affine
  have hd := invariant_functions_descend _ G₀ Q₀.B _ Q₀.q Q₀.i Q₀.q_hom Q₀.i_hom Q₀.q_flat Q₀.q_surj inferInstance
    Q₀.isKernel
  have st₀ : ∀ U : Q₀.B.left.Opens, (snd (splitTorus _ X) G₀).left ⁻¹ᵁ (Q₀.q.left ⁻¹ᵁ U) ≤
      ((fst (splitTorus _ X) G₀ ≫ Q₀.i) * snd _ G₀).left ⁻¹ᵁ (Q₀.q.left ⁻¹ᵁ U) := fun U => by
    rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, ← Over.comp_left, ← Over.comp_left, act_comp_q]
  have st : ∀ (U : Q₀.B.left.Opens) (V : G.left.Opens), F ⁻¹ᵁ V = Q₀.q.left ⁻¹ᵁ U →
      (snd (splitTorus _ X) G).left ⁻¹ᵁ V ≤ ((fst (splitTorus _ X) G ≫ i) * snd _ G).left ⁻¹ᵁ V := fun U V e =>
    torus_stable_of_red A J hJ X G G₀ F hF Q₀.i i hT V (e ▸ st₀ U)
  have aff : ∀ (U : Q₀.B.left.Opens), IsAffineOpen U → ∀ V : G.left.Opens, F ⁻¹ᵁ V = Q₀.q.left ⁻¹ᵁ U →
      IsAffineOpen V := fun U hU V e => isAffineOpen_of_preimage hJ hF.1 (e ▸ hU.preimage Q₀.q.left)
  have gr : ∀ (U : Q₀.B.left.Opens), IsAffineOpen U → ∀ V : G.left.Opens, F ⁻¹ᵁ V = Q₀.q.left ⁻¹ᵁ U →
      Graded i V := fun U hU V e => functions_graded_by_weights _ G X i hi V (aff U hU V e) (st U V e)
  have lft : ∀ (U : Q₀.B.left.Opens), IsAffineOpen U → ∀ (V : G.left.Opens) (e : F ⁻¹ᵁ V = Q₀.q.left ⁻¹ᵁ U) (χ : X)
      (y : Γ(G₀.left, Q₀.q.left ⁻¹ᵁ U)), IsWt Q₀.i _ y χ → ∃ x, IsWt i V x χ ∧ (F.appLE V _ e.ge).hom x = y := by
    intro U hU V e χ y hy
    obtain ⟨u, rfl⟩ := (surjective_and_ker hF.1 (aff U hU V e) e).1 y
    exact (gr U hU V e).exists_lift (functions_graded_by_weights _ G₀ X Q₀.i Q₀.i_hom _ (hU.preimage _) (st₀ U)) _
      (isWt_appLE_of_isGrpPullback hF hT e.ge) u hy
  obtain ⟨B, s, q, j, hqs, hj, hsq, H⟩ := exists_quotient hJ G.hom F Q₀.B.hom Q₀.q.left
    (by rw [hF.1.w, ← Category.assoc, Over.w]) (wtZero i) (fun V V' h a ha => IsWt.res ha h)
    (fun V c => isWt_appLE_of_invariant G.hom (fun Z t g => by rw [Over.w, Over.w]) ⊤ le_top c)
    (fun U => (hd U).1)
    (fun U V e a ha => (hd U).2.2 _ fun Z t g h₁ h₂ => by
      rw [isWt_appLE_of_isGrpPullback hF hT e.ge 0 a ha Z t g h₁ h₂, ← chV_val, chV_zero, Units.val_one,
        _root_.one_mul])
    {U | IsAffineOpen U ∧ ∀ χ, χ ∈ unitWts Q₀.i (Q₀.q.left ⁻¹ᵁ U)} (fun U hU => hU.1)
    (fun U hU f => ⟨hU.1.basicOpen f, fun χ =>
      unitWts_mono (Q₀.q.left.preimage_mono (Q₀.B.left.basicOpen_le f)) (hU.2 χ)⟩)
    (exists_affine_unitWts Q₀)
    (fun U hU V e c => lft U hU.1 V e 0 _ (by
      rw [Scheme.Hom.app_eq_appLE]
      exact isWt_appLE_of_invariant Q₀.q.left (fun Z t g => congrArg (·.left) (act_comp_q Q₀ t g)) U le_rfl c))
    (fun U hU V e a ha => (gr U hU.1 V e).mem_map J _ a
      ((surjective_and_ker hF.1 (aff U hU.1 V e) e).2.le ha))
    (fun U hU V e a V' h e' => (gr U hU.1 V e).isLocalization (aff U hU.1 V e) a V' h e' (by
      obtain ⟨c, hc⟩ := (hd U).2.2 ((F.appLE V _ e.ge).hom a.1) fun Z t g h₁ h₂ => by
        rw [isWt_appLE_of_isGrpPullback hF hT e.ge 0 a.1 a.2 Z t g h₁ h₂, ← chV_val, chV_zero, Units.val_one,
          _root_.one_mul]
      refine gr _ (hU.1.basicOpen c) V' ?_
      rw [e', Scheme.preimage_basicOpen Q₀.q.left, hc, Scheme.basicOpen_appLE, eq_comm, inf_eq_right, ← e]
      exact F.preimage_mono (G.left.basicOpen_le _)))
  have hp : ∀ V : B.Opens, F ⁻¹ᵁ q ⁻¹ᵁ V = Q₀.q.left ⁻¹ᵁ j ⁻¹ᵁ V := fun V => by
    rw [← Scheme.Hom.comp_preimage, ← hsq, Scheme.Hom.comp_preimage]
  refine ⟨Over.mk s, Over.homMk q hqs, j, hj, hsq, isAffineHom_of_forall_exists_isAffineOpen q fun b => ?_,
    fun b => ?_⟩
  · obtain ⟨V, hb, hU, hV, -⟩ := H b
    exact ⟨V, hb, hV, aff _ hU.1 _ (hp V)⟩
  · obtain ⟨V, hb, hU, hV, h₁, h₂⟩ := H b
    refine ⟨V, hb, hV, h₂, h₁, st _ _ (hp V), exists_units_hom (V := q ⁻¹ᵁ V) fun χ => ?_⟩
    obtain ⟨u, hu⟩ := hU.2 χ
    obtain ⟨x, hx, e⟩ := lft _ hU.1 _ (hp V) χ _ hu
    obtain ⟨hs, hk⟩ := surjective_and_ker hF.1 (aff _ hU.1 _ (hp V)) (hp V)
    obtain ⟨y, hy⟩ := hs (u⁻¹).val
    have h1 : x * y - 1 ∈ J.map (baseMap G.hom (q ⁻¹ᵁ V)) := by
      rw [← hk, RingHom.mem_ker, map_sub, map_mul, e, hy, Units.mul_inv, map_one, sub_self]
    obtain ⟨n, hn⟩ := hJ
    have h2 : IsNilpotent (x * y - 1) := ⟨n, by
      have := Ideal.pow_mem_pow h1 n
      rw [← Ideal.map_pow, hn] at this
      simpa using this⟩
    have h3 : IsUnit (x * y) := by simpa using h2.isUnit_add_one
    obtain ⟨v, rfl⟩ := isUnit_of_mul_isUnit_left h3
    exact ⟨v, hx⟩

end GlobalTheory.TorusQuotientLift
end
