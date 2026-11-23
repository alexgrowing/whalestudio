import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSectionOfChg
import Formalism.LocalToGlobal.ProjectiveLattices.SatLeaves

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.HermitianCompactForm GlobalTheory.Toroidal GlobalTheory.ShFam
  GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.DetLine

namespace GlobalTheory.DetLine.FromGeneric

section Points

variable {X : Scheme.{0}} {A R : Type} [CommRing A] [CommRing R]

theorem exists_lift (x : Sp A ⟶ X) [IsOpenImmersion x] (z : Sp R ⟶ X) (h : Set.range z ⊆ Set.range x) :
    ∃ m : A →+* R, z = spMap m ≫ x := by
  obtain ⟨m, hm⟩ := Spec.map_surjective (IsOpenImmersion.lift x z h)
  exact ⟨m.hom, (IsOpenImmersion.lift_fac x z h).symm.trans (congrArg (· ≫ x) hm.symm)⟩

theorem lift_unique (x : Sp A ⟶ X) [Mono x] {m m' : A →+* R} (h : spMap m ≫ x = spMap m' ≫ x) : m = m' :=
  congrArg CommRingCat.Hom.hom (Spec.map_injective ((cancel_mono x).1 h))

theorem range_subset [IsLocalRing R] (z : Sp R ⟶ X) {U : Set X} (hU : IsOpen U)
    (h : z (IsLocalRing.closedPoint R) ∈ U) : Set.range z ⊆ U := by
  rintro _ ⟨a, rfl⟩
  exact ((IsLocalRing.specializes_closedPoint a).map z.continuous).mem_open hU h

theorem locPt_closedPoint (y : X) : locPt X y (IsLocalRing.closedPoint (X.presheaf.stalk y)) = y :=
  Scheme.fromSpecStalk_closedPoint

theorem locPt_comp_closedPoint {Z : Scheme.{0}} (f : X ⟶ Z) (y : X) :
    (locPt X y ≫ f) (IsLocalRing.closedPoint (X.presheaf.stalk y)) = f y :=
  (Scheme.Hom.comp_apply _ _ _).trans (congrArg f (locPt_closedPoint y))

theorem exists_locPt [IsLocalRing R] (z : Sp R ⟶ X) :
    ∃ m : X.presheaf.stalk (z (IsLocalRing.closedPoint R)) →+* R, z = spMap m ≫ locPt X _ :=
  ⟨(Scheme.stalkClosedPointTo (R := CommRingCat.of R) z).hom,
    (Scheme.Spec_stalkClosedPointTo_fromSpecStalk (R := CommRingCat.of R) z).symm⟩

theorem genPt_eq [IsIntegral X] (y : X) :
    genPt X = spMap (algebraMap (X.presheaf.stalk y) X.functionField) ≫ locPt X y :=
  (Scheme.SpecMap_stalkSpecializes_fromSpecStalk ((genericPoint_spec X).specializes trivial)).symm

theorem exists_spread (y : X) {U : Set X} (hU : IsOpen U) (hy : y ∈ U) {β : X.presheaf.stalk y} (hβ : IsUnit β) :
    ∃ (A : Type) (_ : CommRing A) (x : Sp A ⟶ X) (m : A →+* X.presheaf.stalk y) (α : A),
      IsOpenImmersion x ∧ Set.range x ⊆ U ∧ locPt X y = spMap m ≫ x ∧ IsUnit α ∧ m α = β := by
  obtain ⟨W, hW, a, rfl⟩ := X.presheaf.exists_germ_eq β
  have hb : y ∈ X.basicOpen a := (X.mem_basicOpen a y hW).2 hβ
  obtain ⟨_, ⟨W', hW' : IsAffineOpen W', rfl⟩, hyW', hle⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
    (show y ∈ U ∩ X.basicOpen a from ⟨hy, hb⟩) (hU.inter (X.basicOpen a).isOpen)
  have h1 : W' ≤ X.basicOpen a := fun z hz => (hle hz).2
  refine ⟨Γ(X, W'), inferInstance, hW'.fromSpec, (X.presheaf.germ W' y hyW').hom,
    X.presheaf.map (homOfLE (h1.trans (X.basicOpen_le a))).op a, inferInstanceAs (IsOpenImmersion hW'.fromSpec), ?_,
    (hW'.fromSpecStalk_eq_fromSpecStalk hyW').symm, ?_, X.presheaf.germ_res_apply _ _ _ _⟩
  · intro z hz
    rw [show Set.range _ = _ from hW'.range_fromSpec] at hz
    exact (hle hz).1
  · have := (X.toRingedSpace.isUnit_res_basicOpen a).map (X.presheaf.map (homOfLE h1).op).hom
    convert this using 1
    exact ConcreteCategory.congr_hom (X.presheaf.map_comp (homOfLE (X.basicOpen_le a)).op (homOfLE h1).op) a

end Points

section Glue

variable {X Y : Scheme.{0}} [IsIntegral Y] {io : Y ⟶ X} {Fr : ∀ (R : Type) [CommRing R], Type}
  (pt : ∀ (R : Type) [CommRing R], Fr R → (Sp R ⟶ X))
  (d : ∀ (R R' : Type) [CommRing R] [CommRing R'], (R →+* R') → Fr R → Fr R' → R')
  (a₀ : Fr Y.functionField) (δ : Y.functionField)

def IsTest {A : Type} [CommRing A] (b : Fr A) (α : A) : Prop :=
  IsOpenImmersion (pt _ b) ∧ IsUnit α ∧ ∃ k : A →+* Y.functionField, pt _ a₀ = spMap k ≫ pt _ b ∧ d _ _ k b a₀ * k α = δ

def IsVal {R R' : Type} [CommRing R] [CommRing R'] (g : R →+* R') (a : Fr R) (r : R') : Prop :=
  ∀ (L : Type) [CommRing L] [IsLocalRing L] (g' : R' →+* L) (e : Fr L) (A : Type) [CommRing A] (b : Fr A) (α : A)
    (h : A →+* L), IsTest pt d a₀ δ b α → pt _ e = spMap (g'.comp g) ≫ pt _ a → pt _ e = spMap h ≫ pt _ b →
    d _ _ (g'.comp g) a e * g' r = d _ _ h b e * h α

variable {pt d a₀ δ}

theorem IsVal.map {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] {g : R →+* R'} {a : Fr R} {r : R'}
    (h : IsVal pt d a₀ δ g a r) (g' : R' →+* R'') : IsVal pt d a₀ δ (g'.comp g) a (g' r) :=
  fun L _ _ g'' e A _ b α k hb h1 h2 => h L (g''.comp g') e A b α k hb h1 h2

variable [IsOpenImmersion io]
  (hrange : ∀ (R : Type) [CommRing R] (a : Fr R), Set.range (pt _ a) ⊆ Set.range io)
  (hpull : ∀ (R R' : Type) [CommRing R] [CommRing R'] (g : R →+* R') (a : Fr R), ∃ a' : Fr R', pt _ a' = spMap g ≫ pt _ a)
  (hunit : ∀ (R R' : Type) [CommRing R] [CommRing R'] (g : R →+* R') (a : Fr R) (a' : Fr R'),
    pt _ a' = spMap g ≫ pt _ a → IsUnit (d _ _ g a a'))
  (hcoc : ∀ (R R' R'' : Type) [CommRing R] [CommRing R'] [CommRing R''] (g : R →+* R') (g' : R' →+* R'') (a : Fr R)
    (a' : Fr R') (a'' : Fr R''), pt _ a' = spMap g ≫ pt _ a → pt _ a'' = spMap g' ≫ pt _ a' →
    d _ _ (g'.comp g) a a'' = d _ _ g' a' a'' * g' (d _ _ g a a'))
  (h₀ : pt _ a₀ = genPt Y ≫ io)
  (hcov : ∀ z ∈ Set.range io, ∃ (A : Type) (_ : CommRing A) (b : Fr A), IsOpenImmersion (pt _ b) ∧ z ∈ Set.range (pt _ b))
  (hδ : ∀ y : Y, ∃ (b : Fr (Y.presheaf.stalk y)) (u : Y.presheaf.stalk y), IsUnit u ∧ pt _ b = locPt Y y ≫ io ∧
    d _ _ (algebraMap _ Y.functionField) b a₀ * algebraMap _ Y.functionField u = δ)

include hpull hunit hcoc h₀ hcov hδ in

theorem exists_test (y : Y) :
    ∃ (A : Type) (_ : CommRing A) (b : Fr A) (α : A), IsTest pt d a₀ δ b α ∧ io y ∈ Set.range (pt _ b) := by
  obtain ⟨B, _, bW, hW, hyW⟩ := hcov (io y) ⟨y, rfl⟩
  obtain ⟨e, u, hu, he, hd⟩ := hδ y
  have hop : IsOpen (Set.range (pt _ bW)) := (pt _ bW).isOpenEmbedding.isOpen_range
  obtain ⟨m, hm⟩ := exists_lift (pt _ bW) (pt _ e) (range_subset _ hop (by
    rw [he, locPt_comp_closedPoint]; exact hyW))
  obtain ⟨β, hβ⟩ := hunit _ _ m bW e hm
  obtain ⟨A, _, x, m', α, hx, hxU, hm', hα, hαβ⟩ := exists_spread y (hop.preimage io.continuous) hyW
    ((β⁻¹).isUnit.mul hu)
  obtain ⟨n, hn⟩ := exists_lift (pt _ bW) (x ≫ io) (by
    rintro _ ⟨z, rfl⟩
    rw [Scheme.Hom.comp_apply]
    exact hxU ⟨z, rfl⟩)
  obtain ⟨b, hb⟩ := hpull _ _ n bW
  have hb' : pt _ b = x ≫ io := hb.trans hn.symm
  have heb : pt _ e = spMap m' ≫ pt _ b := by rw [he, hb', hm', Category.assoc]
  have h0e : pt _ a₀ = spMap (algebraMap _ Y.functionField) ≫ pt _ e := by rw [h₀, he, genPt_eq y, Category.assoc]
  obtain rfl : m = m'.comp n := lift_unique (pt _ bW) (by rw [← hm, heb, hb, DetExtendZero.spMap_comp, Category.assoc])
  refine ⟨A, inferInstance, b, d _ _ n bW b * α, ⟨by rw [hb']; infer_instance, (hunit _ _ _ _ _ hb).mul hα,
    (algebraMap _ Y.functionField).comp m', by rw [h0e, heb, DetExtendZero.spMap_comp, Category.assoc], ?_⟩, ?_⟩
  · rw [hcoc _ _ _ _ _ _ _ _ heb h0e, RingHom.comp_apply, _root_.mul_assoc, ← map_mul, map_mul m', ← _root_.mul_assoc,
      ← hcoc _ _ _ _ _ _ _ _ hb heb, ← hβ, hαβ, Units.mul_inv_cancel_left, hd]
  · refine ⟨spMap m' (IsLocalRing.closedPoint _), ?_⟩
    refine (Scheme.Hom.comp_apply _ _ _).symm.trans ?_
    rw [← heb, he]
    exact locPt_comp_closedPoint io y

include hrange hpull hunit hcoc h₀ in

theorem test_compat {L : Type} [CommRing L] [IsLocalRing L] (e : Fr L) {A A' : Type} [CommRing A] [CommRing A']
    {b : Fr A} {b' : Fr A'} {α : A} {α' : A'} (hb : IsTest pt d a₀ δ b α) (hb' : IsTest pt d a₀ δ b' α')
    {h : A →+* L} {h' : A' →+* L} (he : pt _ e = spMap h ≫ pt _ b) (he' : pt _ e = spMap h' ≫ pt _ b') :
    d _ _ h b e * h α = d _ _ h' b' e * h' α' := by
  let z : Sp L ⟶ Y := IsOpenImmersion.lift io (pt _ e) (hrange _ e)
  have hz : z ≫ io = pt _ e := IsOpenImmersion.lift_fac _ _ _
  obtain ⟨n, hn⟩ := exists_locPt z
  generalize hy : z (IsLocalRing.closedPoint L) = y at n hn
  have hlift : ∀ {B : Type} [CommRing B] (f : Fr B) (k : B →+* L), IsOpenImmersion (pt _ f) → pt _ e = spMap k ≫ pt _ f →
      ∃ m : B →+* Y.presheaf.stalk y, locPt Y y ≫ io = spMap m ≫ pt _ f ∧ k = n.comp m := by
    intro B _ f k hf hk
    obtain ⟨m, hm⟩ := exists_lift (pt _ f) (locPt Y y ≫ io) (range_subset _ (pt _ f).isOpenEmbedding.isOpen_range (by
      have h1 : (z ≫ io) (IsLocalRing.closedPoint L) = io y := (Scheme.Hom.comp_apply _ _ _).trans (congrArg io hy)
      rw [locPt_comp_closedPoint, ← h1, hz, hk]
      exact ⟨_, (Scheme.Hom.comp_apply _ _ _).symm⟩))
    exact ⟨m, hm, lift_unique (pt _ f) (by rw [← hk, ← hz, hn, DetExtendZero.spMap_comp, Category.assoc, Category.assoc, hm])⟩
  obtain ⟨m, hm, rfl⟩ := hlift b h hb.1 he
  obtain ⟨m', hm', rfl⟩ := hlift b' h' hb'.1 he'
  obtain ⟨f, hf⟩ := hpull _ _ m b
  have hf' : pt _ f = spMap m' ≫ pt _ b' := by rw [hf, ← hm, hm']
  have hef : pt _ e = spMap n ≫ pt _ f := by rw [hf, ← hm, ← hz, hn, Category.assoc]
  have h0f : pt _ a₀ = spMap (algebraMap _ Y.functionField) ≫ pt _ f := by rw [h₀, hf, ← hm, genPt_eq y, Category.assoc]
  have key : ∀ {B : Type} [CommRing B] (c : Fr B) (ω : B) (k : B →+* Y.presheaf.stalk y), IsTest pt d a₀ δ c ω →
      pt _ f = spMap k ≫ pt _ c →
      d _ _ (algebraMap _ Y.functionField) f a₀ * algebraMap _ Y.functionField (d _ _ k c f * k ω) = δ := by
    intro B _ c ω k hc hk
    obtain ⟨hc1, -, k', hk', hd⟩ := hc
    obtain rfl : k' = (algebraMap _ Y.functionField).comp k :=
      lift_unique (pt _ c) (by rw [← hk', h0f, hk, DetExtendZero.spMap_comp, Category.assoc])
    rw [map_mul, ← _root_.mul_assoc, ← hcoc _ _ _ _ _ _ _ _ hk h0f]
    exact hd
  have e1 := IsFractionRing.injective (Y.presheaf.stalk y) Y.functionField
    ((hunit _ _ _ _ _ h0f).mul_left_cancel ((key b α m hb hf).trans (key b' α' m' hb' hf').symm))
  rw [hcoc _ _ _ _ _ _ _ _ hf hef, hcoc _ _ _ _ _ _ _ _ hf' hef, RingHom.comp_apply, RingHom.comp_apply,
    _root_.mul_assoc, _root_.mul_assoc, ← map_mul, ← map_mul, e1]

include hrange hpull hunit hcoc h₀ in

theorem exists_val_of_test {R R' A : Type} [CommRing R] [CommRing R'] [CommRing A] (g : R →+* R') (a : Fr R)
    {b : Fr A} {α : A} (hb : IsTest pt d a₀ δ b α) {h : A →+* R'} (hh : spMap g ≫ pt _ a = spMap h ≫ pt _ b) :
    ∃ r, IsVal pt d a₀ δ g a r := by
  obtain ⟨a', ha'⟩ := hpull _ _ g a
  obtain ⟨β, hβ⟩ := hunit _ _ g a a' ha'
  refine ⟨β⁻¹ * (d _ _ h b a' * h α), fun L _ _ g' e A' _ b' α' h' hb' h1 h2 => ?_⟩
  have h3 : pt _ e = spMap g' ≫ pt _ a' := by rw [h1, ha', DetExtendZero.spMap_comp, Category.assoc]
  have h4 := ha'.trans hh
  rw [hcoc _ _ _ _ _ _ _ _ ha' h3, _root_.mul_assoc, ← map_mul, ← hβ, Units.mul_inv_cancel_left, map_mul,
    ← _root_.mul_assoc, ← hcoc _ _ _ _ _ _ _ _ h4 h3]
  exact test_compat hrange hpull hunit hcoc h₀ e hb hb' (by rw [h3, h4, DetExtendZero.spMap_comp, Category.assoc]) h2

include hrange hpull hunit hcoc h₀ hcov hδ in

theorem exists_local {R L : Type} [CommRing R] [CommRing L] [IsLocalRing L] (g : R →+* L) (a : Fr R) :
    ∃ (e : Fr L) (A : Type) (_ : CommRing A) (b : Fr A) (α : A) (h : A →+* L),
      IsTest pt d a₀ δ b α ∧ pt _ e = spMap g ≫ pt _ a ∧ pt _ e = spMap h ≫ pt _ b := by
  obtain ⟨e, he⟩ := hpull _ _ g a
  obtain ⟨y, hy⟩ := hrange _ e ⟨IsLocalRing.closedPoint L, rfl⟩
  obtain ⟨A, _, b, α, hb, hyb⟩ := exists_test hpull hunit hcoc h₀ hcov hδ y
  have := hb.1
  obtain ⟨h, hh⟩ := exists_lift (pt _ b) (pt _ e) (range_subset _ (pt _ b).isOpenEmbedding.isOpen_range (hy ▸ hyb))
  exact ⟨e, A, _, b, α, h, hb, he, hh⟩

include hrange hpull hunit hcoc h₀ hcov hδ in
theorem IsVal.unique {R R' : Type} [CommRing R] [CommRing R'] {g : R →+* R'} {a : Fr R} {r r' : R'}
    (h : IsVal pt d a₀ δ g a r) (h' : IsVal pt d a₀ δ g a r') : r = r' := by
  refine sub_eq_zero.1 (eq_zero_of_localization _ fun P _ => ?_)
  rw [map_sub, sub_eq_zero]
  obtain ⟨e, A, _, b, α, k, hb, h1, h2⟩ := exists_local hrange hpull hunit hcoc h₀ hcov hδ
    ((algebraMap R' (Localization.AtPrime P)).comp g) a
  exact (hunit _ _ _ _ _ h1).mul_left_cancel ((h _ _ e A b α k hb h1 h2).trans (h' _ _ e A b α k hb h1 h2).symm)

include hrange hpull hunit hcoc h₀ hcov hδ in
theorem IsVal.isUnit {R R' : Type} [CommRing R] [CommRing R'] {g : R →+* R'} {a : Fr R} {r : R'}
    (h : IsVal pt d a₀ δ g a r) : IsUnit r := by
  by_contra hn
  obtain ⟨P, hP, hr⟩ := exists_max_ideal_of_mem_nonunits hn
  obtain ⟨e, A, _, b, α, k, hb, h1, h2⟩ := exists_local hrange hpull hunit hcoc h₀ hcov hδ
    ((algebraMap R' (Localization.AtPrime P)).comp g) a
  have h3 : IsUnit (d _ _ _ a e * algebraMap R' (Localization.AtPrime P) r) :=
    h _ _ e A b α k hb h1 h2 ▸ (hunit _ _ _ _ _ h2).mul (hb.2.1.map k)
  exact (IsLocalization.AtPrime.isUnit_to_map_iff (Localization.AtPrime P) P r).1 (isUnit_of_mul_isUnit_right h3) hr

include hrange hpull hunit hcoc h₀ hcov hδ in

theorem exists_val {R : Type} [CommRing R] (a : Fr R) : ∃ r, IsVal pt d a₀ δ (RingHom.id R) a r := by
  let s : Set R := {f | ∃ r, IsVal pt d a₀ δ (algebraMap R (Localization.Away f)) a r}
  have hs : ∀ P : Ideal R, P.IsPrime → ∃ f ∈ s, f ∉ P := by
    intro P hP
    let z : Sp R := (⟨P, hP⟩ : PrimeSpectrum R)
    obtain ⟨y, hy⟩ := hrange _ a ⟨z, rfl⟩
    obtain ⟨A, _, b, α, hb, hyb⟩ := exists_test hpull hunit hcoc h₀ hcov hδ y
    have := hb.1
    obtain ⟨_, ⟨f, rfl⟩, hf, hle⟩ := PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open
      (show z ∈ pt _ a ⁻¹' Set.range (pt _ b) by rw [Set.mem_preimage, ← hy]; exact hyb)
      ((pt _ b).isOpenEmbedding.isOpen_range.preimage (pt _ a).continuous)
    obtain ⟨h, hh⟩ := exists_lift (pt _ b) (spMap (algebraMap R (Localization.Away f)) ≫ pt _ a) (by
      rintro _ ⟨w, rfl⟩
      rw [Scheme.Hom.comp_apply]
      refine hle fun hw => ?_
      exact (PrimeSpectrum.isPrime (R := Localization.Away f) w).ne_top
        (Ideal.eq_top_of_isUnit_mem _ hw (IsLocalization.Away.algebraMap_isUnit f)))
    exact ⟨f, exists_val_of_test hrange hpull hunit hcoc h₀ _ a hb hh, hf⟩
  have hspan : Ideal.span s = ⊤ := by
    by_contra hn
    obtain ⟨P, hP, hle⟩ := Ideal.exists_le_maximal _ hn
    obtain ⟨f, hf, hfP⟩ := hs P hP.isPrime
    exact hfP (hle (Ideal.subset_span hf))
  choose ρ hρ using fun f : s => f.2
  obtain ⟨r, hr, -⟩ := Localization.existsUnique_algebraMap_eq_of_span_eq_top s hspan ρ fun f f' => by
    have e1 := (hρ f).map (IsLocalization.Away.awayToAwayRight (P := Localization.Away (f.1 * f'.1)) f.1 f'.1)
    have e2 := (hρ f').map (IsLocalization.Away.awayToAwayLeft (P := Localization.Away (f.1 * f'.1)) f'.1 f.1)
    refine IsVal.unique hrange hpull hunit hcoc h₀ hcov hδ e1 ?_
    convert e2 using 1
    ext x
    simp only [RingHom.comp_apply, IsLocalization.Away.awayToAwayRight_eq, IsLocalization.Away.awayToAwayLeft_eq]
  refine ⟨r, fun L _ _ g e A _ b α h hb h1 h2 => ?_⟩
  obtain ⟨f, hf, hfP⟩ := hs ((IsLocalRing.maximalIdeal L).comap g) inferInstance
  have hu : IsUnit (g f) := by
    by_contra hn
    exact hfP hn
  have hg : (IsLocalization.Away.lift (S := Localization.Away f) f hu).comp (algebraMap R _) = g.comp (RingHom.id R) :=
    IsLocalization.Away.lift_comp f hu
  have := hρ ⟨f, hf⟩ L (IsLocalization.Away.lift f hu) e A b α h hb (by rw [hg]; exact h1) h2
  rwa [hg, ← hr ⟨f, hf⟩, IsLocalization.Away.lift_eq] at this

include hrange hpull hunit hcoc h₀ hcov hδ in

theorem exists_coord : ∃ f : ∀ (R : Type) [CommRing R], Fr R → R,
    (∀ (R R' : Type) [CommRing R] [CommRing R'] (g : R →+* R') (a : Fr R) (a' : Fr R'), pt _ a' = spMap g ≫ pt _ a →
      f R' a' = d _ _ g a a' * g (f R a)) ∧ (∀ (R : Type) [CommRing R] (a : Fr R), IsUnit (f R a)) ∧ f _ a₀ = δ := by
  choose f hf using fun (R : Type) [CommRing R] (a : Fr R) => exists_val hrange hpull hunit hcoc h₀ hcov hδ a
  refine ⟨f, fun R R' _ _ g a a' ha => IsVal.unique hrange hpull hunit hcoc h₀ hcov hδ (hf R' a') ?_,
    fun R _ a => IsVal.isUnit hrange hpull hunit hcoc h₀ hcov hδ (hf R a), ?_⟩
  · intro L _ _ g' e A _ b α h hb h1 h2
    rw [RingHom.comp_id] at h1 ⊢
    rw [map_mul, ← _root_.mul_assoc, ← hcoc _ _ _ _ _ _ _ _ ha h1]
    exact hf R a L (g'.comp g) e A b α h hb (by rw [RingHom.comp_id, h1, ha, DetExtendZero.spMap_comp, Category.assoc]) h2
  · obtain ⟨A, _, b, α, hb, -⟩ := exists_test hpull hunit hcoc h₀ hcov hδ (genericPoint Y)
    obtain ⟨k, hk, hd⟩ := hb.2.2
    have hid : pt _ a₀ = spMap (RingHom.id _) ≫ pt _ a₀ := by rw [DetExtendZero.spMap_id, Category.id_comp]
    have h1 : d _ _ (RingHom.id _) a₀ a₀ = 1 := by
      have := hcoc _ _ _ _ _ _ _ _ hid hid
      exact ((hunit _ _ _ _ _ hid).mul_left_cancel ((_root_.mul_one _).trans this)).symm
    have := hf _ a₀ _ (RingHom.id _) a₀ A b α k hb hid hk
    rwa [RingHom.comp_id, h1, _root_.one_mul, hd] at this

end Glue

section Change

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Geo.Tor.Host E} {l : Level H}
  {S X : Scheme.{0}} {c : Coeff l} {t : SAB H S} {π : X ⟶ S} {s : X ⟶ Sp c.F} {V : Set X} {τ : E →+* ℂ}
  {p q : ℕ} {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R'']

theorem comb_vecMul {x : Sp R ⟶ S} {n m : ℕ} {v : Fin n → (epsAt x ⟶ t.G)}
    (hv : ∀ i, spMap (TrivSqZeroExt.fstHom R R R).toRingHom ≫ (v i).left = (1 : Over.mk x ⟶ t.G).left)
    {w : Fin m → (epsAt x ⟶ t.G)} {A : Matrix (Fin m) (Fin n) R}
    (hA : ∀ i, FramedFlatCoordinates.IsCombination x (A i) (fun k => (v k).left) (w i)) {N : Fin m → R} {w' : epsAt x ⟶ t.G}
    (h : FramedFlatCoordinates.IsCombination x N (fun k => (w k).left) w') :
    FramedFlatCoordinates.IsCombination x (Matrix.vecMul N A) (fun k => (v k).left) w' := by
  have e : ∀ {k : ℕ} (a : Fin k → R) (u : Fin k → (Sp (DualNumber R) ⟶ t.G.left)) (z : epsAt x ⟶ t.G),
      FramedFlatCoordinates.IsCombination x a u z ↔ Formalism.L2.Pj.IsCombAtG t x u a z.left := fun a u z =>
    exists_congr fun u' => and_congr Iff.rfl
      ⟨fun h => congrArg CommaMorphism.left h.symm, fun h => Over.OverMorphism.ext h.symm⟩
  rw [e, ← Matrix.mulVec_transpose]
  exact Formalism.L2.Pj.tanLinG _ (fun j => ⟨Over.w (v j), hv j⟩) (fun k => (w k).left) A.transpose N _
    (fun i => (e _ _ _).1 (hA i)) ((e _ _ _).1 h)

theorem comb_comp (g' : R' →+* R'') {x' : Sp R' ⟶ S} {x'' : Sp R'' ⟶ S} (hx : x'' = spMap g' ≫ x') {n : ℕ}
    {v : Fin n → (Sp (DualNumber R') ⟶ t.G.left)} {v' : Fin n → (epsAt x' ⟶ t.G)} {v₂ v'' : Fin n → (epsAt x'' ⟶ t.G)}
    (hv : ∀ i, spMap (TrivSqZeroExt.fstHom R'' R'' R'').toRingHom ≫ (v₂ i).left = (1 : Over.mk x'' ⟶ t.G).left)
    (h₂ : ∀ i, (v₂ i).left = spMap (Chart.dualMapR g') ≫ v i)
    {M : Matrix (Fin n) (Fin n) R'} {M' : Matrix (Fin n) (Fin n) R''}
    (h : ∀ i, FramedFlatCoordinates.IsCombination x' (M i) v (v' i))
    (h' : ∀ i, FramedFlatCoordinates.IsCombination x'' (M' i) (fun k => spMap (Chart.dualMapR g') ≫ (v' k).left) (v'' i)) (i : Fin n) :
    FramedFlatCoordinates.IsCombination x'' ((M' * g'.mapMatrix M) i) (fun k => (v₂ k).left) (v'' i) := by
  subst hx
  refine comb_vecMul hv (w := fun k => DetExtendZero.epsMap g' x' ≫ v' k) (A := g'.mapMatrix M) (fun k => ?_) (h' i)
  simp only [h₂]
  exact DetExtendZero.comb_map g' rfl (h k) rfl

variable {j : c.F →+* R} {j' : c.F →+* R'} {x : Sp R ⟶ X}
  {v : Fin p → (epsAt (x ≫ π) ⟶ t.G)} {w : Fin q → (epsAt (x ≫ π) ⟶ t.G)} {x' : Sp R' ⟶ X}
  {v' : Fin p → (epsAt (x' ≫ π) ⟶ t.G)} {w' : Fin q → (epsAt (x' ≫ π) ⟶ t.G)} {x'' : Sp R'' ⟶ X}
  {v'' : Fin p → (epsAt (x'' ≫ π) ⟶ t.G)} {w'' : Fin q → (epsAt (x'' ≫ π) ⟶ t.G)}

theorem chg_comp {g : R →+* R'} {g' : R' →+* R''} (h : IsFrame t π s V (HermitianCompactForm.chi c τ) j x v w) {M N M' N'}
    (hc : IsChg t π g x v w x' v' w' M N) (hc' : IsChg t π g' x' v' w' x'' v'' w'' M' N') :
    IsChg t π (g'.comp g) x v w x'' v'' w'' (M' * g'.mapMatrix M) (N' * g'.mapMatrix N) := by
  have hx : x'' = spMap (g'.comp g) ≫ x := by rw [hc'.1, hc.1, DetExtendZero.spMap_comp, Category.assoc]
  have hx' : x'' ≫ π = spMap g' ≫ x' ≫ π := by rw [hc'.1, Category.assoc]
  obtain ⟨v₂, w₂, h₂, a, b⟩ := exists_pull (g'.comp g) h hx
  refine ⟨hx, fun i => ?_, fun i => ?_⟩
  · simp only [← a]
    exact comb_comp g' hx' (fun k => (h₂.2.2.1.1 k).1)
      (fun k => by rw [a, DetExtendZero.dual_comp]; exact Category.assoc _ _ _) hc.2.1 hc'.2.1 i
  · simp only [← b]
    exact comb_comp g' hx' (fun k => (h₂.2.2.2.1 k).1)
      (fun k => by rw [b, DetExtendZero.dual_comp]; exact Category.assoc _ _ _) hc.2.2 hc'.2.2 i

theorem chg_unique {g : R →+* R'} (h : IsFrame t π s V (HermitianCompactForm.chi c τ) j x v w)
    (h' : IsFrame t π s V (HermitianCompactForm.chi c τ) j' x' v' w') {M N M' N'}
    (hc : IsChg t π g x v w x' v' w' M N) (hc' : IsChg t π g x v w x' v' w' M' N') : M = M' ∧ N = N' := by
  obtain ⟨v₁, w₁, h₁, a, b⟩ := exists_pull g h hc.1
  obtain rfl := (exists_chg g h h' hc.1).1
  obtain ⟨-, h1, h2⟩ := hc
  obtain ⟨-, h1', h2'⟩ := hc'
  simp only [← a] at h1 h1'
  simp only [← b] at h2 h2'
  exact ⟨funext fun i => (h₁.2.2.1.2 _ (h'.2.2.1.1 i)).unique (h1 i) (h1' i),
    funext fun i => (h₁.2.2.2.2 _ (h'.2.2.2.1 i)).unique (h2 i) (h2' i)⟩

theorem chg_isUnit {g : R →+* R'} (h : IsFrame t π s V (HermitianCompactForm.chi c τ) j x v w)
    (h' : IsFrame t π s V (HermitianCompactForm.chi c τ) j' x' v' w') {M N}
    (hc : IsChg t π g x v w x' v' w' M N) : IsUnit M.det ∧ IsUnit N.det := by
  obtain ⟨v₁, w₁, h₁, a, b⟩ := exists_pull g h hc.1
  obtain ⟨-, M', N', hc'⟩ := exists_chg (RingHom.id R') h' h₁ (by rw [DetExtendZero.spMap_id, Category.id_comp])
  have h1 : IsChg t π g x v w x' v₁ w₁ 1 1 := by
    refine ⟨hc.1, fun i => ?_, fun i => ?_⟩
    · simp only [← a]; exact DetExtendZero.comb_one (fun k => (h₁.2.2.1.1 k).1) i
    · simp only [← b]; exact DetExtendZero.comb_one (fun k => (h₁.2.2.2.1 k).1) i
  obtain ⟨e1, e2⟩ := chg_unique h h₁ (chg_comp h hc hc') h1
  exact ⟨Matrix.isUnit_det_of_left_inverse e1, Matrix.isUnit_det_of_left_inverse e2⟩

variable (c t π s V τ p q) in

def Framed (R : Type) [CommRing R] : Type :=
  Σ' (x : Sp R ⟶ X) (v : Fin p → (epsAt (x ≫ π) ⟶ t.G)) (w : Fin q → (epsAt (x ≫ π) ⟶ t.G)),
    ∃ j, IsFrame t π s V (HermitianCompactForm.chi c τ) j x v w

def factor (g : R →+* R') (a : Framed c t π s V τ p q R) (a' : Framed c t π s V τ p q R') : R' :=
  @Classical.epsilon R' ⟨0⟩ fun e => IsUnit e ∧
    ∀ M N, IsChg t π g a.1 a.2.1 a.2.2.1 a'.1 a'.2.1 a'.2.2.1 M N → N.det = e * M.det

theorem factor_spec (g : R →+* R') (a : Framed c t π s V τ p q R) (a' : Framed c t π s V τ p q R')
    (hx : a'.1 = spMap g ≫ a.1) : IsUnit (factor g a a') ∧
    ∀ M N, IsChg t π g a.1 a.2.1 a.2.2.1 a'.1 a'.2.1 a'.2.2.1 M N → N.det = factor g a a' * M.det := by
  refine Classical.epsilon_spec_aux ⟨0⟩ (fun e => IsUnit e ∧
    ∀ M N, IsChg t π g a.1 a.2.1 a.2.2.1 a'.1 a'.2.1 a'.2.2.1 M N → N.det = e * M.det) ?_
  obtain ⟨j, h⟩ := a.2.2.2
  obtain ⟨j', h'⟩ := a'.2.2.2
  obtain ⟨-, M, N, hc⟩ := exists_chg g h h' hx
  obtain ⟨⟨u, hu⟩, hN⟩ := chg_isUnit h h' hc
  refine ⟨N.det * u⁻¹, hN.mul (Units.isUnit _), fun M' N' hc' => ?_⟩
  obtain ⟨rfl, rfl⟩ := chg_unique h h' hc hc'
  rw [← hu, Units.inv_mul_cancel_right]

theorem factor_comp (g : R →+* R') (g' : R' →+* R'') (a : Framed c t π s V τ p q R) (a' : Framed c t π s V τ p q R')
    (a'' : Framed c t π s V τ p q R'') (hx : a'.1 = spMap g ≫ a.1) (hx' : a''.1 = spMap g' ≫ a'.1) :
    factor (g'.comp g) a a'' = factor g' a' a'' * g' (factor g a a') := by
  obtain ⟨j, h⟩ := a.2.2.2
  obtain ⟨j', h'⟩ := a'.2.2.2
  obtain ⟨j'', h''⟩ := a''.2.2.2
  obtain ⟨-, M, N, hc⟩ := exists_chg g h h' hx
  obtain ⟨-, M', N', hc'⟩ := exists_chg g' h' h'' hx'
  have hc'' := chg_comp h hc hc'
  have e := (factor_spec _ a a'' hc''.1).2 _ _ hc''
  refine (chg_isUnit h h'' hc'').1.mul_right_cancel ?_
  rw [← e, Matrix.det_mul, Matrix.det_mul, ← RingHom.map_det, ← RingHom.map_det, (factor_spec _ a a' hx).2 _ _ hc,
    (factor_spec _ a' a'' hx').2 _ _ hc', map_mul]
  ring

end Change

theorem exists_section : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (l : Level H) (c : Coeff l) (S X : Scheme.{0}) (t : SAB H S) (π : X ⟶ S) (s : X ⟶ Sp c.F) (τ : E →+* ℂ) (p q : ℕ) (Y : Scheme.{0}) [IsIntegral Y] (io : Y ⟶ X) (V : Set X), IsOpenImmersion io → Set.range io = V → FrameCover t π s V (HermitianCompactForm.chi c τ) p q → ∀ (j₀ : c.F →+* Y.functionField) v₀ w₀ (δ : Y.functionField), IsFrame t π s V (HermitianCompactForm.chi c τ) j₀ (genPt Y ≫ io) v₀ w₀ → (∀ y : Y, UnitAtPt t π s V (HermitianCompactForm.chi c τ) io v₀ w₀ δ y) → ∃ σ : Rule t π p q, IsSection t π s V (HermitianCompactForm.chi c τ) σ ∧ NowhereZero t π s V (HermitianCompactForm.chi c τ) σ ∧ σ Y.functionField (genPt Y ≫ io) v₀ w₀ = δ := by
  intro E _ _ _ H l c S X t π s τ p q Y _ io V hio hV hcov j₀ v₀ w₀ δ h₀ hδ
  subst hV
  obtain ⟨f, hf, hu, h0⟩ := exists_coord (io := io) (Fr := Framed c t π s (Set.range io) τ p q)
    (pt := fun _ _ a => a.1) (d := fun _ _ _ _ => factor) (a₀ := ⟨_, v₀, w₀, j₀, h₀⟩) (δ := δ)
    (fun R _ a => a.2.2.2.choose_spec.2.1)
    (fun R R' _ _ g a => by
      obtain ⟨j, h⟩ := a.2.2.2
      obtain ⟨v, w, h', -⟩ := exists_pull g h rfl
      exact ⟨⟨_, v, w, _, h'⟩, rfl⟩)
    (fun R R' _ _ g a a' h => (factor_spec g a a' h).1) (fun _ _ _ _ _ _ => factor_comp) rfl
    (fun z hz => by
      obtain ⟨W, hW, j, v, w, hzW, h⟩ := hcov z hz
      refine ⟨Γ(X, W), inferInstance, ⟨_, v, w, j, h⟩, inferInstanceAs (IsOpenImmersion hW.fromSpec), ?_⟩
      rw [show Set.range _ = _ from hW.range_fromSpec]
      exact hzW)
    (fun y => by
      obtain ⟨j, v, w, M, N, u, h, hc, e⟩ := hδ y
      refine ⟨⟨_, v, w, j, h⟩, u, u.isUnit, rfl, (chg_isUnit h h₀ hc).1.mul_left_cancel ?_⟩
      rw [← e, (factor_spec _ ⟨_, v, w, j, h⟩ ⟨_, v₀, w₀, j₀, h₀⟩ hc.1).2 M N hc]
      ring)
  classical
  let σ : Rule t π p q := fun R _ x v w =>
    if h : ∃ j, IsFrame t π s (Set.range io) (HermitianCompactForm.chi c τ) j x v w then f R ⟨x, v, w, h⟩ else 0
  have hσ : ∀ (R : Type) [CommRing R] j x v w (h : IsFrame t π s (Set.range io) (HermitianCompactForm.chi c τ) j x v w),
      σ R x v w = f R ⟨x, v, w, j, h⟩ := fun R _ j x v w h => dif_pos ⟨j, h⟩
  refine ⟨σ, isSection_of_chg fun R R' _ _ g j j' x v w x' v' w' M N h h' hc => ?_, fun R _ j x v w h => ?_, ?_⟩
  · rw [hσ R j x v w h, hσ R' j' x' v' w' h', hf R R' g ⟨x, v, w, j, h⟩ ⟨x', v', w', j', h'⟩ hc.1,
      (factor_spec g ⟨x, v, w, j, h⟩ ⟨x', v', w', j', h'⟩ hc.1).2 M N hc]
    ring
  · rw [hσ R j x v w h]
    exact hu _ _
  · rw [hσ _ j₀ _ v₀ w₀ h₀]
    exact h0

end GlobalTheory.DetLine.FromGeneric
