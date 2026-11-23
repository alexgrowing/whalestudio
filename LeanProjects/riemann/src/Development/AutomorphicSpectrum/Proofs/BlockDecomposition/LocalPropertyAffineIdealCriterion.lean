import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.LeftZeroDuality.H1StructureDimLe
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsPowMulOfAway
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual PositivityTheory.ObstructionTrivialLocus GlobalTheory.CompanionTheory.TrivLoc
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompanionTheory.TrivLoc.Rep

theorem exists_basicOpen_le {Y : Scheme.{0}} {U V : Y.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (r : Γ(Y, V)) (y : Y) (hyU : y ∈ U) (hyr : y ∈ Y.basicOpen r) :
    ∃ f : Γ(Y, U), y ∈ Y.basicOpen f ∧ Y.basicOpen f ≤ Y.basicOpen r := by
  obtain ⟨f, g, e, hy⟩ := exists_basicOpen_le_affine_inter hU (hV.basicOpen r) y ⟨hyU, hyr⟩
  exact ⟨f, hy, e ▸ Y.basicOpen_le g⟩

theorem isUnit_res_of_le {Y : Scheme.{0}} {V W : Y.Opens} (r : Γ(Y, V)) (hle : W ≤ Y.basicOpen r)
    (hWV : W ≤ V) : IsUnit ((Y.presheaf.map (homOfLE hWV).op).hom r) := by
  have h := Y.toRingedSpace.isUnit_res_basicOpen r
  have e : (Y.presheaf.map (homOfLE hWV).op).hom r =
      (Y.presheaf.map (homOfLE hle).op).hom
        ((Y.presheaf.map (homOfLE (Y.basicOpen_le r)).op).hom r) := by
    rw [← CommRingCat.comp_apply, ← Functor.map_comp]; rfl
  rw [e]
  exact h.map (Y.presheaf.map (homOfLE hle).op).hom

theorem exists_ideal_on_basicOpen {Y : Scheme.{0}} (P : ∀ T : Scheme.{0}, (T ⟶ Y) → Prop)
    {U V : Y.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V) (f : Γ(Y, U)) (r : Γ(Y, V))
    (I : Ideal Γ(Y, V)) (hle : Y.basicOpen f ≤ Y.basicOpen r)
    (hI : ∀ (R' : Type) [CommRing R'] (g : Γ(Y, V) →+* R'), IsUnit (g r) →
      (P (Spec (CommRingCat.of R')) (Spec.map (CommRingCat.ofHom g) ≫ hV.fromSpec) ↔ I ≤ RingHom.ker g)) :
    ∃ J : Ideal Γ(Y, U), ∀ (R' : Type) [CommRing R'] (g : Γ(Y, U) →+* R'), IsUnit (g f) →
      (P (Spec (CommRingCat.of R')) (Spec.map (CommRingCat.ofHom g) ≫ hU.fromSpec) ↔ J ≤ RingHom.ker g) := by
  have hWV : Y.basicOpen f ≤ V := hle.trans (Y.basicOpen_le r)
  let resV : Γ(Y, V) →+* Γ(Y, Y.basicOpen f) := (Y.presheaf.map (homOfLE hWV).op).hom
  let I₂ : Ideal Γ(Y, Y.basicOpen f) := I.map resV
  haveI := hU.isLocalization_basicOpen f
  refine ⟨I₂.comap (algebraMap Γ(Y, U) Γ(Y, Y.basicOpen f)), fun R' _ g hu => ?_⟩
  let h' : Γ(Y, Y.basicOpen f) →+* R' := IsLocalization.Away.lift f hu
  have hcomp : h'.comp (algebraMap Γ(Y, U) Γ(Y, Y.basicOpen f)) = g := IsLocalization.Away.lift_comp f hu
  have hW := hU.basicOpen f
  have hg : CommRingCat.ofHom g =
      Y.presheaf.map (homOfLE (Y.basicOpen_le f)).op ≫ CommRingCat.ofHom h' := by
    rw [← hcomp]; rfl
  have hg' : CommRingCat.ofHom (h'.comp resV) =
      Y.presheaf.map (homOfLE hWV).op ≫ CommRingCat.ofHom h' := rfl
  have e : Spec.map (CommRingCat.ofHom g) ≫ hU.fromSpec =
      Spec.map (CommRingCat.ofHom (h'.comp resV)) ≫ hV.fromSpec := by
    rw [hg, hg', Spec.map_comp, Spec.map_comp, Category.assoc, Category.assoc,
      hU.map_fromSpec hW, hV.map_fromSpec hW]
  have hunit : IsUnit ((h'.comp resV) r) := (isUnit_res_of_le r hle hWV).map h'
  rw [e, hI R' _ hunit]
  constructor
  · intro h x hx
    have hx' : algebraMap Γ(Y, U) Γ(Y, Y.basicOpen f) x ∈ I₂ := hx
    have h2 : I₂ ≤ RingHom.ker h' := by
      rw [show I₂ = I.map resV from rfl, Ideal.map_le_iff_le_comap]
      intro z hz
      exact h hz
    have := h2 hx'
    rw [RingHom.mem_ker] at this ⊢
    rw [← hcomp]
    exact this
  · intro h z hz
    have h2 : I₂ ≤ RingHom.ker h' := by
      rw [← IsLocalization.map_comap (Submonoid.powers f) Γ(Y, Y.basicOpen f) I₂, Ideal.map_le_iff_le_comap]
      intro x hx
      have := h hx
      rw [RingHom.mem_ker] at this
      rw [Ideal.mem_comap, RingHom.mem_ker]
      rw [← hcomp] at this
      exact this
    exact h2 (Ideal.mem_map_of_mem resV hz)

theorem local_on_affine {Y : Scheme.{0}} (P : ∀ T : Scheme.{0}, (T ⟶ Y) → Prop)
    (stab : ∀ (T T' : Scheme.{0}) (h : T' ⟶ T) (t : T ⟶ Y), P T t → P T' (h ≫ t))
    (loc : ∀ (T : Scheme.{0}) (t : T ⟶ Y), (∀ x : T, ∃ W : T.Opens, x ∈ W ∧ P W.toScheme (W.ι ≫ t)) → P T t)
    {U : Y.Opens} (hU : IsAffineOpen U) (R' : Type) [CommRing R'] (g : Γ(Y, U) →+* R') (s : Set R')
    (hs : Ideal.span s = ⊤)
    (hQ : ∀ a ∈ s, P (Spec (CommRingCat.of (Localization.Away a)))
      (Spec.map (CommRingCat.ofHom ((algebraMap R' (Localization.Away a)).comp g)) ≫ hU.fromSpec)) :
    P (Spec (CommRingCat.of R')) (Spec.map (CommRingCat.ofHom g) ≫ hU.fromSpec) := by
  refine loc _ _ fun x => ?_
  let x' : PrimeSpectrum R' := x
  have hx : ∃ a ∈ s, a ∉ x'.asIdeal := by
    by_contra hcon
    push Not at hcon
    have : Ideal.span s ≤ x'.asIdeal := Ideal.span_le.2 hcon
    rw [hs] at this
    exact x'.2.ne_top (top_le_iff.1 this)
  obtain ⟨a, ha, hax⟩ := hx
  let j : Spec (CommRingCat.of (Localization.Away a)) ⟶ Spec (CommRingCat.of R') :=
    Spec.map (CommRingCat.ofHom (algebraMap R' (Localization.Away a)))
  haveI : IsOpenImmersion j := IsOpenImmersion.of_isLocalization a
  refine ⟨j.opensRange, ?_, ?_⟩
  · have h := PrimeSpectrum.localization_away_comap_range (Localization.Away a) a
    have hx' : x' ∈ Set.range (PrimeSpectrum.comap (algebraMap R' (Localization.Away a))) := by
      rw [h]; exact hax
    obtain ⟨z, hz⟩ := hx'
    exact ⟨z, hz⟩
  · have h0 := hQ a ha
    rw [CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc] at h0
    have h1 := stab _ _ j.isoOpensRange.inv _ h0
    rwa [← Category.assoc, Scheme.Hom.isoOpensRange_inv_comp] at h1

theorem exists_ideal_on_affine : ∀ (Y : Scheme.{0}) (P : ∀ T : Scheme.{0}, (T ⟶ Y) → Prop),
    (∀ (T T' : Scheme.{0}) (h : T' ⟶ T) (t : T ⟶ Y), P T t → P T' (h ≫ t)) →
    (∀ (T : Scheme.{0}) (t : T ⟶ Y), (∀ x : T, ∃ W : T.Opens, x ∈ W ∧ P W.toScheme (W.ι ≫ t)) → P T t) →
    (∀ y : Y, ∃ (U : Y.Opens) (hU : IsAffineOpen U) (r : Γ(Y, U)) (I : Ideal Γ(Y, U)), y ∈ Y.basicOpen r ∧
      ∀ (R' : Type) [CommRing R'] (g : Γ(Y, U) →+* R'), IsUnit (g r) →
        (P (Spec (CommRingCat.of R')) (Spec.map (CommRingCat.ofHom g) ≫ hU.fromSpec) ↔ I ≤ RingHom.ker g)) →
    ∀ (U : Y.Opens) (hU : IsAffineOpen U), ∃ J : Ideal Γ(Y, U), ∀ (R' : Type) [CommRing R'] (g : Γ(Y, U) →+* R'),
      (P (Spec (CommRingCat.of R')) (Spec.map (CommRingCat.ofHom g) ≫ hU.fromSpec) ↔ J ≤ RingHom.ker g) := by
  intro Y P stab loc hloc U hU
  let Q : ∀ (R' : Type) [CommRing R'], (Γ(Y, U) →+* R') → Prop := fun R' _ g =>
    P (Spec (CommRingCat.of R')) (Spec.map (CommRingCat.ofHom g) ≫ hU.fromSpec)
  let S : Set Γ(Y, U) := {f | ∃ J : Ideal Γ(Y, U), ∀ (R' : Type) [CommRing R'] (g : Γ(Y, U) →+* R'),
    IsUnit (g f) → (Q R' g ↔ J ≤ RingHom.ker g)}
  have hS : Ideal.span S = ⊤ := by
    refine hU.self_le_iSup_basicOpen_iff.1 fun y hy => ?_
    obtain ⟨V, hV, r, I, hyr, hI⟩ := hloc y
    obtain ⟨f, hyf, hle⟩ := exists_basicOpen_le hU hV r y hy hyr
    have hf : f ∈ S := exists_ideal_on_basicOpen P hU hV f r I hle hI
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨f, hf⟩, hyf⟩
  obtain ⟨s, hsS, hs⟩ := (Ideal.span_eq_top_iff_finite S).1 hS
  have hS' : ∀ f, f ∈ S → ∃ J : Ideal Γ(Y, U), ∀ (R' : Type) [CommRing R'] (g : Γ(Y, U) →+* R'),
    IsUnit (g f) → (Q R' g ↔ J ≤ RingHom.ker g) := fun _ h => h
  choose! I hI using hS'
  refine exists_ideal_of_local Q ?_ ?_ s hs I fun f hf => hI f (hsS hf)
  · intro R' R'' _ _ g h hq
    have := stab _ _ (Spec.map (CommRingCat.ofHom h)) _ hq
    change P _ _
    rwa [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp] at this
  · intro R' _ g s hs hQ
    exact local_on_affine P stab loc hU R' g s hs hQ

end GlobalTheory.CompanionTheory.TrivLoc.Rep
