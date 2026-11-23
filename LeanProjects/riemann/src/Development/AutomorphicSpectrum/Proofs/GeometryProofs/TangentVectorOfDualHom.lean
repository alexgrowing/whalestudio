import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EigLat
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsCocharLie
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.TanChart

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

theorem spMap_fromSpec_hom {X Y : Scheme.{0}} (f : X ⟶ Y) {U : X.Opens} {V : Y.Opens}
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) (hUV : U ≤ f ⁻¹ᵁ V) {D : Type} [CommRing D]
    (ψ : Γ(X, U) →+* D) :
    spMap ψ ≫ hU.fromSpec ≫ f = spMap (ψ.comp (f.appLE V U hUV).hom) ≫ hV.fromSpec := by
  rw [← IsAffineOpen.SpecMap_appLE_fromSpec f hV hU hUV, ← Category.assoc, ← Spec.map_comp]
  rfl

theorem ringHom_eq_of_fromSpec {X : Scheme.{0}} {U : X.Opens} (hU : IsAffineOpen U) {D : Type} [CommRing D]
    {ψ ψ' : Γ(X, U) →+* D} (h : spMap ψ ≫ hU.fromSpec = spMap ψ' ≫ hU.fromSpec) : ψ = ψ' := by
  rw [cancel_mono] at h
  exact congrArg CommRingCat.Hom.hom (Spec.map_injective h)

theorem exists_ringHom_of_le {X : Scheme.{0}} {U : X.Opens} (hU : IsAffineOpen U) {D : Type} [CommRing D]
    (x : Sp D ⟶ X) (hx : ⊤ ≤ x ⁻¹ᵁ U) : ∃ φ : Γ(X, U) →+* D, x = spMap φ ≫ hU.fromSpec := by
  refine ⟨(x.appLE U ⊤ hx ≫ (Scheme.ΓSpecIso (CommRingCat.of D)).hom).hom, ?_⟩
  have h := IsAffineOpen.SpecMap_appLE_fromSpec x hU (isAffineOpen_top (Spec (CommRingCat.of D))) hx
  rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv] at h
  change x = Spec.map (CommRingCat.ofHom (x.appLE U ⊤ hx ≫ (Scheme.ΓSpecIso (CommRingCat.of D)).hom).hom) ≫ _
  rw [CommRingCat.ofHom_hom, Spec.map_comp, Category.assoc, h, ← Category.assoc, ← Spec.map_comp,
    Iso.inv_hom_id, Spec.map_id, Category.id_comp]

theorem le_preimage_of_fst {X : Scheme.{0}} {U : X.Opens} {C : Type} [CommRing C] (x : Sp (DualNumber C) ⟶ X)
    (h : ∀ p, (spMap (TrivSqZeroExt.fstHom C C C).toRingHom ≫ x) p ∈ U) : ⊤ ≤ x ⁻¹ᵁ U := by
  intro p _
  have hs : Function.Surjective (TrivSqZeroExt.fstHom C C C).toRingHom := fun c => ⟨TrivSqZeroExt.inl c, by simp⟩
  have hker : RingHom.ker (TrivSqZeroExt.fstHom C C C).toRingHom ≤ p.asIdeal := fun a ha => by
    have h0 : a.fst = 0 := ha
    have h2 : a ^ 2 = 0 := by
      ext <;> simp [pow_two, TrivSqZeroExt.fst_mul, TrivSqZeroExt.snd_mul, h0]
    exact p.isPrime.mem_of_pow_mem 2 (by rw [h2]; exact zero_mem _)
  haveI := p.isPrime
  have hprime := Ideal.map_isPrime_of_surjective hs hker
  let p₀ : ↥(Sp C) := (⟨p.asIdeal.map (TrivSqZeroExt.fstHom C C C).toRingHom, hprime⟩ : PrimeSpectrum C)
  have hp : (spMap (TrivSqZeroExt.fstHom C C C).toRingHom).base p₀ = p := by
    apply PrimeSpectrum.ext
    change Ideal.comap (TrivSqZeroExt.fstHom C C C).toRingHom
      (Ideal.map (TrivSqZeroExt.fstHom C C C).toRingHom p.asIdeal) = p.asIdeal
    rw [Ideal.comap_map_of_surjective' _ hs, sup_eq_left.mpr hker]
  have e := h p₀
  simp only [Scheme.Hom.comp_apply] at e
  show x p ∈ U
  rw [← hp]
  exact e

theorem tan_iff_der (S : Scheme.{0}) (G : Over S) [GrpObj G] (U : G.left.Opens) (V : S.Opens) (hU : IsAffineOpen U)
    (hV : IsAffineOpen V) (hUV : U ≤ G.hom ⁻¹ᵁ V)
    (C : Type) [CommRing C] (y : Sp C ⟶ S) (u : Γ(G.left, U) →+* C) :
    (1 : Over.mk y ⟶ G).left = spMap u ≫ hU.fromSpec →
    (∀ φ : Γ(G.left, U) →+* DualNumber C, (∀ a, (φ a).fst = u a) →
       (∀ b : Γ(S, V), (φ ((G.hom.appLE V U hUV).hom b)).snd = 0) →
       ∃ v : epsAt y ⟶ G, IsTanAt G y v ∧ v.left = spMap φ ≫ hU.fromSpec) ∧
    (∀ v : epsAt y ⟶ G, IsTanAt G y v → ∃ φ : Γ(G.left, U) →+* DualNumber C, (∀ a, (φ a).fst = u a) ∧
       (∀ b : Γ(S, V), (φ ((G.hom.appLE V U hUV).hom b)).snd = 0) ∧ v.left = spMap φ ≫ hU.fromSpec) := by
  intro h1
  have hal : ∀ c : C, algebraMap C (DualNumber C) c = TrivSqZeroExt.inl c := fun _ => rfl
  have hy : y = spMap (u.comp (G.hom.appLE V U hUV).hom) ≫ hV.fromSpec := by
    have hw := Over.w (1 : Over.mk y ⟶ G)
    rw [h1, Category.assoc, spMap_fromSpec_hom G.hom hU hV hUV u] at hw
    exact hw.symm
  have hbase : spMap (algebraMap C (DualNumber C)) ≫ y =
      spMap (((algebraMap C (DualNumber C)).comp u).comp (G.hom.appLE V U hUV).hom) ≫ hV.fromSpec := by
    rw [hy, ← Category.assoc, ← Spec.map_comp]
    rfl
  refine ⟨fun φ hφ hb => ?_, fun v hv => ?_⟩
  · have hcomp : φ.comp (G.hom.appLE V U hUV).hom =
        ((algebraMap C (DualNumber C)).comp u).comp (G.hom.appLE V U hUV).hom := by
      ext b
      · simpa [hal] using hφ _
      · simpa [hal] using hb b
    refine ⟨Over.homMk (spMap φ ≫ hU.fromSpec) ?_, ?_, rfl⟩
    · change (spMap φ ≫ hU.fromSpec) ≫ G.hom = spMap (algebraMap C (DualNumber C)) ≫ y
      rw [Category.assoc, spMap_fromSpec_hom G.hom hU hV hUV φ, hbase, hcomp]
    · have hfst : (TrivSqZeroExt.fstHom C C C).toRingHom.comp φ = u := by
        ext a
        exact hφ a
      change spMap (TrivSqZeroExt.fstHom C C C).toRingHom ≫ spMap φ ≫ hU.fromSpec = _
      rw [h1, ← Category.assoc, ← Spec.map_comp, ← hfst]
      rfl
  · have hv' : spMap (TrivSqZeroExt.fstHom C C C).toRingHom ≫ v.left = spMap u ≫ hU.fromSpec := hv.trans h1
    have hle : ⊤ ≤ v.left ⁻¹ᵁ U := by
      refine le_preimage_of_fst v.left fun p => ?_
      rw [hv']
      simp only [Scheme.Hom.comp_apply]
      exact hU.range_fromSpec.subset (Set.mem_range_self _)
    obtain ⟨φ, hφ⟩ := exists_ringHom_of_le hU v.left hle
    have hfst : (TrivSqZeroExt.fstHom C C C).toRingHom.comp φ = u := by
      apply ringHom_eq_of_fromSpec hU
      rw [← hv', hφ, ← Category.assoc, ← Spec.map_comp]
      rfl
    have hcomp : φ.comp (G.hom.appLE V U hUV).hom =
        ((algebraMap C (DualNumber C)).comp u).comp (G.hom.appLE V U hUV).hom := by
      apply ringHom_eq_of_fromSpec hV
      rw [← hbase, ← spMap_fromSpec_hom G.hom hU hV hUV φ, ← Category.assoc, ← hφ]
      exact Over.w v
    refine ⟨φ, fun a => RingHom.congr_fun hfst a, fun b => ?_, hφ⟩
    have := RingHom.congr_fun hcomp b
    simpa [hal] using congrArg TrivSqZeroExt.snd this

end GlobalTheory.CompanionTheory.Ar.TanChart
