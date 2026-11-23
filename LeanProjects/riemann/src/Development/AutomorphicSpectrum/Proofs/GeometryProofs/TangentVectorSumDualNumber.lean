import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EigLat
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsCocharLie
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TangentSectionAdditiveStatement

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.TanMul

abbrev red (C : Type) [CommRing C] : Sp C ⟶ Sp (DualNumber C) :=
  spMap (TrivSqZeroExt.fstHom C C C).toRingHom

theorem red_surj (C : Type) [CommRing C] (p : Sp (DualNumber C)) : ∃ q : Sp C, red C q = p := by
  let P : PrimeSpectrum (DualNumber C) := p
  have hker : RingHom.ker (TrivSqZeroExt.fstHom C C C).toRingHom ≤ P.asIdeal := by
    intro a ha
    have h0 : a.fst = 0 := ha
    have h2 : a * a = 0 := by
      ext <;> simp [TrivSqZeroExt.fst_mul, TrivSqZeroExt.snd_mul, h0]
    have : a * a ∈ P.asIdeal := by rw [h2]; exact zero_mem _
    rcases P.isPrime.mem_or_mem this with h | h <;> exact h
  have hs : Function.Surjective (TrivSqZeroExt.fstHom C C C).toRingHom :=
    fun a => ⟨TrivSqZeroExt.inl a, rfl⟩
  haveI := P.isPrime
  have hprime := Ideal.map_isPrime_of_surjective hs hker
  refine ⟨(⟨_, hprime⟩ : PrimeSpectrum C), ?_⟩
  have e : PrimeSpectrum.comap (TrivSqZeroExt.fstHom C C C).toRingHom ⟨_, hprime⟩ = P := by
    apply PrimeSpectrum.ext
    change Ideal.comap (TrivSqZeroExt.fstHom C C C).toRingHom
      (Ideal.map (TrivSqZeroExt.fstHom C C C).toRingHom P.asIdeal) = P.asIdeal
    rw [Ideal.comap_map_of_surjective' _ hs, sup_eq_left.mpr hker]
  exact e

variable {X : Scheme.{0}} {U : X.Opens} (hU : IsAffineOpen U)

include hU in

theorem top_le {C : Type} [CommRing C] (t : Sp (DualNumber C) ⟶ X) (u : Γ(X, U) →+* C)
    (h : red C ≫ t = spMap u ≫ hU.fromSpec) : ⊤ ≤ t ⁻¹ᵁ U := by
  intro p _
  obtain ⟨q, rfl⟩ := red_surj C p
  show t (red C q) ∈ U
  have e : t (red C q) = hU.fromSpec (spMap u q) := by
    have := congrArg (fun f : Sp C ⟶ X => f q) h
    simpa using this
  rw [e]
  exact hU.range_fromSpec.subset (Set.mem_range_self _)

def ringOf {A : Type} [CommRing A] (t : Sp A ⟶ X) (h : ⊤ ≤ t ⁻¹ᵁ U) : Γ(X, U) →+* A :=
  (t.appLE U ⊤ h ≫ (Scheme.ΓSpecIso (CommRingCat.of A)).hom).hom

theorem ringOf_spec {A : Type} [CommRing A] (t : Sp A ⟶ X) (h : ⊤ ≤ t ⁻¹ᵁ U) :
    spMap (ringOf t h) ≫ hU.fromSpec = t := by
  have e := IsAffineOpen.SpecMap_appLE_fromSpec t hU (isAffineOpen_top (Spec (CommRingCat.of A))) h
  rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv] at e
  have e2 : spMap (ringOf t h) = Spec.map (t.appLE U ⊤ h ≫ (Scheme.ΓSpecIso (CommRingCat.of A)).hom) := by
    unfold ringOf spMap
    rw [CommRingCat.ofHom_hom]
  rw [e2, Spec.map_comp, Category.assoc, e, ← Category.assoc, ← Spec.map_comp, Iso.inv_hom_id, Spec.map_id,
    Category.id_comp]

include hU in
theorem ring_inj {A : Type} [CommRing A] {f g : Γ(X, U) →+* A}
    (h : spMap f ≫ hU.fromSpec = spMap g ≫ hU.fromSpec) : f = g := by
  rw [cancel_mono] at h
  have := congrArg CommRingCat.Hom.hom (Spec.map_injective h)
  simpa using this

theorem ringOf_eq {A : Type} [CommRing A] {t : Sp A ⟶ X} (h : ⊤ ≤ t ⁻¹ᵁ U) {f : Γ(X, U) →+* A}
    (e : t = spMap f ≫ hU.fromSpec) : ringOf t h = f :=
  ring_inj hU ((ringOf_spec hU t h).trans e)

variable {S : Scheme.{0}} {C : Type} [CommRing C] (y : Sp C ⟶ S)

def redO : Over.mk y ⟶ epsAt y :=
  Over.homMk (red C) (by
    have h : (TrivSqZeroExt.fstHom C C C).toRingHom.comp (algebraMap C (DualNumber C)) = RingHom.id C := by
      ext a; simp
    show red C ≫ spMap (algebraMap C (DualNumber C)) ≫ y = y
    rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, h]
    simp)

def projO : epsAt y ⟶ Over.mk y :=
  Over.homMk (spMap (algebraMap C (DualNumber C))) rfl

theorem comp_one_O {G T T' : Over S} [GrpObj G] (f : T' ⟶ T) : f ≫ (1 : T ⟶ G) = 1 := by
  rw [Hom.one_def, Hom.one_def, ← Category.assoc, toUnit_unique (f ≫ toUnit T) (toUnit T')]

theorem comp_mul_O {G T T' : Over S} [GrpObj G] (f : T' ⟶ T) (a b : T ⟶ G) :
    f ≫ (a * b) = (f ≫ a) * (f ≫ b) := by
  rw [Hom.mul_def, Hom.mul_def, ← Category.assoc, comp_lift]

theorem mul_left_eq : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (U : G.left.Opens) (hU : IsAffineOpen U)
  (C : Type) [CommRing C] (y : Sp C ⟶ S) (u : Γ(G.left, U) →+* C),
  (1 : Over.mk y ⟶ G).left = spMap u ≫ hU.fromSpec →
  ∀ (v w : epsAt y ⟶ G), IsTanAt G y v → IsTanAt G y w →
  ∀ φ ψ χ : Γ(G.left, U) →+* DualNumber C, (∀ a, (φ a).fst = u a) → (∀ a, (ψ a).fst = u a) → (∀ a, (χ a).fst = u a) →
    (∀ a, (χ a).snd = (φ a).snd + (ψ a).snd) →
    v.left = spMap φ ≫ hU.fromSpec → w.left = spMap ψ ≫ hU.fromSpec → (v * w).left = spMap χ ≫ hU.fromSpec := by
  intro S G _ U hU C _ y u hu v w hv hw φ ψ χ hφ hψ hχ hs ev ew
  have rv : redO y ≫ v = 1 := Over.OverMorphism.ext hv
  have rw' : redO y ≫ w = 1 := Over.OverMorphism.ext hw
  have rvw : redO y ≫ (v * w) = 1 := by rw [comp_mul_O, rv, rw', _root_.one_mul]
  have r1 : redO y ≫ (1 : epsAt y ⟶ G) = 1 := comp_one_O _
  have lv : red C ≫ v.left = spMap u ≫ hU.fromSpec := hv.trans hu
  have lw : red C ≫ w.left = spMap u ≫ hU.fromSpec := hw.trans hu
  have lvw : red C ≫ (v * w).left = spMap u ≫ hU.fromSpec :=
    (congrArg (fun f => CommaMorphism.left f) rvw).trans hu
  have l1 : red C ≫ (1 : epsAt y ⟶ G).left = spMap u ≫ hU.fromSpec :=
    (congrArg (fun f => CommaMorphism.left f) r1).trans hu
  have hv' := top_le hU _ u lv
  have hw' := top_le hU _ u lw
  have hvw := top_le hU _ u lvw
  have h1 := top_le hU _ u l1
  have e1 : (1 : epsAt y ⟶ G).left = spMap ((algebraMap C (DualNumber C)).comp u) ≫ hU.fromSpec := by
    have p1 : projO y ≫ (1 : Over.mk y ⟶ G) = 1 := comp_one_O _
    have p2 : spMap (algebraMap C (DualNumber C)) ≫ (1 : Over.mk y ⟶ G).left = (1 : epsAt y ⟶ G).left :=
      congrArg (fun f => CommaMorphism.left f) p1
    rw [← p2, hu, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  have hfst : (TrivSqZeroExt.fstHom C C C).toRingHom.comp (ringOf (v * w).left hvw) = u := by
    apply ring_inj hU
    have : spMap ((TrivSqZeroExt.fstHom C C C).toRingHom.comp (ringOf (v * w).left hvw)) =
        red C ≫ spMap (ringOf (v * w).left hvw) := by
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rw [this, Category.assoc, ringOf_spec hU, lvw]
  have hχ' : ringOf (v * w).left hvw = χ := by
    ext s
    · rw [hχ]
      exact RingHom.congr_fun hfst s
    · have key := congrArg (Scheme.ΓSpecIso (CommRingCat.of (DualNumber C))).hom.hom
        (GlobalTheory.T.tangent_section_additive S G C y v w hv hw U hv' hw' hvw h1 s)
      rw [map_add, map_add] at key
      change ringOf (v * w).left hvw s + ringOf (1 : epsAt y ⟶ G).left h1 s =
        ringOf v.left hv' s + ringOf w.left hw' s at key
      rw [ringOf_eq hU h1 e1, ringOf_eq hU hv' ev, ringOf_eq hU hw' ew] at key
      have := congrArg TrivSqZeroExt.snd key
      have h0 : TrivSqZeroExt.snd (((algebraMap C (DualNumber C)).comp u) s) = 0 := by
        simp [TrivSqZeroExt.algebraMap_eq_inl]
      rw [TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_add, h0, add_zero] at this
      rw [hs, this]
  rw [← hχ', ringOf_spec hU]

end GlobalTheory.CompanionTheory.Ar.TanMul
