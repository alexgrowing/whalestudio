import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDefiniteDatumGoodObj
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.SchRing

theorem spMap_comp' {R S T : Type} [CommRing R] [CommRing S] [CommRing T] (f : R →+* S) (g : S →+* T) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  simp only [spMap, CommRingCat.ofHom_comp, Spec.map_comp]

theorem spMap_inj {R S : Type} [CommRing R] [CommRing S] {a b : R →+* S} (h : spMap a = spMap b) : a = b := by
  have := Spec.map_injective h
  exact congrArg CommRingCat.Hom.hom this

theorem subsingleton_primeSpectrum_trivSqZeroExt (k : Type) [Field k] (M : Type) [AddCommGroup M] [Module k M] [Module kᵐᵒᵖ M] [IsCentralScalar k M] :
    Subsingleton (PrimeSpectrum (TrivSqZeroExt k M)) := by
  have key : ∀ (P : PrimeSpectrum (TrivSqZeroExt k M)) (a : TrivSqZeroExt k M), a ∈ P.asIdeal ↔ a.fst = 0 := by
    intro P a
    constructor
    · intro ha
      by_contra h
      have hu : IsUnit a := TrivSqZeroExt.isUnit_iff_isUnit_fst.mpr (isUnit_iff_ne_zero.mpr h)
      exact P.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ ha hu)
    · intro h
      have ha : a = TrivSqZeroExt.inr a.snd := TrivSqZeroExt.ext (by simp [h]) (by simp)
      apply P.isPrime.mem_of_pow_mem 2
      rw [ha, pow_two, TrivSqZeroExt.inr_mul_inr]
      exact P.asIdeal.zero_mem
  exact ⟨fun P Q => PrimeSpectrum.ext (Ideal.ext fun a => (key P a).trans (key Q a).symm)⟩

theorem range_subset_of_fst {X : Scheme.{0}} (k : Type) [Field k] (M : Type) [AddCommGroup M] [Module k M] [Module kᵐᵒᵖ M] [IsCentralScalar k M]
    (x : Sp k ⟶ X) (u : Sp (TrivSqZeroExt k M) ⟶ X)
    (h : spMap (TrivSqZeroExt.fstHom k k M).toRingHom ≫ u = x) : Set.range u.base ⊆ Set.range x.base := by
  rintro _ ⟨y, rfl⟩
  haveI := subsingleton_primeSpectrum_trivSqZeroExt k M
  let z : PrimeSpectrum k := ⟨⊥, Ideal.bot_prime⟩
  refine ⟨z, ?_⟩
  have hy : (spMap (TrivSqZeroExt.fstHom k k M).toRingHom).base z = y := Subsingleton.elim (α := PrimeSpectrum (TrivSqZeroExt k M)) _ _
  rw [← h, ← hy]
  rfl

theorem exists_ringHom_of_range {X : Scheme.{0}} {V : X.Opens} (hV : IsAffineOpen V) (D : Type) [CommRing D]
    (g : Sp D ⟶ X) (hg : Set.range g.base ⊆ (V : Set X)) : ∃ r : Γ(X, V) →+* D, g = spMap r ≫ hV.fromSpec := by
  have h' : Set.range g ⊆ Set.range hV.fromSpec := by rw [hV.range_fromSpec]; exact hg
  refine ⟨(Spec.preimage (IsOpenImmersion.lift hV.fromSpec g h')).hom, ?_⟩
  have e1 : spMap (Spec.preimage (IsOpenImmersion.lift hV.fromSpec g h')).hom = IsOpenImmersion.lift hV.fromSpec g h' := by
    simp only [spMap, CommRingCat.ofHom_hom, Spec.map_preimage]
  rw [e1, IsOpenImmersion.lift_fac]

theorem spMap_cancel {R D : Type} [CommRing R] [CommRing D] {Y : Scheme.{0}} (G : Sp R ⟶ Y) [Mono G]
    {a b : R →+* D} (h : spMap a ≫ G = spMap b ≫ G) : a = b :=
  spMap_inj (cancel_mono G |>.mp h)

end GlobalTheory.SchRing

namespace GlobalTheory.SchRing

theorem deformation_on_sections : ∀ (B : Type) [CommRing B] (X : Scheme.{0}) (s : X ⟶ Sp B) (U : (Sp B).Opens) (V : X.Opens),
    IsAffineOpen U → IsAffineOpen V → ∀ (e : V ≤ s ⁻¹ᵁ U) (d : ℕ) (k : Type) [Field k] (x : Sp k ⟶ X),
    Set.range x.base ⊆ (V : Set X) → (∃ u : Sp (TrivSqZeroExt k (Fin d → k)) ⟶ X, spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom ≫ u = x ∧ u ≫ s = spMap (algebraMap k (TrivSqZeroExt k (Fin d → k))) ≫ x ≫ s ∧ ∀ v : Sp (DualNumber k) ⟶ X, spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ v = x → v ≫ s = spMap (algebraMap k (DualNumber k)) ≫ x ≫ s → ∃! c : (Fin d → k) →ₗ[k] k, v = spMap (TrivSqZeroExt.map c).toRingHom ≫ u) →
    ∃ (φ : Γ(X, V) →+* k) (ψ : Γ(X, V) →+* TrivSqZeroExt k (Fin d → k)),
      (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom.comp ψ = φ ∧
      ψ.comp (s.appLE U V e).hom = (algebraMap k (TrivSqZeroExt k (Fin d → k))).comp (φ.comp (s.appLE U V e).hom) ∧
      ∀ v : Γ(X, V) →+* DualNumber k, (TrivSqZeroExt.fstHom k k k).toRingHom.comp v = φ →
        v.comp (s.appLE U V e).hom = (algebraMap k (DualNumber k)).comp (φ.comp (s.appLE U V e).hom) →
        ∃! c : (Fin d → k) →ₗ[k] k, v = (TrivSqZeroExt.map c).toRingHom.comp ψ := by
  intro B _ X s U V hU hV e d k _ x hx hyp
  obtain ⟨u, hux, hus, huniq⟩ := hyp
  obtain ⟨φ, hφ⟩ := exists_ringHom_of_range hV k x hx
  obtain ⟨ψ, hψ⟩ := exists_ringHom_of_range hV _ u ((range_subset_of_fst k _ x u hux).trans hx)
  have key := IsAffineOpen.SpecMap_appLE_fromSpec s hU hV e
  have hs : ∀ (D : Type) [CommRing D] (r : Γ(X, V) →+* D),
      spMap r ≫ hV.fromSpec ≫ s = spMap (r.comp (s.appLE U V e).hom) ≫ hU.fromSpec := by
    intro D _ r
    rw [← key, spMap_comp']
    rfl
  have hbase : ∀ (D : Type) [CommRing D] (alg : k →+* D) (r : Γ(X, V) →+* D),
      (spMap r ≫ hV.fromSpec) ≫ s = spMap alg ≫ x ≫ s ↔
        r.comp (s.appLE U V e).hom = alg.comp (φ.comp (s.appLE U V e).hom) := by
    intro D _ alg r
    rw [hφ]
    simp only [Category.assoc]
    rw [hs, ← Category.assoc (spMap alg) (spMap φ), ← spMap_comp', hs]
    constructor
    · intro h; exact spMap_inj ((cancel_mono hU.fromSpec).mp h)
    · intro h; rw [h]
  have hfst : ∀ (D : Type) [CommRing D] (f : D →+* k) (r : Γ(X, V) →+* D),
      spMap f ≫ spMap r ≫ hV.fromSpec = x ↔ f.comp r = φ := by
    intro D _ f r
    rw [hφ, ← Category.assoc, ← spMap_comp']
    constructor
    · intro h; exact spMap_cancel hV.fromSpec h
    · intro h; rw [h]
  refine ⟨φ, ψ, ?_, ?_, ?_⟩
  · rw [hψ] at hux; exact (hfst _ _ _).mp hux
  · rw [hψ] at hus; exact (hbase _ _ _).mp hus
  · intro v hv1 hv2
    have h1 : spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ (spMap v ≫ hV.fromSpec) = x := (hfst _ _ _).mpr hv1
    have h2 := (hbase _ _ _).mpr hv2
    obtain ⟨c, hc, hcu⟩ := huniq _ h1 h2
    refine ⟨c, ?_, ?_⟩
    · rw [hψ, ← Category.assoc, ← spMap_comp'] at hc
      exact spMap_cancel hV.fromSpec hc
    · intro c' hc'
      apply hcu
      rw [hψ, ← Category.assoc, ← spMap_comp', ← hc']

end GlobalTheory.SchRing
