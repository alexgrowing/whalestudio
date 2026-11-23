import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FunctionFieldMapCompConstFn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NadelVanishingCanonicalAddBoundary
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy
open Polynomial

namespace GlobalTheory.ZariskiDescent

theorem dvr_dvd_pow_of_mem_maximalIdeal {L : Type} [Field L] (V : ValuationSubring L)
    [IsDiscreteValuationRing V] (x y : V) (hx : x ∈ IsLocalRing.maximalIdeal V) (hy : y ≠ 0) :
    ∃ n : ℕ, y ∣ x ^ n := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible V
  obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hy hϖ
  rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ, Ideal.mem_span_singleton'] at hx
  obtain ⟨z, rfl⟩ := hx
  refine ⟨n, ⟨z ^ n * ↑u⁻¹, ?_⟩⟩
  rw [hu, mul_pow]
  have : (↑u * ↑u⁻¹ : V) = 1 := Units.mul_inv u
  linear_combination (-(z ^ n * ϖ ^ n)) * this

theorem mem_of_nonunits_of_localization {L : Type} [Field L] (V : ValuationSubring L)
    [IsDiscreteValuationRing V] {A : Type} [CommRing A] (ι : A →+* L) (hι : Function.Injective ι)
    (hV : ∀ a, ι a ∈ V)
    (hloc : ∀ s ∈ V, ∃ b d : A, ι d ≠ 0 ∧ (ι d)⁻¹ ∈ V ∧ s = ι b / ι d)
    (P₁ : Ideal A) [P₁.IsPrime] (hne : P₁ ≠ ⊥) (hP₁ : ∀ z ∈ P₁, ι z ∈ V.nonunits) :
    ∀ x, ι x ∈ V.nonunits → x ∈ P₁ := by
  intro x hx
  obtain ⟨y, hyP, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have hyV : (⟨ι y, hV y⟩ : V) ≠ 0 := by
    intro h
    apply hy0
    apply hι
    simpa using congrArg Subtype.val h
  have hxV : (⟨ι x, hV x⟩ : V) ∈ IsLocalRing.maximalIdeal V :=
    ValuationSubring.coe_mem_nonunits_iff.mp hx
  obtain ⟨n, w, hw⟩ := dvr_dvd_pow_of_mem_maximalIdeal V _ _ hxV hyV
  obtain ⟨b, d, hd0, hdinv, hwbd⟩ := hloc (w : L) w.2
  have hL : ι x ^ n = ι y * (ι b / ι d) := by
    have := congrArg Subtype.val hw
    simp only [SubmonoidClass.coe_pow, Subring.coe_mul] at this
    rw [this, ← hwbd]
    rfl
  have hA : x ^ n * d = y * b := by
    apply hι
    rw [map_mul, map_mul, map_pow, hL]
    field_simp
  have hmem : x ^ n * d ∈ P₁ := by
    rw [hA]; exact P₁.mul_mem_right b hyP
  rcases Ideal.IsPrime.mem_or_mem ‹_› hmem with h | h
  · exact Ideal.IsPrime.mem_of_pow_mem ‹_› n h
  · exfalso
    have := (ValuationSubring.mem_nonunits_iff_or (A := V)).mp (hP₁ d h)
    rcases this with h1 | h1
    · exact hd0 h1
    · exact h1 hdinv

end GlobalTheory.ZariskiDescent

namespace GlobalTheory.ZariskiDescent

theorem comap_nonunits_iff {K L : Type} [Field K] [Field L] (φ : K →+* L) (V : ValuationSubring L)
    (x : K) : x ∈ (V.comap φ).nonunits ↔ φ x ∈ V.nonunits := by
  rw [ValuationSubring.mem_nonunits_iff_or, ValuationSubring.mem_nonunits_iff_or,
    ValuationSubring.mem_comap, map_inv₀, map_eq_zero]

theorem height_le_one_of_going_down :
    ∀ (K L : Type) [Field K] [Field L] (φ : K →+* L) (c : ℂ →+* K) (V : ValuationSubring L)
      [IsDiscreteValuationRing V] (R : Subring K) [IsIntegrallyClosed R], (∀ a, c a ∈ R) →
      R ≤ (V.comap φ).toSubring → ∀ t : Finset L,
      (∀ x ∈ t, x ∈ V ∧ ∃ p : R[X], p.Monic ∧ p.eval₂ (φ.comp R.subtype) x = 0) →
      (∀ s ∈ V, ∃ b ∈ Subring.closure (Set.range (φ.comp c) ∪ ↑t),
        ∃ d ∈ Subring.closure (Set.range (φ.comp c) ∪ ↑t), d ≠ 0 ∧ d⁻¹ ∈ V ∧ s = b / d) →
      ∀ p : Ideal R, p.IsPrime → p ≠ ⊥ → (∀ r ∈ p, (r : K) ∈ (V.comap φ).nonunits) →
      ∀ r : R, (r : K) ∈ (V.comap φ).nonunits → r ∈ p := by
  intro K L _ _ φ c V _ R _ hc hRV t ht hloc p hp hp0 hpq
  letI : Algebra R L := (φ.comp R.subtype).toAlgebra
  have halg : ∀ r : R, algebraMap R L r = φ r := fun r => rfl
  set S : Subalgebra R L := Algebra.adjoin R (t : Set L) with hSdef
  have hinjRL : Function.Injective (algebraMap R L) := by
    intro a b h
    rw [halg, halg] at h
    exact Subtype.ext (φ.injective h)
  haveI : FaithfulSMul R S := by
    rw [faithfulSMul_iff_algebraMap_injective]
    intro a b h
    apply hinjRL
    have := congrArg Subtype.val h
    simpa using this
  haveI : Algebra.IsIntegral R S := Algebra.IsIntegral.adjoin (fun x hx => by
    obtain ⟨-, q, hq, hqx⟩ := ht x hx
    exact ⟨q, hq, hqx⟩)
  haveI : Algebra.HasGoingDown R S := inferInstance

  have hSV : ∀ z ∈ S, z ∈ V := by
    intro z hz
    have hz' : z ∈ S.toSubring := hz
    rw [hSdef, Algebra.adjoin_eq_ring_closure] at hz'
    refine (Subring.closure_le (t := V.toSubring)).mpr ?_ hz'
    rintro w (⟨r, rfl⟩ | hw)
    · exact (ValuationSubring.mem_comap).mp (hRV r.2)
    · exact (ht w hw).1

  have hclS : Subring.closure (Set.range (φ.comp c) ∪ ↑t) ≤ S.toSubring := by
    rw [Subring.closure_le]
    rintro w (⟨a, rfl⟩ | hw)
    · have : (φ.comp c) a = algebraMap R L ⟨c a, hc a⟩ := rfl
      rw [this]
      exact S.algebraMap_mem _
    · exact Algebra.subset_adjoin hw
  let ι : S →+* L := algebraMap S L
  have hι : Function.Injective ι := Subtype.val_injective
  let f : S →+* V := ι.codRestrict V (fun z => hSV z.1 z.2)
  let P : Ideal S := Ideal.comap f (IsLocalRing.maximalIdeal V)
  haveI : P.IsPrime := Ideal.comap_isPrime f _
  have hPmem : ∀ z : S, z ∈ P ↔ (z : L) ∈ V.nonunits := by
    intro z
    show f z ∈ IsLocalRing.maximalIdeal V ↔ _
    exact ValuationSubring.coe_mem_nonunits_iff.symm
  let q : Ideal R := P.comap (algebraMap R S)
  haveI : q.IsPrime := Ideal.comap_isPrime _ _
  haveI : P.LiesOver q := ⟨rfl⟩
  have hqmem : ∀ r : R, r ∈ q ↔ (r : K) ∈ (V.comap φ).nonunits := by
    intro r
    show algebraMap R S r ∈ P ↔ _
    rw [hPmem, comap_nonunits_iff]
    rfl
  have hpq' : p ≤ q := fun r hr => (hqmem r).mpr (hpq r hr)
  obtain ⟨P₁, hP₁P, hP₁, hP₁o⟩ := Ideal.exists_ideal_le_liesOver_of_le (p := p) (q := q) P hpq'
  have hpover : p = P₁.comap (algebraMap R S) := hP₁o.over
  have hP₁ne : P₁ ≠ ⊥ := by
    intro h
    apply hp0
    rw [hpover, h, eq_bot_iff]
    intro r hr
    rw [Ideal.mem_comap, Ideal.mem_bot] at hr
    rw [Ideal.mem_bot]
    apply hinjRL
    have := congrArg Subtype.val hr
    simpa using this
  have key := mem_of_nonunits_of_localization V ι hι (fun a => hSV a.1 a.2)
    (by
      intro s hs
      obtain ⟨b, hb, d, hd, hd0, hdinv, rfl⟩ := hloc s hs
      exact ⟨⟨b, hclS hb⟩, ⟨d, hclS hd⟩, hd0, hdinv, rfl⟩)
    P₁ hP₁ne (fun z hz => (hPmem z).mp (hP₁P hz))
  intro r hr
  rw [hpover, Ideal.mem_comap]
  apply key
  exact (hPmem _).mp ((hqmem r).mpr hr)

end GlobalTheory.ZariskiDescent
