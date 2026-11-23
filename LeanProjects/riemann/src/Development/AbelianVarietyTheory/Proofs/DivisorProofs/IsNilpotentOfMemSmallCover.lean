import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham

namespace GlobalTheory.Cris

set_option autoImplicit false in
open CategoryTheory AlgebraicGeometry DividedPowers in
private theorem isNilpotent_of_mem_of_isNilDP {B : Type} [CommRing B]
    {J : Ideal B} (δ : DividedPowers J) (hδ : _root_.GlobalTheory.Cris.IsNilDP δ) {x : B} (hx : x ∈ J) :
    IsNilpotent x := by
  obtain ⟨N, hN⟩ := hδ
  refine ⟨N, ?_⟩
  have h := hN [(N, x)] (by simpa using hx) (by simp)
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one] at h
  rw [← δ.factorial_mul_dpow_eq_pow hx, h, mul_zero]

set_option autoImplicit false in
open CategoryTheory AlgebraicGeometry DividedPowers in

theorem _root_.GlobalTheory.Cris.exists_finite_small_cover (R : Type) [CommRing R] (I : Ideal R) (κ : DividedPowers I)
    (X : Scheme.{0}) (s : X ⟶ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp R) (K : Type) (U : K → X.Opens) (hU : ⨆ i, U i = ⊤)
    (T : _root_.GlobalTheory.Cris.Thick κ s) : ∃ (n : ℕ) (b : Fin n → T.B),
      Ideal.span (Set.range b) = ⊤ ∧
      ∀ (i : Fin n) (S : _root_.GlobalTheory.Cris.Thick κ s) (u : T ⟶ S),
        IsUnit (u.φ (b i)) → _root_.GlobalTheory.Cris.IsSmall κ s U S := by
  classical
  let G : Set T.B₀ := {f | ∃ k, ∀ p : PrimeSpectrum T.B₀,
    f ∉ p.asIdeal → T.x.base p ∈ U k}
  have hG : Ideal.span G = ⊤ := by
    by_contra h
    obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ h
    let p : PrimeSpectrum T.B₀ := ⟨m, hm.isPrime⟩
    have hp : T.x.base p ∈ (⨆ i, U i : X.Opens) := by rw [hU]; trivial
    obtain ⟨k, hk⟩ := (TopologicalSpace.Opens.mem_iSup).1 hp
    obtain ⟨_, ⟨f, rfl⟩, hpf, hsub⟩ :=
      PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open
        (a := p) (u := (fun q : PrimeSpectrum T.B₀ ↦ T.x.base q) ⁻¹' (U k))
        hk ((U k).isOpen.preimage T.x.continuous)
    exact hpf (hle (Ideal.subset_span ⟨k, fun q hq ↦ hsub hq⟩))
  obtain ⟨t, htG, htspan⟩ := (Ideal.span_eq_top_iff_finite G).1 hG
  let e := t.equivFin
  have hlift : ∀ i : Fin t.card, ∃ y, T.π y = (e.symm i : T.B₀) :=
    fun i ↦ T.surj _
  choose b hb using hlift
  refine ⟨t.card, b, ?_, ?_⟩
  · have hmap : Ideal.map T.π (Ideal.span (Set.range b)) = ⊤ := by
      rw [Ideal.map_span, ← htspan]
      congr 1
      ext f
      constructor
      · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
        rw [hb]
        exact (e.symm i).2
      · intro hf
        exact ⟨b (e ⟨f, hf⟩), ⟨_, rfl⟩, by rw [hb, Equiv.symm_apply_apply]⟩
    obtain ⟨y, hy, hy1⟩ := (Ideal.mem_map_iff_of_surjective _ T.surj).1
      (hmap ▸ Submodule.mem_top : (1 : T.B₀) ∈ _)
    have hJ : 1 - y ∈ T.J := by
      rw [← T.ker, map_sub, map_one, hy1, sub_self]
    have hunit : IsUnit y := by
      have := (isNilpotent_of_mem_of_isNilDP _ T.nil hJ).isUnit_one_sub
      simpa using this
    exact Ideal.eq_top_of_isUnit_mem _ hy hunit
  · intro i S u hu
    obtain ⟨k, hk⟩ := htG (e.symm i).2
    refine ⟨k, fun q _ ↦ ?_⟩
    show S.x.base q ∈ U k
    rw [← u.pt, Scheme.Hom.comp_apply]
    apply hk
    intro hq
    have h1 : u.φ₀ (e.symm i : T.B₀) ∈ q.asIdeal := hq
    rw [← hb, u.comm] at h1
    exact q.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ h1 (hu.map S.π))

end GlobalTheory.Cris
