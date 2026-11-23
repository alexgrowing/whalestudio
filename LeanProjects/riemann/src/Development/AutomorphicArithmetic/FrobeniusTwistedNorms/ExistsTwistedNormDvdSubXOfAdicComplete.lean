import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.FrobeniusTwistedHilbertNinetyAlt
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.NormAdic

open Polynomial

private theorem UpperTheory.adjoinRoot_ringEquiv_of_invariant (O : Type) [CommRing O] (σ : O ≃+* O) (f : O[X])
    (hf : f.map (σ : O →+* O) = f) :
    ∃ τ : AdjoinRoot f ≃+* AdjoinRoot f, ∀ g : O[X],
      τ (AdjoinRoot.mk f g) = AdjoinRoot.mk f (g.map (σ : O →+* O)) := by
  refine ⟨AdjoinRoot.mapRingEquiv σ f f (by rw [hf]), fun g => ?_⟩
  simp [AdjoinRoot.mapRingEquiv, AdjoinRoot.map]
  rw [← AdjoinRoot.aeval_eq, Polynomial.aeval_def, Polynomial.eval₂_map]
  rfl

private theorem polynomial_map_one (O : Type) [CommRing O] (q : Polynomial O) :
    q.map (1 : O →+* O) = q :=
  Polynomial.map_id

theorem UpperTheory.exists_twistedNorm_dvd_sub_X_of_adicComplete :
    ∀ (O : Type) [CommRing O] (m : Ideal O) (σ : O ≃+* O) (d : ℕ) (f : O[X]) [IsAdicComplete (m.map (AdjoinRoot.of f)) (AdjoinRoot f)], (∀ x, σ^[d] x = x) → (∀ x ∈ m, σ x ∈ m) → ∀ a : O, ∑ i ∈ Finset.range d, σ^[i] a = 1 → f.map (σ : O →+* O) = f → IsUnit (f.coeff 0) → ∀ g : O[X], AdjoinRoot.mk f (∏ i ∈ Finset.range d, g.map ((σ : O →+* O) ^ i) - X) ∈ m.map (AdjoinRoot.of f) → ∃ p : O[X], f ∣ ∏ i ∈ Finset.range d, p.map ((σ : O →+* O) ^ i) - X := by
  intro O _ m σ d f _ hd hm a ha hf hc0 g hg
  obtain ⟨τ, hτ⟩ := UpperTheory.adjoinRoot_ringEquiv_of_invariant O σ f hf
  have hit : ∀ (i : ℕ) (q : O[X]),
      (⇑τ)^[i] (AdjoinRoot.mk f q) = AdjoinRoot.mk f (q.map ((σ : O →+* O) ^ i)) := by
    intro i
    induction i with
    | zero => intro q; rw [pow_zero, Function.iterate_zero_apply, polynomial_map_one]
    | succ i ih =>
      intro q
      rw [Function.iterate_succ_apply', ih, hτ, Polynomial.map_map, pow_succ']
      rfl
  have hof : ∀ b : O, τ (AdjoinRoot.of f b) = AdjoinRoot.of f (σ b) := by
    intro b
    have := hτ (Polynomial.C b)
    simpa [AdjoinRoot.mk_C] using this
  have hofit : ∀ (i : ℕ) (b : O), (⇑τ)^[i] (AdjoinRoot.of f b) = AdjoinRoot.of f ((⇑σ)^[i] b) := by
    intro i
    induction i with
    | zero => intro b; rfl
    | succ i ih => intro b; rw [Function.iterate_succ_apply', ih, hof, Function.iterate_succ_apply']
  have hd' : ∀ x, (⇑τ)^[d] x = x := by
    intro x
    obtain ⟨q, rfl⟩ := AdjoinRoot.mk_surjective x
    rw [hit]
    congr 1
    ext j
    rw [Polynomial.coeff_map, RingHom.coe_pow]
    exact hd _
  have hI : ∀ x ∈ m.map (AdjoinRoot.of f), τ x ∈ m.map (AdjoinRoot.of f) := by
    have : m.map (AdjoinRoot.of f) ≤ (m.map (AdjoinRoot.of f)).comap (τ : AdjoinRoot f →+* AdjoinRoot f) := by
      rw [Ideal.map_le_iff_le_comap]
      intro b hb
      show τ (AdjoinRoot.of f b) ∈ m.map (AdjoinRoot.of f)
      rw [hof]
      exact Ideal.mem_map_of_mem _ (hm b hb)
    exact fun x hx => this hx
  have ha' : ∑ i ∈ Finset.range d, (⇑τ)^[i] (AdjoinRoot.of f a) = 1 := by
    simp_rw [hofit]
    rw [← map_sum, ha, map_one]
  have hroot_fix : τ (AdjoinRoot.root f) = AdjoinRoot.root f := by
    have := hτ Polynomial.X
    simpa [AdjoinRoot.mk_X] using this
  have hunit : IsUnit (AdjoinRoot.root f) := by
    obtain ⟨q, hq⟩ := Polynomial.X_dvd_sub_C (p := f)
    have h1 := congrArg (AdjoinRoot.mk f) hq
    rw [map_sub, AdjoinRoot.mk_self, map_mul, AdjoinRoot.mk_X, AdjoinRoot.mk_C, zero_sub] at h1
    have h2 : AdjoinRoot.root f * (-(AdjoinRoot.mk f q)) = AdjoinRoot.of f (f.coeff 0) := by
      rw [mul_neg, ← h1, neg_neg]
    have h3 : IsUnit (AdjoinRoot.root f * (-(AdjoinRoot.mk f q))) := h2 ▸ hc0.map _
    exact isUnit_of_mul_isUnit_left h3
  have hgI : UpperTheory.Gal.InertialTypesAlt.L.itN τ d (AdjoinRoot.mk f g) - AdjoinRoot.root f ∈ m.map (AdjoinRoot.of f) := by
    have : AdjoinRoot.mk f (∏ i ∈ Finset.range d, g.map ((σ : O →+* O) ^ i) - Polynomial.X) =
        UpperTheory.Gal.InertialTypesAlt.L.itN τ d (AdjoinRoot.mk f g) - AdjoinRoot.root f := by
      rw [map_sub, map_prod, AdjoinRoot.mk_X, UpperTheory.Gal.InertialTypesAlt.L.itN]
      simp_rw [hit]
    rw [← this]
    exact hg
  obtain ⟨y', hy'⟩ := UpperTheory.Gal.InertialTypesAlt.L.normAdic (AdjoinRoot f) (m.map (AdjoinRoot.of f)) τ d hd' hI
    (AdjoinRoot.of f a) ha' (AdjoinRoot.root f) (AdjoinRoot.mk f g) hunit hroot_fix hgI
  obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective y'
  refine ⟨p, ?_⟩
  rw [← AdjoinRoot.mk_eq_zero, map_sub, map_prod, AdjoinRoot.mk_X]
  simp_rw [← hit]
  rw [← UpperTheory.Gal.InertialTypesAlt.L.itN, hy', sub_self]
