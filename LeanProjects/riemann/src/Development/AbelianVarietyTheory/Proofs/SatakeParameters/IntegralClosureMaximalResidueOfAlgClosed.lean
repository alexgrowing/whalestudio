import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GalMapMul
open GlobalTheory.EtC

namespace GlobalTheory

theorem integralClosure_maximal_residue_algClosed : ∀ (k K : Type) [Field k] [IsAlgClosed k] [Field K] (φ : k →+* K) (D : Subring K) (m₀ : Ideal D),
    φ.range ≤ D → m₀.IsMaximal → (∀ r : D, ∃ c : k, ∃ h : φ c ∈ D, r - ⟨φ c, h⟩ ∈ m₀) →
    (∀ x : K, ∃ d : D, d ≠ 0 ∧ IsIntegral D ((d : K) * x)) →
    ∃ (R : Subring K) (𝔪 : Ideal R), φ.range ≤ R ∧ 𝔪.IsMaximal ∧ (∀ r : R, ∃ c : k, ∃ h : φ c ∈ R, r - ⟨φ c, h⟩ ∈ 𝔪) ∧
      (∀ x : K, ∃ d : R, d ≠ 0 ∧ (d : K) * x ∈ R) ∧ ∀ x : K, IsIntegral R x → x ∈ R := by
  intro k K _ _ _ φ D m₀ hφD hm₀ hres hfrac
  let A := integralClosure D K
  have hφA : ∀ c : k, φ c ∈ A := fun c =>
    isIntegral_algebraMap (R := D) (x := (⟨φ c, hφD ⟨c, rfl⟩⟩ : D))
  have hker : RingHom.ker (algebraMap D A) ≤ m₀ := by
    intro d hd
    have h0 : (algebraMap D A d : K) = 0 := by rw [RingHom.mem_ker.mp hd]; rfl
    have : d = 0 := Subtype.ext h0
    simp [this]
  obtain ⟨𝔪, h𝔪max, h𝔪comap⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := A) m₀ hker
  let φA : k →+* A := φ.codRestrict A hφA
  let ψ : k →+* A ⧸ 𝔪 := (Ideal.Quotient.mk 𝔪).comp φA
  have hcoef : ∀ d : D, algebraMap D (A ⧸ 𝔪) d ∈ Set.range ψ := by
    intro d
    obtain ⟨c, hc, hdc⟩ := hres d
    refine ⟨c, ?_⟩
    have hmem : algebraMap D A (d - ⟨φ c, hc⟩) ∈ 𝔪 := by
      rw [← Ideal.mem_comap, h𝔪comap]; exact hdc
    change Ideal.Quotient.mk 𝔪 (φA c) = Ideal.Quotient.mk 𝔪 (algebraMap D A d)
    symm
    rw [map_sub] at hmem
    exact Ideal.Quotient.eq.mpr hmem
  have hres' : ∀ r : A, ∃ c : k, r - φA c ∈ 𝔪 := by
    intro r
    letI : Field (A ⧸ 𝔪) := Ideal.Quotient.field 𝔪
    letI : Algebra k (A ⧸ 𝔪) := ψ.toAlgebra
    have hr : IsIntegral D (Ideal.Quotient.mkₐ D 𝔪 r) :=
      (Algebra.IsIntegral.isIntegral (R := D) r).map (Ideal.Quotient.mkₐ D 𝔪)
    obtain ⟨f, hfm, hf⟩ := hr
    have hlift : f.map (algebraMap D (A ⧸ 𝔪)) ∈ Polynomial.lifts ψ := by
      rw [Polynomial.lifts_iff_coeff_lifts]
      intro n; rw [Polynomial.coeff_map]; exact hcoef _
    obtain ⟨q, hq, -, hqm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hlift (hfm.map _)
    have hint : IsIntegral k (Ideal.Quotient.mk 𝔪 r) := by
      refine ⟨q, hqm, ?_⟩
      rw [Polynomial.eval₂_eq_eval_map]
      change Polynomial.eval _ (q.map ψ) = 0
      rw [hq, ← Polynomial.eval₂_eq_eval_map]
      exact hf
    have h1 := IsAlgClosed.degree_eq_one_of_irreducible k (minpoly.irreducible hint)
    obtain ⟨c, hc⟩ := minpoly.mem_range_of_degree_eq_one k _ h1
    exact ⟨c, Ideal.Quotient.eq.mp hc.symm⟩
  refine ⟨A.toSubring, 𝔪, ?_, h𝔪max, ?_, ?_, ?_⟩
  · rintro _ ⟨c, rfl⟩; exact hφA c
  · intro r
    obtain ⟨c, hc⟩ := hres' r
    exact ⟨c, hφA c, hc⟩
  · intro x
    obtain ⟨d, hd, hint⟩ := hfrac x
    refine ⟨⟨(d : K), Subalgebra.algebraMap_mem A d⟩, ?_, hint⟩
    intro h
    apply hd
    exact Subtype.ext (by simpa using congrArg Subtype.val h)
  · intro x hx
    have hx' : IsIntegral A x := hx
    exact isIntegral_trans x hx'

end GlobalTheory
