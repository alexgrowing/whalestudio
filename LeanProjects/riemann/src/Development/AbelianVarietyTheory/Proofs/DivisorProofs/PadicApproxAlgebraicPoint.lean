import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgClosedDenseInCpStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PAdicAlgebraicApproximationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolynomialSystemSpecializationStatement
open Polynomial

namespace GlobalTheory.AlgPointsDense

theorem exists_algebraic_approx : ∀ (K : Type) [Field K] [NumberField K] (R : Type) [CommRing R] [Algebra K R] [Algebra.FiniteType K R] (p : ℕ) [Fact p.Prime] (ε : R →+* ℂ_[p]) (s : Finset R) (η : ℝ), 0 < η → ∃ (ι : AlgebraicClosure K →+* ℂ_[p]) (φ : R →ₐ[K] AlgebraicClosure K), ∀ h ∈ s, ‖ι (φ h) - ε h‖ < η := by
  intro K _ _ R _ _ _ p _ ε s η hη
  letI : Algebra K ℂ_[p] := (ε.comp (algebraMap K R)).toAlgebra
  let ε' : R →ₐ[K] ℂ_[p] := { ε with commutes' := fun c => rfl }
  let ι₀ : AlgebraicClosure K →ₐ[K] ℂ_[p] := IsAlgClosed.lift
  have hc : (ι₀ : AlgebraicClosure K →+* ℂ_[p]).comp (algebraMap K _) = algebraMap K ℂ_[p] := by
    ext c; exact ι₀.commutes c
  have hdense := GlobalTheory.T.algClosed_dense_in_Cp p (AlgebraicClosure K) (ι₀ : AlgebraicClosure K →+* ℂ_[p])
  classical
  obtain ⟨s0, hs0⟩ := Algebra.FiniteType.out (R := K) (A := R)
  let S : Finset R := s0 ∪ s
  let e : Fin S.card ≃ S := S.equivFin.symm
  let a : Fin S.card → ℂ_[p] := fun j => ε (e j)
  obtain ⟨d, t, θ, P, Δ, Q, hPm, hPθ, hΔ, hQ, huniv⟩ := GlobalTheory.T.polynomial_system_specialization K ℂ_[p] S.card a
  obtain ⟨t', θ', hΔ', hP', hclose⟩ := GlobalTheory.T.p_adic_algebraic_approximation p K (AlgebraicClosure K)
    (ι₀ : AlgebraicClosure K →+* ℂ_[p]) hdense hc d S.card t θ P Δ Q η hη hPm hPθ hΔ
  obtain ⟨f, hf⟩ := huniv (AlgebraicClosure K) t' θ' hΔ' hP'
  have hmem : ∀ r : R, ε' r ∈ Algebra.adjoin K (Set.range a) := by
    intro r
    have hr : r ∈ Algebra.adjoin K (s0 : Set R) := by rw [hs0]; trivial
    have h1 : ε' r ∈ (Algebra.adjoin K (s0 : Set R)).map ε' := Subalgebra.mem_map.2 ⟨r, hr, rfl⟩
    rw [← Algebra.adjoin_image] at h1
    refine Algebra.adjoin_mono ?_ h1
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨e.symm ⟨x, Finset.mem_union_left _ hx⟩, by simp [a, ε']⟩
  let g : R →ₐ[K] Algebra.adjoin K (Set.range a) := ε'.codRestrict _ hmem
  refine ⟨(ι₀ : AlgebraicClosure K →+* ℂ_[p]), f.comp g, ?_⟩
  intro h hh
  let j := e.symm ⟨h, Finset.mem_union_right _ hh⟩
  have haj : a j = ε h := by simp [a, j]
  have hg : g h = ⟨a j, Algebra.subset_adjoin (Set.mem_range_self j)⟩ :=
    Subtype.ext (show ε h = a j from haj.symm)
  have h1 : f (g h) = Polynomial.eval₂ (MvPolynomial.aeval t').toRingHom θ' (Q j) /
      MvPolynomial.aeval t' Δ := by
    rw [hg, hf j]; field_simp
  have h2 : ε h = Polynomial.eval₂ (MvPolynomial.aeval t).toRingHom θ (Q j) /
      MvPolynomial.aeval t Δ := by
    rw [← haj, hQ j]; field_simp
  have := hclose j
  rw [AlgHom.comp_apply, h1, map_div₀, h2]
  exact this

end GlobalTheory.AlgPointsDense
