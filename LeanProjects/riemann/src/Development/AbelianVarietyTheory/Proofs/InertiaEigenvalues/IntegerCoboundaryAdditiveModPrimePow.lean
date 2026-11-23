import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NoTowerQ

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram

namespace GlobalTheory.PMon.Ram

theorem int_dvd_of_eq_pow_mul {R : Type} [CommRing R] [IsDomain R] {p : ℕ} (hp : p.Prime)
    (hu : ¬ IsUnit (p : R)) (h0 : (p : R) ≠ 0) :
    ∀ (r : ℕ) (m : ℤ) (w : R), (m : R) = (p : R) ^ r * w → (p : ℤ) ^ r ∣ m := by
  intro r
  induction r with
  | zero => intro m w _; simp
  | succ r ih =>
    intro m w hm
    have hpm : (p : ℤ) ∣ m := by
      by_contra hnd
      have hcop : IsCoprime (p : ℤ) m :=
        (Irreducible.coprime_iff_not_dvd (Nat.prime_iff_prime_int.mp hp).irreducible).mpr hnd
      obtain ⟨u, v, huv⟩ := hcop
      apply hu
      have h1 : ((u * p + v * m : ℤ) : R) = 1 := by rw [huv]; simp
      push_cast at h1
      rw [hm] at h1
      refine isUnit_iff_exists_inv.mpr ⟨u + v * (p : R) ^ r * w, ?_⟩
      rw [← h1]; ring
    obtain ⟨m', rfl⟩ := hpm
    have hm' : (m' : R) = (p : R) ^ r * w := by
      push_cast at hm
      apply mul_left_cancel₀ h0
      rw [hm]; ring
    rw [pow_succ, mul_comm ((p : ℤ) ^ r)]
    exact mul_dvd_mul_left _ (ih m' w hm')

theorem coboundary_int_additive_mod : ∀ (K L : Type) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L] [IsGalois K L] (p E r : ℕ) (A : Subgroup (L ≃ₐ[K] L)) (x : L) (a : (L ≃ₐ[K] L) → ℤ), p.Prime → 0 < E → OrdIs L p E → (∀ σ ∈ A, ∃ z ∈ 𝒪[L], σ x - x = (a σ : L) + (p : L) ^ r * z) → ∀ σ ∈ A, ∀ τ ∈ A, (p : ℤ) ^ r ∣ a (σ * τ) - a σ - a τ := by
  intro K L _ _ _ _ _ _ _ _ _ _ _ _ p E r A x a hp hE hord hx σ hσ τ hτ
  obtain ⟨zσ, hzσ, eσ⟩ := hx σ hσ
  obtain ⟨zτ, hzτ, eτ⟩ := hx τ hτ
  obtain ⟨zστ, hzστ, eστ⟩ := hx (σ * τ) (A.mul_mem hσ hτ)
  have hσz : σ zτ ∈ 𝒪[L] := by
    have := (integerAlgEquiv K L σ ⟨zτ, hzτ⟩).2
    simpa using this
  let w : 𝒪[L] := ⟨σ zτ + zσ - zστ, Subring.sub_mem _ (Subring.add_mem _ hσz hzσ) hzστ⟩
  have hmul : (σ * τ) x - x = σ (τ x - x) + (σ x - x) := by
    rw [AlgEquiv.mul_apply, map_sub]; ring
  have hστ : σ (τ x - x) = (a τ : L) + (p : L) ^ r * σ zτ := by
    rw [eτ, map_add, map_mul, map_pow, map_intCast, map_natCast]
  have key : (((a (σ * τ) - a σ - a τ : ℤ)) : 𝒪[L]) = (p : 𝒪[L]) ^ r * w := by
    apply Subtype.ext
    simp only [w, Subring.coe_mul, Subring.coe_pow, Subring.coe_natCast, Subring.coe_intCast]
    push_cast
    rw [hmul, hστ, eσ] at eστ
    linear_combination -eστ
  have hu : ¬ IsUnit (p : 𝒪[L]) := by
    rintro ⟨u, hu⟩
    have h := IsDiscreteValuationRing.addVal_eq_zero_of_unit (R := 𝒪[L]) u
    unfold OrdIs at hord
    rw [hu, hord] at h
    have : E = 0 := by exact_mod_cast h
    omega
  have h0 : (p : 𝒪[L]) ≠ 0 := by
    intro h
    unfold OrdIs at hord
    rw [h, IsDiscreteValuationRing.addVal_zero] at hord
    exact ENat.top_ne_coe E hord
  exact int_dvd_of_eq_pow_mul hp hu h0 r _ w key

end GlobalTheory.PMon.Ram
