import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsMulVal
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField WithConv
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.PerfdLat GlobalTheory.GroupBplus GlobalTheory.GroupBplus.Aff
open Coalgebra Bialgebra
open GlobalTheory.DeRham (spOver spOver_comp)
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.exists_element_eval_eq_const_mul_of_finite_points : ∀ (R K : Type) [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K] (A : Type) [CommRing A] [Algebra R A] [Finite (A →ₐ[R] K)] (f : (A →ₐ[R] K) → K), ∃ (r : R) (a : A), r ≠ 0 ∧ ∀ ψ : A →ₐ[R] K, ψ a = algebraMap R K r * f ψ := by
  classical
  intro R K _ _ _ _ _ A _ _ _ f
  haveI : Fintype (A →ₐ[R] K) := Fintype.ofFinite _

  have hsep : ∀ ψ ψ' : A →ₐ[R] K, ∃ b : A, ψ ≠ ψ' → (ψ' b = 0 ∧ ψ b ≠ 0) := by
    intro ψ ψ'
    by_cases h : ψ = ψ'
    · exact ⟨0, fun h' => absurd h h'⟩
    · obtain ⟨a, ha⟩ : ∃ a, ψ a ≠ ψ' a := by
        by_contra hc
        push_neg at hc
        exact h (AlgHom.ext hc)
      obtain ⟨⟨n, d⟩, hnd⟩ := IsLocalization.surj (nonZeroDivisors R) (ψ' a)
      refine ⟨(d : R) • a - algebraMap R A n, fun _ => ⟨?_, ?_⟩⟩
      · simp only [map_sub, Algebra.smul_def, map_mul, AlgHom.commutes]
        simp only at hnd
        rw [mul_comm] at hnd
        rw [hnd, sub_self]
      · simp only [map_sub, Algebra.smul_def, map_mul, AlgHom.commutes]
        simp only at hnd
        have hd : algebraMap R K d ≠ 0 :=
          IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors d.2
        rw [← hnd, mul_comm (ψ' a), ← mul_sub]
        exact mul_ne_zero hd (sub_ne_zero.mpr ha)
  choose b hb using hsep
  let e : (A →ₐ[R] K) → A := fun ψ => ∏ ψ' ∈ Finset.univ.erase ψ, b ψ ψ'
  have he1 : ∀ ψ : A →ₐ[R] K, ψ (e ψ) ≠ 0 := by
    intro ψ
    simp only [e, map_prod]
    rw [Finset.prod_ne_zero_iff]
    intro ψ' hψ'
    exact (hb ψ ψ' (Finset.ne_of_mem_erase hψ').symm).2
  have he0 : ∀ ψ ψ' : A →ₐ[R] K, ψ' ≠ ψ → ψ' (e ψ) = 0 := by
    intro ψ ψ' hne
    simp only [e, map_prod]
    exact Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hne, Finset.mem_univ _⟩)
      (hb ψ ψ' hne.symm).1
  obtain ⟨c, hc⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors R) Finset.univ
    (fun ψ => f ψ / ψ (e ψ))
  choose m hm using fun ψ => hc ψ (Finset.mem_univ _)
  refine ⟨c, ∑ ψ, m ψ • e ψ, nonZeroDivisors.ne_zero c.2, fun ψ0 => ?_⟩
  rw [map_sum, Finset.sum_eq_single ψ0]
  · rw [map_smul, Algebra.smul_def, hm ψ0, Algebra.smul_def]
    rw [_root_.mul_assoc, div_mul_cancel₀ _ (he1 ψ0)]
  · intro ψ _ hne
    rw [map_smul, he0 ψ ψ0 (Ne.symm hne), smul_zero]
  · intro h; exact absurd (Finset.mem_univ _) h
