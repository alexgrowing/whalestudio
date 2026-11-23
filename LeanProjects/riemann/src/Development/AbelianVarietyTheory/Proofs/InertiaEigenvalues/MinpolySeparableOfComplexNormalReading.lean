import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.OffRange

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.IntegralHeckeForms Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial GlobalTheory.LiftLeaf GlobalTheory.SupLaw
open scoped TensorProduct

namespace GlobalTheory.NormalSeparable

section SlopeTestRemainingChoices
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem aeval_mem (U : Submodule ℂ H) (S : Module.End ℂ H) (hS : ∀ u ∈ U, S u ∈ U)
    (q : Polynomial ℂ) : ∀ u ∈ U, Polynomial.aeval S q u ∈ U := by
  refine Polynomial.induction_on q ?_ ?_ ?_
  · intro a u hu
    simpa [Module.algebraMap_end_apply] using U.smul_mem a hu
  · intro p r hp hr u hu
    simpa using U.add_mem (hp u hu) (hr u hu)
  · intro n a ih u hu
    rw [pow_succ, ← mul_assoc, map_mul, Polynomial.aeval_X, Module.End.mul_apply]
    exact ih _ (hS u hu)

theorem aeval_adj (U : Submodule ℂ H) (S S' : Module.End ℂ H) (hS : ∀ u ∈ U, S u ∈ U)
    (hadj : ∀ u ∈ U, ∀ v ∈ U, inner ℂ (S u) v = inner ℂ u (S' v)) (hS' : ∀ u ∈ U, S' u ∈ U)
    (q : Polynomial ℂ) : ∀ u ∈ U, ∀ v ∈ U, inner ℂ (Polynomial.aeval S q u) v
      = inner ℂ u (Polynomial.aeval S' (q.map (starRingEnd ℂ)) v) := by
  refine Polynomial.induction_on q ?_ ?_ ?_
  · intro a u hu v hv
    simp [Module.algebraMap_end_apply, inner_smul_left, inner_smul_right, mul_comm]
  · intro p r hp hr u hu v hv
    simp only [map_add, Polynomial.map_add, LinearMap.add_apply, inner_add_left, inner_add_right,
      hp u hu v hv, hr u hu v hv]
  · intro n a ih u hu v hv
    have e : (Polynomial.C a * Polynomial.X ^ (n + 1) : Polynomial ℂ)
        = Polynomial.C a * Polynomial.X ^ n * Polynomial.X := by ring
    rw [e]
    generalize Polynomial.C a * Polynomial.X ^ n = p at ih ⊢
    have e2 : (p * Polynomial.X).map (starRingEnd ℂ) = Polynomial.X * p.map (starRingEnd ℂ) := by
      rw [Polynomial.map_mul, Polynomial.map_X, mul_comm]
    rw [e2, map_mul, Polynomial.aeval_X, Module.End.mul_apply, map_mul, Polynomial.aeval_X,
      Module.End.mul_apply, ih _ (hS u hu) v hv]
    exact hadj u hu _ (GlobalTheory.NormalSeparable.aeval_mem U S' hS' _ v hv)

theorem aeval_comm (U : Submodule ℂ H) (S B : Module.End ℂ H) (hS : ∀ u ∈ U, S u ∈ U)
    (hc : ∀ u ∈ U, S (B u) = B (S u)) (q : Polynomial ℂ) :
    ∀ u ∈ U, Polynomial.aeval S q (B u) = B (Polynomial.aeval S q u) := by
  refine Polynomial.induction_on q ?_ ?_ ?_
  · intro a u hu
    simp [Module.algebraMap_end_apply]
  · intro p r hp hr u hu
    simp only [map_add, LinearMap.add_apply, hp u hu, hr u hu]
  · intro n a ih u hu
    rw [pow_succ, ← mul_assoc, map_mul, Polynomial.aeval_X]
    simp only [Module.End.mul_apply]
    rw [hc u hu, ih _ (hS u hu)]

theorem normal_sq_zero (U : Submodule ℂ H) (A A' : Module.End ℂ H) (hA : ∀ u ∈ U, A u ∈ U)
    (hA' : ∀ u ∈ U, A' u ∈ U)
    (hadj : ∀ u ∈ U, ∀ v ∈ U, inner ℂ (A u) v = inner ℂ u (A' v))
    (hc : ∀ u ∈ U, A (A' u) = A' (A u)) (u : H) (hu : u ∈ U) (h : A (A u) = 0) : A u = 0 := by
  have hw : A u ∈ U := hA u hu
  have h1 : A' (A u) = 0 := by
    have h2 : inner ℂ (A' (A u)) (A' (A u)) = 0 := by
      rw [← hadj _ (hA' _ hw) _ hw, hc _ hw, h, map_zero, inner_zero_left]
    exact inner_self_eq_zero.mp h2
  have h3 : inner ℂ (A u) (A u) = 0 := by
    rw [hadj _ hu _ hw, h1, inner_zero_right]
  exact inner_self_eq_zero.mp h3

end SlopeTestRemainingChoices

theorem minpoly_separable_of_normal : ∀ (K V H : Type) [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [NormedAddCommGroup H] [InnerProductSpace ℂ H] (φ : K →+* ℂ) (j : V →ₛₗ[φ] H) (T : Module.End K V) (S S' : Module.End ℂ H), (∀ (n : ℕ) (x : Fin n → V), LinearIndependent K x → LinearIndependent ℂ (fun a => j (x a))) → (∀ x, j (T x) = S (j x)) → (∀ u ∈ Submodule.span ℂ (Set.range j), S' u ∈ Submodule.span ℂ (Set.range j)) → (∀ u ∈ Submodule.span ℂ (Set.range j), ∀ v ∈ Submodule.span ℂ (Set.range j), inner ℂ (S u) v = inner ℂ u (S' v)) → (∀ u ∈ Submodule.span ℂ (Set.range j), S (S' u) = S' (S u)) → (minpoly K T).Separable := by
  intro K V H _ _ _ _ _ _ φ j T S S' hlin hT hS' hadj hc
  haveI : CharZero K := φ.charZero
  set U : Submodule ℂ H := Submodule.span ℂ (Set.range j) with hU
  have hjU : ∀ x, j x ∈ U := fun x => Submodule.subset_span ⟨x, rfl⟩
  have hSU : ∀ u ∈ U, S u ∈ U := by
    have hle : U ≤ U.comap S := by
      rw [hU, Submodule.span_le]
      rintro _ ⟨x, rfl⟩
      rw [SetLike.mem_coe, Submodule.mem_comap, ← hT x]
      exact Submodule.subset_span ⟨T x, rfl⟩
    intro u hu
    exact hle hu
  have hinj : ∀ v : V, j v = 0 → v = 0 := by
    intro v hv
    by_contra hne
    have hli : LinearIndependent K (fun _ : Fin 1 => v) := by
      rw [Fintype.linearIndependent_iff]
      intro g hg i
      obtain rfl : i = 0 := Subsingleton.elim _ _
      simp only [Fin.sum_univ_one] at hg
      exact (smul_eq_zero.mp hg).resolve_right hne
    have h1 := hlin 1 (fun _ => v) hli
    exact h1.ne_zero 0 (by simpa using hv)
  have htr : ∀ (p : Polynomial K) (x : V),
      j (Polynomial.aeval T p x) = Polynomial.aeval S (p.map φ) (j x) := by
    intro p
    refine Polynomial.induction_on p ?_ ?_ ?_
    · intro a x
      simp [Module.algebraMap_end_apply]
    · intro p r hp hr x
      simp only [map_add, Polynomial.map_add, LinearMap.add_apply, hp, hr]
    · intro n a ih x
      have e : (Polynomial.C a * Polynomial.X ^ (n + 1) : Polynomial K)
          = Polynomial.C a * Polynomial.X ^ n * Polynomial.X := by ring
      rw [e]
      generalize Polynomial.C a * Polynomial.X ^ n = p at ih ⊢
      rw [map_mul, Polynomial.aeval_X, Module.End.mul_apply, ih, Polynomial.map_mul,
        Polynomial.map_X, map_mul, Polynomial.aeval_X, Module.End.mul_apply, hT]
  have hsq : Squarefree (minpoly K T) := by
    intro q hq
    obtain ⟨r, hr⟩ := hq
    have hp0 : minpoly K T ≠ 0 := minpoly.ne_zero (Algebra.IsIntegral.isIntegral T)
    have hann : Polynomial.aeval T (q * r) = 0 := by
      apply LinearMap.ext
      intro x
      rw [LinearMap.zero_apply]
      apply hinj
      have e1 : Polynomial.aeval T (q * r) x = Polynomial.aeval T q (Polynomial.aeval T r x) := by
        rw [map_mul, Module.End.mul_apply]
      rw [e1, htr]
      have h0 : Polynomial.aeval T q (Polynomial.aeval T q (Polynomial.aeval T r x)) = 0 := by
        have h4 : Polynomial.aeval T (q * q * r) x = 0 := by
          rw [← hr, minpoly.aeval, LinearMap.zero_apply]
        simpa only [map_mul, Module.End.mul_apply] using h4
      have h0' : Polynomial.aeval S (q.map φ)
          (Polynomial.aeval S (q.map φ) (j (Polynomial.aeval T r x))) = 0 := by
        rw [← htr, ← htr, h0, map_zero]
      have hcomm1 : ∀ u ∈ U, Polynomial.aeval S (q.map φ) (S' u)
          = S' (Polynomial.aeval S (q.map φ) u) :=
        GlobalTheory.NormalSeparable.aeval_comm U S S' hSU hc (q.map φ)
      have hcomm2 := GlobalTheory.NormalSeparable.aeval_comm U S' (Polynomial.aeval S (q.map φ)) hS'
        (fun u hu => (hcomm1 u hu).symm) ((q.map φ).map (starRingEnd ℂ))
      exact GlobalTheory.NormalSeparable.normal_sq_zero U (Polynomial.aeval S (q.map φ))
        (Polynomial.aeval S' ((q.map φ).map (starRingEnd ℂ)))
        (GlobalTheory.NormalSeparable.aeval_mem U S hSU _) (GlobalTheory.NormalSeparable.aeval_mem U S' hS' _)
        (GlobalTheory.NormalSeparable.aeval_adj U S S' hSU hadj hS' _) (fun u hu => (hcomm2 u hu).symm)
        (j (Polynomial.aeval T r x)) (hjU _) h0'
    have hdvd : minpoly K T ∣ q * r := minpoly.dvd K T hann
    rw [hr] at hdvd
    have hqr : q * r ≠ 0 := by
      intro h
      apply hp0
      rw [hr, mul_assoc, h, mul_zero]
    have h5 : q * (q * r) ∣ 1 * (q * r) := by rwa [one_mul, ← mul_assoc]
    exact isUnit_of_dvd_one ((mul_dvd_mul_iff_right hqr).mp h5)
  exact PerfectField.separable_iff_squarefree.mpr hsq

end GlobalTheory.NormalSeparable
