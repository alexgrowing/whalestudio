import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.TcoMem
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FibFiniteAndSep

open GlobalTheory GlobalTheory.PD

set_option autoImplicit false

noncomputable section

namespace UpperTheory

end UpperTheory

theorem UpperTheory.finite_fiber_of_finiteType_parameter_ring :
    ∀ (F K : Type) [Field F] [Field K] [Algebra ℂ F] [Algebra ℂ K] [Algebra F K] [IsScalarTower ℂ F K]
      (d : ℕ) (x : Fin (d + 1) → F), IsPd ℂ x → Algebra.FiniteType ℂ (rB ℂ K x {0}) →
      Finite (fib ℂ K x) := by
  intro F K _ _ _ _ _ _ d x hx hft
  classical
  have hmem : ∀ c : rA ℂ x {0}, algebraMap F K (c : F) ∈ rB ℂ K x {0} := by
    intro c
    show algebraMap F K (c : F) ∈ (integralClosure (rA ℂ x {0}) K).restrictScalars ℂ
    rw [Subalgebra.mem_restrictScalars, mem_integralClosure_iff]
    exact isIntegral_algebraMap (x := c)
  let ι : rA ℂ x {0} →ₐ[ℂ] rB ℂ K x {0} :=
    ((IsScalarTower.toAlgHom ℂ F K).comp (rA ℂ x {0}).val).codRestrict _ hmem
  have key : ∀ e1 e2 : fib ℂ K x, ∀ c : rA ℂ x {0}, e1.1 (ι c) = e2.1 (ι c) := by
    intro e1 e2 c
    obtain ⟨c, hc⟩ := c
    induction hc using Algebra.adjoin_induction with
    | mem y hy =>
      obtain ⟨i, hi, j, rfl⟩ := hy
      rw [Finset.mem_singleton] at hi
      subst hi
      rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j', rfl⟩
      · have h3 : ∀ (e : fib ℂ K x) (h : x 0 / x 0 ∈ rA ℂ x {0}), e.1 (ι ⟨x 0 / x 0, h⟩) = 1 := by
          intro e h
          have h1 : (⟨x 0 / x 0, h⟩ : rA ℂ x {0}) = 1 := Subtype.ext (div_self (hx.ne 0))
          rw [h1, map_one, map_one]
        exact (h3 e1 _).trans (h3 e2 _).symm
      · exact (e1.2 j').trans (e2.2 j').symm
    | algebraMap r =>
      show e1.1 (ι (algebraMap ℂ (rA ℂ x {0}) r)) = e2.1 (ι (algebraMap ℂ (rA ℂ x {0}) r))
      simp only [AlgHom.commutes]
    | add y z hy hz ihy ihz =>
      show e1.1 (ι (⟨y, hy⟩ + ⟨z, hz⟩)) = e2.1 (ι (⟨y, hy⟩ + ⟨z, hz⟩))
      simp only [map_add, ihy, ihz]
    | mul y z hy hz ihy ihz =>
      show e1.1 (ι (⟨y, hy⟩ * ⟨z, hz⟩)) = e2.1 (ι (⟨y, hy⟩ * ⟨z, hz⟩))
      simp only [map_mul, ihy, ihz]
  rcases isEmpty_or_nonempty (fib ℂ K x) with hE | hE
  · infer_instance
  obtain ⟨e0⟩ := hE
  obtain ⟨s, hs⟩ := hft.out
  let ψ : rA ℂ x {0} →+* ℂ := (e0.1.comp ι).toRingHom
  have hint : ∀ b : rB ℂ K x {0}, IsIntegral (rA ℂ x {0}) (b : K) := fun b => b.2
  let R : rB ℂ K x {0} → Finset ℂ := fun b => (((hint b).choose).map ψ).roots.toFinset
  have hR : ∀ (e : fib ℂ K x) (b : rB ℂ K x {0}), e.1 b ∈ R b := by
    intro e b
    obtain ⟨hm, hp⟩ := (hint b).choose_spec
    have h0 : Polynomial.eval₂ (ι : rA ℂ x {0} →+* rB ℂ K x {0}) b (hint b).choose = 0 := by
      apply Subtype.ext
      have := Polynomial.hom_eval₂ (hint b).choose (ι : rA ℂ x {0} →+* rB ℂ K x {0})
        (rB ℂ K x {0}).val.toRingHom b
      refine this.trans ?_
      rw [Subalgebra.coe_zero]
      exact hp
    have h1 := Polynomial.hom_eval₂ (hint b).choose (ι : rA ℂ x {0} →+* rB ℂ K x {0}) e.1.toRingHom b
    rw [h0, map_zero] at h1
    have h2 : e.1.toRingHom.comp (ι : rA ℂ x {0} →+* rB ℂ K x {0}) = ψ :=
      RingHom.ext fun c => key e e0 c
    rw [h2] at h1
    have hne : ((hint b).choose.map ψ) ≠ 0 := (hm.map ψ).ne_zero
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hne, Polynomial.IsRoot, Polynomial.eval_map]
    exact h1.symm
  let Φ : fib ℂ K x → ((t : s) → (R t : Set ℂ)) := fun e t => ⟨e.1 t, hR e t⟩
  apply Finite.of_injective Φ
  intro e1 e2 h
  apply Subtype.ext
  apply AlgHom.ext_of_adjoin_eq_top hs
  intro t ht
  have := congrFun h ⟨t, ht⟩
  exact congrArg Subtype.val this
