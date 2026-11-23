import Mathlib
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

theorem exists_rootsOfUnity_eval_ne_zero {s : ℕ} {c : MvPolynomial (Fin s) ℚ} (hc : c ≠ 0) :
    ∃ (N : ℕ) (y : Fin s → AlgebraicClosure ℚ), 0 < N ∧ (∀ j, y j ^ N = 1) ∧ aeval y c ≠ 0 := by
  classical
  set N := c.totalDegree + 1 with hN
  have hNpos : 0 < N := Nat.succ_pos _
  have : NeZero ((N : ℕ) : ℚ) := ⟨by exact_mod_cast hNpos.ne'⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (AlgebraicClosure ℚ) N
  set S := Polynomial.nthRootsFinset N (1 : AlgebraicClosure ℚ)
  have hS : S.card = N := hζ.card_nthRootsFinset
  set c' := MvPolynomial.map (algebraMap ℚ (AlgebraicClosure ℚ)) c
  have hc' : c' ≠ 0 := by
    intro h
    apply hc
    exact MvPolynomial.map_injective _ (algebraMap ℚ (AlgebraicClosure ℚ)).injective
      (h.trans (map_zero _).symm)
  by_contra hcon
  push Not at hcon
  apply hc'
  refine MvPolynomial.eq_zero_of_eval_zero_at_prod_finset c' (fun _ ↦ S) (fun i ↦ ?_) ?_
  · rw [hS]
    calc c'.degreeOf i = c.degreeOf i := by
          simp only [c', MvPolynomial.degreeOf_def,
            MvPolynomial.degrees_map_of_injective _ (algebraMap ℚ (AlgebraicClosure ℚ)).injective]
      _ ≤ c.totalDegree := MvPolynomial.degreeOf_le_totalDegree c i
      _ < N := Nat.lt_succ_self _
  · intro x hx
    have hx' : ∀ j, x j ^ N = 1 := fun j ↦ (Polynomial.mem_nthRootsFinset hNpos 1).mp (hx j)
    have := hcon N x hNpos hx'
    rw [MvPolynomial.eval_map]
    rw [MvPolynomial.aeval_def] at this
    exact this

theorem exists_algHom_rootsOfUnity_ne_zero {B : Type*} [CommRing B] [IsDomain B] [Algebra ℚ B]
    {s : ℕ} (g0 : MvPolynomial (Fin s) ℚ →ₐ[ℚ] B) (hinj : Function.Injective g0)
    (hint : g0.IsIntegral) {g : B} (hg : g ≠ 0) :
    ∃ ψ : B →ₐ[ℚ] AlgebraicClosure ℚ, ψ g ≠ 0 ∧
      ∀ j, ∃ N : ℕ, 0 < N ∧ ψ (g0 (MvPolynomial.X j)) ^ N = 1 := by
  classical
  let : Algebra (MvPolynomial (Fin s) ℚ) B := g0.toRingHom.toAlgebra
  have hmap : ∀ a, algebraMap (MvPolynomial (Fin s) ℚ) B a = g0 a := fun _ ↦ rfl
  have hInt : Algebra.IsIntegral (MvPolynomial (Fin s) ℚ) B := ⟨hint⟩

  have hI : (Ideal.span {g}).comap (algebraMap (MvPolynomial (Fin s) ℚ) B) ≠ ⊥ :=
    Ideal.comap_ne_bot_of_integral_mem hg (Ideal.mem_span_singleton_self g)
      (Algebra.IsIntegral.isIntegral g)
  obtain ⟨c, hcI, hc0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.mp (Ideal.mem_comap.mp hcI)

  obtain ⟨N, y, hNpos, hy, hcy⟩ := exists_rootsOfUnity_eval_ne_zero hc0
  set ev : MvPolynomial (Fin s) ℚ →+* AlgebraicClosure ℚ := (aeval y).toRingHom with hev
  have : (RingHom.ker ev).IsPrime := RingHom.ker_isPrime ev
  have hker : RingHom.ker (algebraMap (MvPolynomial (Fin s) ℚ) B) ≤ RingHom.ker ev := by
    intro a ha
    rw [RingHom.mem_ker, hmap] at ha
    have : a = 0 := hinj (ha.trans (map_zero g0).symm)
    rw [this]
    exact (RingHom.ker ev).zero_mem
  obtain ⟨Q, hQ, hQc⟩ := Ideal.exists_ideal_over_prime_of_isIntegral_of_isDomain (RingHom.ker ev) hker
  have := hQ
  set p := Q.comap (algebraMap (MvPolynomial (Fin s) ℚ) B) with hp
  have : p.IsPrime := Ideal.comap_isPrime _ Q

  have hvan : ∀ a ∈ p, ev a = 0 := fun a ha ↦ by
    rw [hQc] at ha
    exact RingHom.mem_ker.mp ha
  let evq : MvPolynomial (Fin s) ℚ ⧸ p →+* AlgebraicClosure ℚ := Ideal.Quotient.lift p ev hvan
  have hevq : Function.Injective evq :=
    RingHom.lift_injective_of_ker_le_ideal p hvan (by rw [hQc])
  let : Algebra (MvPolynomial (Fin s) ℚ ⧸ p) (AlgebraicClosure ℚ) := evq.toAlgebra
  have : Module.IsTorsionFree (MvPolynomial (Fin s) ℚ ⧸ p) (AlgebraicClosure ℚ) :=
    (Module.isTorsionFree_iff_algebraMap_injective).mpr hevq
  have : Module.IsTorsionFree (MvPolynomial (Fin s) ℚ ⧸ p) (B ⧸ Q) :=
    (Module.isTorsionFree_iff_algebraMap_injective).mpr Ideal.algebraMap_quotient_injective
  have : Algebra.IsIntegral (MvPolynomial (Fin s) ℚ ⧸ p) (B ⧸ Q) := Algebra.IsIntegral.quotient
  let ψq : (B ⧸ Q) →ₐ[MvPolynomial (Fin s) ℚ ⧸ p] AlgebraicClosure ℚ := IsAlgClosed.lift
  let ψ0 : B →+* AlgebraicClosure ℚ := ψq.toRingHom.comp (Ideal.Quotient.mk Q)
  have hψ0 : ∀ a, ψ0 (g0 a) = aeval y a := by
    intro a
    have h1 : Ideal.Quotient.mk Q (g0 a) =
        algebraMap (MvPolynomial (Fin s) ℚ ⧸ p) (B ⧸ Q) (Ideal.Quotient.mk p a) := rfl
    change ψq (Ideal.Quotient.mk Q (g0 a)) = aeval y a
    rw [h1, ψq.commutes]
    rfl
  refine ⟨ψ0.toRatAlgHom, ?_, fun j ↦ ⟨N, hNpos, ?_⟩⟩
  · intro h0
    apply hcy
    rw [← hψ0, ← hmap, ← hb]
    rw [map_mul]
    change ψ0 b * ψ0.toRatAlgHom g = 0
    rw [h0, mul_zero]
  · change ψ0 (g0 (X j)) ^ N = 1
    rw [hψ0, aeval_X]
    exact hy j

end GroundTheory.Heights₂.Heights
