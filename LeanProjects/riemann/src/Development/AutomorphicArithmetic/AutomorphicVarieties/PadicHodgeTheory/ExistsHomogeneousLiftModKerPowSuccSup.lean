import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective

open IsLocalRing UpperTheory.V.Alg

private theorem mul_mem_pow_sup {R : Type} [CommRing R] (P I : Ideal R) (m k : ℕ) (u v : R)
    (hu : u ∈ P ^ m) (hv : v ∈ P ^ k ⊔ I) : u * v ∈ P ^ (m + k) ⊔ I := by
  obtain ⟨p, hp, i, hi, rfl⟩ := Submodule.mem_sup.mp hv
  rw [mul_add]
  refine Submodule.add_mem_sup ?_ (I.mul_mem_left u hi)
  rw [pow_add]
  exact Ideal.mul_mem_mul hu hp

theorem UpperTheory.exists_homogeneous_lift_mod_ker_pow_succ_sup :
    ∀ (O R : Type) [CommRing O] [IsDomain O] [CommRing R] [Algebra O R] (I : Ideal R) (x : R →ₐ[O] O) (n : ℕ) (t : Fin n → R), (∀ i, x (t i) = 0) → (∀ a, x a = 0 → ∃ (e : O) (o : Fin n → O), e ≠ 0 ∧ e • a - ∑ i, o i • t i ∈ RingHom.ker x ^ 2 ⊔ I) → ∀ (N : ℕ), ∀ a ∈ RingHom.ker x ^ N, ∃ (e : O) (h : MvPolynomial (Fin n) O), e ≠ 0 ∧ h.IsHomogeneous N ∧ e • a - MvPolynomial.aeval t h ∈ RingHom.ker x ^ (N + 1) ⊔ I := by
  intro O R _ _ _ _ I x n t ht hyp
  have htK : ∀ i, t i ∈ RingHom.ker x := fun i => RingHom.mem_ker.mpr (ht i)
  have key : ∀ N : ℕ, ∀ a ∈ RingHom.ker x ^ N, ∃ (e : O) (h : MvPolynomial (Fin n) O),
      e ≠ 0 ∧ h.IsHomogeneous N ∧ MvPolynomial.aeval t h ∈ RingHom.ker x ^ N ∧
      e • a - MvPolynomial.aeval t h ∈ RingHom.ker x ^ (N + 1) ⊔ I := by
    intro N
    induction N with
    | zero =>
      intro a _
      refine ⟨1, MvPolynomial.C (x a), one_ne_zero, MvPolynomial.isHomogeneous_C _ _, ?_, ?_⟩
      · rw [pow_zero, Ideal.one_eq_top]
        exact Submodule.mem_top
      · apply Ideal.mem_sup_left
        rw [zero_add, pow_one, RingHom.mem_ker]
        simp
    | succ N ih =>
      intro a ha
      rw [pow_succ] at ha
      refine Submodule.mul_induction_on (C := fun a => ∃ (e : O) (h : MvPolynomial (Fin n) O),
        e ≠ 0 ∧ h.IsHomogeneous (N + 1) ∧ MvPolynomial.aeval t h ∈ RingHom.ker x ^ (N + 1) ∧
        e • a - MvPolynomial.aeval t h ∈ RingHom.ker x ^ (N + 1 + 1) ⊔ I) ha ?_ ?_
      · intro b hb c hc
        obtain ⟨e1, h1, he1, hh1, hm1, hs1⟩ := ih b hb
        have hxc : x c = 0 := RingHom.mem_ker.mp hc
        obtain ⟨e2, o, he2, hs2⟩ := hyp c hxc
        have haL : MvPolynomial.aeval t (∑ i, MvPolynomial.C (o i) * MvPolynomial.X i)
            = ∑ i, o i • t i := by
          simp [map_sum, Algebra.smul_def]
        have hLK : MvPolynomial.aeval t (∑ i, MvPolynomial.C (o i) * MvPolynomial.X i)
            ∈ RingHom.ker x := by
          rw [haL]
          exact Ideal.sum_mem _ (fun i _ => by
            rw [Algebra.smul_def]
            exact Ideal.mul_mem_left _ _ (htK i))
        refine ⟨e1 * e2, h1 * ∑ i, MvPolynomial.C (o i) * MvPolynomial.X i,
          mul_ne_zero he1 he2, ?_, ?_, ?_⟩
        · exact hh1.mul (MvPolynomial.IsHomogeneous.sum _ _ _
            (fun i _ => MvPolynomial.isHomogeneous_C_mul_X _ _))
        · rw [map_mul, pow_succ]
          exact Ideal.mul_mem_mul hm1 hLK
        · have eq : (e1 * e2) • (b * c) - MvPolynomial.aeval t
                (h1 * ∑ i, MvPolynomial.C (o i) * MvPolynomial.X i)
              = (e2 • c) * (e1 • b - MvPolynomial.aeval t h1)
                + MvPolynomial.aeval t h1 * (e2 • c - ∑ i, o i • t i) := by
            rw [map_mul, haL]
            simp only [Algebra.smul_def, map_mul]
            ring
          rw [eq]
          refine Submodule.add_mem _ ?_ ?_
          · have hc' : e2 • c ∈ RingHom.ker x ^ 1 := by
              rw [pow_one, Algebra.smul_def]
              exact Ideal.mul_mem_left _ _ hc
            have := mul_mem_pow_sup (RingHom.ker x) I 1 (N + 1) _ _ hc' hs1
            rwa [show 1 + (N + 1) = N + 1 + 1 by omega] at this
          · have := mul_mem_pow_sup (RingHom.ker x) I N 2 _ _ hm1 hs2
            rwa [show N + 2 = N + 1 + 1 by omega] at this
      · rintro a1 a2 ⟨e1, h1, he1, hh1, hm1, hs1⟩ ⟨e2, h2, he2, hh2, hm2, hs2⟩
        refine ⟨e1 * e2, MvPolynomial.C e2 * h1 + MvPolynomial.C e1 * h2, mul_ne_zero he1 he2,
          (hh1.C_mul _).add (hh2.C_mul _), ?_, ?_⟩
        · rw [map_add, map_mul, map_mul, MvPolynomial.aeval_C, MvPolynomial.aeval_C]
          exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hm1) (Ideal.mul_mem_left _ _ hm2)
        · have eq : (e1 * e2) • (a1 + a2) - MvPolynomial.aeval t
                (MvPolynomial.C e2 * h1 + MvPolynomial.C e1 * h2)
              = e2 • (e1 • a1 - MvPolynomial.aeval t h1)
                + e1 • (e2 • a2 - MvPolynomial.aeval t h2) := by
            simp only [map_add, map_mul, MvPolynomial.aeval_C, Algebra.smul_def]
            ring
          rw [eq]
          refine Submodule.add_mem _ ?_ ?_
          · rw [Algebra.smul_def]
            exact Ideal.mul_mem_left _ _ hs1
          · rw [Algebra.smul_def]
            exact Ideal.mul_mem_left _ _ hs2
  intro N a ha
  obtain ⟨e, h, he, hh, _, hs⟩ := key N a ha
  exact ⟨e, h, he, hh, hs⟩
