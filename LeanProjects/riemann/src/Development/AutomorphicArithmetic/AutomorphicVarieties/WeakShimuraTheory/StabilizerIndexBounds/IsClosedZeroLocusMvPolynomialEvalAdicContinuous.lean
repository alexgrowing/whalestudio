import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.UniversalOrdinaryDeterminantRing
import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.IsUnitOrIsUnitOfAddOne
import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.LinClosedOfAdic

open IsLocalRing Polynomial Matrix UpperTheory.V

open Filter Topology in
theorem UpperTheory.V.Ws.isClosed_zeroLocus_mvPolynomial_eval_adicContinuous :
    ∀ (G A κ ι : Type) [TopologicalSpace G] [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsLocalRing A] [Field κ]
      (j : A →+* κ), Function.Injective j → ∀ a : ι → G → A, (∀ s, Alg.AdicCont (maximalIdeal A) (a s)) →
      ∀ f : MvPolynomial ι κ, IsClosed {g | MvPolynomial.eval (fun s => j (a s g)) f = 0} := by
  intro G A κ ι _ _ _ _ _ _ j _ a ha f
  classical
  letI : Algebra A κ := j.toAlgebra
  let L : (f.support → A) →ₗ[A] κ :=
    { toFun := fun v => ∑ d : f.support, f.coeff d.1 * j (v d)
      map_add' := fun x y => by
        simp only [Pi.add_apply, map_add, mul_add, Finset.sum_add_distrib]
      map_smul' := fun c x => by
        change ∑ d : f.support, f.coeff d.1 * j (c * x d) = j c * ∑ d : f.support, f.coeff d.1 * j (x d)
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun d _ => ?_
        rw [map_mul]; ring }
  let m : G → f.support → A := fun g d => ∏ i ∈ d.1.support, a i g ^ d.1 i
  have hL : ∀ g, L (m g) = MvPolynomial.eval (fun s => j (a s g)) f := fun g => by
    rw [MvPolynomial.eval_eq, ← Finset.sum_coe_sort]
    change ∑ d : f.support, f.coeff d.1 * j (m g d) = _
    refine Finset.sum_congr rfl fun d _ => ?_
    simp only [m, map_prod, map_pow]
  let K := LinearMap.ker L
  have hK := Ideal.iInf_pow_smul_eq_bot_of_isLocalRing (M := (f.support → A) ⧸ K) (maximalIdeal A)
    (maximalIdeal.isMaximal A).ne_top
  rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
  intro x hx
  have hx' : K.mkQ (m x) ≠ 0 := fun h => hx (by
    have h2 : L (m x) = 0 := (Submodule.Quotient.mk_eq_zero K).1 h
    rw [hL] at h2
    exact h2)
  obtain ⟨N, hN⟩ : ∃ N : ℕ, K.mkQ (m x) ∉ (maximalIdeal A ^ N • ⊤ : Submodule A ((f.support → A) ⧸ K)) := by
    by_contra h
    push Not at h
    apply hx'
    rw [← Submodule.mem_bot A, ← hK]
    exact (Submodule.mem_iInf _).2 h
  have hev : ∀ᶠ y in 𝓝 x, ∀ d, m x d - m y d ∈ maximalIdeal A ^ N := by
    rw [eventually_all]; intro d
    have h1 : ∀ᶠ y in 𝓝 x, ∀ i ∈ d.1.support,
        Ideal.Quotient.mk (maximalIdeal A ^ N) (a i y) = Ideal.Quotient.mk (maximalIdeal A ^ N) (a i x) := by
      rw [eventually_all_finset]; intro i _
      exact (ha i N).eventually_eq x
    filter_upwards [h1] with y hy
    refine Ideal.Quotient.eq.1 ?_
    simp only [m, map_prod, map_pow]
    exact Finset.prod_congr rfl fun i hi => by rw [hy i hi]
  filter_upwards [hev] with y hy hy0
  apply hN
  have h0 : K.mkQ (m y) = 0 := (Submodule.Quotient.mk_eq_zero K).2 (by
    change L (m y) = 0
    rw [hL]; exact hy0)
  have h1 : K.mkQ (m x) = K.mkQ (m x - m y) := by rw [map_sub, h0, sub_zero]
  rw [h1, pi_eq_sum_univ' (m x - m y), map_sum]
  refine Submodule.sum_mem _ fun s _ => ?_
  rw [map_smul]
  exact Submodule.smul_mem_smul (hy s) Submodule.mem_top
