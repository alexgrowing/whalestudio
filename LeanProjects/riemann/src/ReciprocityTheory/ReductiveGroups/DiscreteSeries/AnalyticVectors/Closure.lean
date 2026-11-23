import ReciprocityTheory.ReductiveGroups.DiscreteSeries.AnalyticVectors.Analytic
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.AnalyticVectors.ClosureK
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.AnalyticVectors.PolarJmConjTranspose
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.AnalyticVectors.ExistsExpEqOfMemKset

noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

section Rep

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {ε : Fin n → Bool}
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H}
  {E : Fin n → Fin n → Module.End ℂ D}

theorem closure_E_mem_genSub {V : Submodule ℂ D} (a b : Fin n) {v : D} (hv : v ∈ genSub E V) :
    E a b v ∈ genSub E V := by
  rw [genSub, Submodule.mem_sInf] at hv ⊢
  intro T hT
  exact hT.2 a b v (hv T hT)

theorem closure_actM_pow_mem_genSub {V : Submodule ℂ D} (X : Matrix (Fin n) (Fin n) ℂ) (m : ℕ)
    {v : D} (hv : v ∈ genSub E V) : ((actM E X) ^ m) v ∈ genSub E V := by
  induction m with
  | zero => simpa using hv
  | succ m ih =>
    rw [pow_succ', Module.End.mul_apply, actM, LinearMap.sum_apply]
    refine Submodule.sum_mem _ fun a _ => ?_
    rw [LinearMap.sum_apply]
    refine Submodule.sum_mem _ fun b _ => ?_
    rw [LinearMap.smul_apply]
    exact Submodule.smul_mem _ _ (closure_E_mem_genSub a b ih)

theorem closure_mapsTo_of_genSub {V : Submodule ℂ D} (T : H →L[ℂ] H)
    (hT : ∀ v : D, v ∈ genSub E V → T (v : H) ∈ ((genSub E V).map D.subtype).topologicalClosure)
    {x : H} (hx : x ∈ ((genSub E V).map D.subtype).topologicalClosure) :
    T x ∈ ((genSub E V).map D.subtype).topologicalClosure := by
  have hsub : (((genSub E V).map D.subtype : Submodule ℂ H) : Set H) ⊆
      T ⁻¹' ((((genSub E V).map D.subtype).topologicalClosure : Submodule ℂ H) : Set H) := by
    rintro y ⟨v, hv, rfl⟩
    exact hT v hv
  have hcl : IsClosed (T ⁻¹' ((((genSub E V).map D.subtype).topologicalClosure :
      Submodule ℂ H) : Set H)) :=
    ((genSub E V).map D.subtype).isClosed_topologicalClosure.preimage T.continuous
  have hx' : x ∈ closure (((genSub E V).map D.subtype : Submodule ℂ H) : Set H) := by
    rwa [← SetLike.mem_coe, Submodule.topologicalClosure_coe] at hx
  exact closure_minimal hsub hcl hx'

theorem closure_inUJ_of_mem_Kset {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Kset ε) :
    k ∈ UJset ε := by
  obtain ⟨hu, hc⟩ := hk
  have h1 : k.conjTranspose * k = 1 := by
    simpa [Matrix.star_eq_conjTranspose] using Matrix.mem_unitaryGroup_iff'.mp hu
  show k.conjTranspose * Jm ε * k = Jm ε
  rw [Matrix.mul_assoc, ← hc, ← Matrix.mul_assoc, h1, Matrix.one_mul]

theorem exp_apply_mem_topologicalClosure (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E)
    {V : Submodule ℂ D} (hVf : FiniteDimensional ℂ V) (hVK : IsKStableSub ε E V) {c : ℝ}
    (hc : ∀ v ∈ V, casimir E v = (c : ℂ) • v) {X : Matrix (Fin n) (Fin n) ℂ}
    (hX : inP ε X) {v : D} (hv : v ∈ genSub E V) :
    σ (NormedSpace.exp X) (v : H) ∈ ((genSub E V).map D.subtype).topologicalClosure := by
  have hSc : IsClosed ((((genSub E V).map D.subtype).topologicalClosure : Submodule ℂ H) : Set H) :=
    ((genSub E V).map D.subtype).isClosed_topologicalClosure
  have hsub : ∀ w : D, w ∈ genSub E V →
      (w : H) ∈ ((genSub E V).map D.subtype).topologicalClosure := fun w hw =>
    ((genSub E V).map D.subtype).le_topologicalClosure ⟨w, hw, rfl⟩
  have hc0 : (0 : ℝ) ≤ √2 * √(∑ a, ∑ b, ‖X a b‖ ^ 2) := by positivity
  obtain ⟨N, hN⟩ := exists_nat_gt (√2 * √(∑ a, ∑ b, ‖X a b‖ ^ 2))
  have hN0 : (0 : ℝ) < N := lt_of_le_of_lt hc0 hN
  have hstep : ∀ j : ℕ, ∀ w : D, w ∈ genSub E V →
      σ (NormedSpace.exp ((((j : ℝ) / N : ℝ) : ℂ) • X)) (w : H) ∈
        ((genSub E V).map D.subtype).topologicalClosure := by
    intro j
    induction j with
    | zero =>
      intro w hw
      simp only [Nat.cast_zero, zero_div, Complex.ofReal_zero, zero_smul, NormedSpace.exp_zero]
      rw [hσ.1.1, ContinuousLinearMap.one_apply]
      exact hsub w hw
    | succ j ih =>
      intro w hw
      have hdiff : (((j + 1 : ℕ) : ℝ) / N) - ((j : ℝ) / N) = 1 / N := by
        rw [Nat.cast_succ, add_div, add_sub_cancel_left]
      have ht : |(((j + 1 : ℕ) : ℝ) / N) - ((j : ℝ) / N)| * (√2 * √(∑ a, ∑ b, ‖X a b‖ ^ 2)) < 1 := by
        rw [hdiff, abs_of_pos (div_pos one_pos hN0), one_div, inv_mul_lt_iff₀ hN0, mul_one]
        exact hN
      have hs := orbit_hasSum_taylor hσ hD hVf hVK hc hX hw ((j : ℝ) / N) (((j + 1 : ℕ) : ℝ) / N) ht
      refine hSc.mem_of_tendsto hs.tendsto_sum_nat (Filter.Eventually.of_forall fun M => ?_)
      refine Submodule.sum_mem _ fun m _ => Submodule.smul_mem _ _ ?_
      exact ih _ (closure_actM_pow_mem_genSub X m hw)
  have h := hstep N v hv
  rwa [div_self hN0.ne', Complex.ofReal_one, one_smul] at h

theorem closure_genSub_stable (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E)
    {V : Submodule ℂ D} (hVf : FiniteDimensional ℂ V) (hVK : IsKStableSub ε E V) {c : ℝ}
    (hc : ∀ v ∈ V, casimir E v = (c : ℂ) • v) :
    ∀ g ∈ UJset ε, ∀ x ∈ ((genSub E V).map D.subtype).topologicalClosure,
      σ g x ∈ ((genSub E V).map D.subtype).topologicalClosure := by
  intro g hg x hx
  obtain ⟨k, hk, Y, hY, hgk⟩ := polar_UJ hg
  have hkU : k ∈ UJset ε := closure_inUJ_of_mem_Kset hk
  have h1 : k.conjTranspose * k = 1 := by
    simpa [Matrix.star_eq_conjTranspose] using Matrix.mem_unitaryGroup_iff'.mp hk.1
  have h2 : k * k.conjTranspose = 1 := by
    simpa [Matrix.star_eq_conjTranspose] using Matrix.mem_unitaryGroup_iff.mp hk.1
  have hEq : k.conjTranspose * g = NormedSpace.exp Y := by
    rw [hgk, ← Matrix.mul_assoc, h1, Matrix.one_mul]
  have hkg : k.conjTranspose * g ∈ UJset ε := by
    have hg' : g.conjTranspose * Jm ε * g = Jm ε := hg
    show (k.conjTranspose * g).conjTranspose * Jm ε * (k.conjTranspose * g) = Jm ε
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    calc g.conjTranspose * k * Jm ε * (k.conjTranspose * g)
        = g.conjTranspose * (k * Jm ε) * k.conjTranspose * g := by simp only [Matrix.mul_assoc]
      _ = g.conjTranspose * (Jm ε * k) * k.conjTranspose * g := by rw [hk.2]
      _ = g.conjTranspose * Jm ε * (k * k.conjTranspose) * g := by simp only [Matrix.mul_assoc]
      _ = Jm ε := by rw [h2, Matrix.mul_one, hg']
  have hσg : σ g = (σ k).comp (σ (k.conjTranspose * g)) := by
    have h3 := hσ.1.2 k hkU _ hkg
    rwa [← Matrix.mul_assoc, h2, Matrix.one_mul] at h3
  have hs1 : σ (NormedSpace.exp Y) x ∈ ((genSub E V).map D.subtype).topologicalClosure :=
    closure_mapsTo_of_genSub _ (fun v hv => exp_apply_mem_topologicalClosure hσ hD hVf hVK hc hY hv) hx
  obtain ⟨Z, hZ, hZe⟩ := exists_exp_eq_of_mem_Kset hk
  have hs2 : ∀ y ∈ ((genSub E V).map D.subtype).topologicalClosure,
      σ k y ∈ ((genSub E V).map D.subtype).topologicalClosure := fun y hy =>
    closure_mapsTo_of_genSub _ (fun v hv => by
      rw [← hZe]
      exact exp_inK_apply_mem_closure hσ hD hVf hVK hZ hv) hy
  rw [hσg, ContinuousLinearMap.comp_apply, hEq]
  exact hs2 _ hs1

end Rep

end ReciprocityTheory.ChartRestriction.DS
