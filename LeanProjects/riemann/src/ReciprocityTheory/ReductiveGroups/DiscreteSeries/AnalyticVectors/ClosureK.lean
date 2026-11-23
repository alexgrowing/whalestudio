import ReciprocityTheory.ReductiveGroups.DiscreteSeries.AnalyticVectors.Taylor
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.AnalyticVectors.ConjTransposeEqOfInG
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.BochnerInequality.LayerBasic

noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

section Rep

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {ε : Fin n → Bool}
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H}
  {E : Fin n → Fin n → Module.End ℂ D}

theorem actM_mem_layer_of_inK {V : Submodule ℂ D} (hE : IsGlRep E) (hV : IsKStableSub ε E V)
    {Z : Matrix (Fin n) (Fin n) ℂ} (hZ : inK ε Z) {k : ℕ} {x : D} (hx : x ∈ layer ε E V k) :
    actM E Z x ∈ layer ε E V k := by
  have hZ0 : ∀ a b, ε a ≠ ε b → Z a b = 0 := by
    intro a b hab
    have h := congrFun (congrFun hZ.2 a) b
    rw [Jm, Matrix.mul_diagonal, Matrix.diagonal_mul] at h
    cases ha : ε a <;> cases hb : ε b <;> simp [ha, hb] at hab h ⊢ <;>
      first | exact h | linear_combination h / 2 | linear_combination -h / 2
  rw [actM, LinearMap.sum_apply]
  refine Submodule.sum_mem _ fun a _ => ?_
  rw [LinearMap.sum_apply]
  refine Submodule.sum_mem _ fun b _ => ?_
  rw [LinearMap.smul_apply]
  by_cases hab : ε a = ε b
  · exact Submodule.smul_mem _ _ (layer_kStable hE hV k a b hab x hx)
  · rw [hZ0 a b hab, zero_smul]
    exact zero_mem _

theorem actM_pow_mem_layer_of_inK {V : Submodule ℂ D} (hE : IsGlRep E) (hV : IsKStableSub ε E V)
    {Z : Matrix (Fin n) (Fin n) ℂ} (hZ : inK ε Z) {k : ℕ} {x : D} (hx : x ∈ layer ε E V k) (m : ℕ) :
    ((actM E Z) ^ m) x ∈ layer ε E V k := by
  induction m with
  | zero => simpa using hx
  | succ m ih =>
    rw [pow_succ', Module.End.mul_apply]
    exact actM_mem_layer_of_inK hE hV hZ ih

theorem exists_norm_actM_pow_le_of_inK {V : Submodule ℂ D} (hE : IsGlRep E)
    (hV : IsKStableSub ε E V) (hVf : FiniteDimensional ℂ V) {Z : Matrix (Fin n) (Fin n) ℂ}
    (hZ : inK ε Z) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ layer ε E V k, ∀ m : ℕ, ‖((actM E Z) ^ m) x‖ ≤ C ^ m * ‖x‖ := by
  haveI : FiniteDimensional ℂ (layer ε E V k) := finiteDimensional_layer hVf k
  let T : layer ε E V k →ₗ[ℂ] layer ε E V k :=
    (actM E Z).restrict (fun x hx => actM_mem_layer_of_inK hE hV hZ hx)
  let T' := LinearMap.toContinuousLinearMap T
  refine ⟨‖T'‖, norm_nonneg _, fun x hx m => ?_⟩
  have hpow : ∀ m : ℕ, ((actM E Z) ^ m) x = (((T ^ m) ⟨x, hx⟩ : layer ε E V k) : D) := by
    intro m
    induction m with
    | zero => rfl
    | succ m ih =>
      rw [pow_succ', Module.End.mul_apply, ih, pow_succ', Module.End.mul_apply]
      rfl
  have hnorm : ∀ (m : ℕ) (y : layer ε E V k), ‖(T ^ m) y‖ ≤ ‖T'‖ ^ m * ‖y‖ := by
    intro m
    induction m with
    | zero => intro y; simp
    | succ m ih =>
      intro y
      rw [pow_succ', Module.End.mul_apply]
      calc ‖T ((T ^ m) y)‖ = ‖T' ((T ^ m) y)‖ := rfl
        _ ≤ ‖T'‖ * ‖(T ^ m) y‖ := T'.le_opNorm _
        _ ≤ ‖T'‖ * (‖T'‖ ^ m * ‖y‖) := by gcongr; exact ih y
        _ = ‖T'‖ ^ (m + 1) * ‖y‖ := by ring
  rw [hpow]
  exact hnorm m ⟨x, hx⟩

theorem exp_inK_apply_mem_closure (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E)
    {V : Submodule ℂ D} (hVf : FiniteDimensional ℂ V) (hVK : IsKStableSub ε E V)
    {Z : Matrix (Fin n) (Fin n) ℂ} (hZ : inK ε Z) {v : D} (hv : v ∈ genSub E V) :
    σ (NormedSpace.exp Z) (v : H) ∈ ((genSub E V).map D.subtype).topologicalClosure := by
  have hE := hD.glRep
  have hv' := hv
  rw [genSub_eq_iSup_layer hE hVK] at hv'
  obtain ⟨k, hk⟩ : ∃ k, v ∈ layer ε E V k :=
    (Submodule.mem_iSup_of_directed _ (Monotone.directed_le fun i j hij => layer_mono hij)).mp hv'
  obtain ⟨C, hC0, hC⟩ := exists_norm_actM_pow_le_of_inK hE hVK hVf hZ k
  have hs : Summable fun m : ℕ => C ^ m * ‖v‖ * |(1 : ℝ) - 0| ^ m / (m.factorial : ℝ) := by
    have := (Real.summable_pow_div_factorial C).mul_left ‖v‖
    refine this.congr fun m => ?_
    simp only [sub_zero, abs_one, one_pow, mul_one]
    ring
  have hsum := hasSum_orbit_of_bound hσ hD hZ.1 v (fun m => C ^ m * ‖v‖)
    (fun m => by simpa using hC v hk m) 0 1 hs
  simp only [Complex.ofReal_zero, zero_smul, NormedSpace.exp_zero, hσ.1.1, Complex.ofReal_one,
    one_smul, ContinuousLinearMap.one_apply, sub_zero, one_pow] at hsum
  rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe]
  refine mem_closure_of_tendsto hsum.tendsto_sum_nat (Filter.Eventually.of_forall fun N => ?_)
  refine Submodule.sum_mem _ fun m _ => Submodule.smul_mem _ _ ?_
  exact Submodule.mem_map_of_mem
    (layer_le_genSub (ε := ε) k (actM_pow_mem_layer_of_inK hE hVK hZ hk m))

end Rep

end ReciprocityTheory.ChartRestriction.DS
