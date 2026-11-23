import ReciprocityTheory.ReductiveGroups.DiscreteSeries.AnalyticVectors.Unitary
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.AnalyticVectors.Taylor
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.AnalyticVectors.Series
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.AnalyticVectors.Growth
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.AnalyticVectors.NcBound

noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

section Rep

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {ε : Fin n → Bool}
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H}
  {E : Fin n → Fin n → Module.End ℂ D}

theorem exists_orbit_bound (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E)
    {V : Submodule ℂ D} (hVf : FiniteDimensional ℂ V) (hVK : IsKStableSub ε E V) {c : ℝ}
    (hc : ∀ v ∈ V, casimir E v = (c : ℂ) • v) {X : Matrix (Fin n) (Fin n) ℂ}
    (hX : inP ε X) {v : D} (hv : v ∈ genSub E V) :
    ∃ a : ℕ → ℝ, (∀ m, ‖((((actM E X) ^ m) v : D) : H)‖ ≤ a m) ∧ (∀ m, 0 ≤ a m) ∧
      ∀ r : ℝ, 0 ≤ r → r * (√2 * √(∑ a, ∑ b, ‖X a b‖ ^ 2)) < 1 →
        Summable fun m : ℕ => a m * r ^ m / (m.factorial : ℝ) := by
  have hE := hD.glRep
  have hU := isInfUnitary_of_isDerivedOn hσ hD
  obtain ⟨R, hR0, hR⟩ := exists_sum_nc_norm_sq_le ε hE hU hVf hVK hc
  set d : ℝ := nsq (rhoC ε) + c
  have hR' : ∀ k : ℕ, ∀ x ∈ layer ε E V k,
      ∑ a, ∑ b ∈ univ.filter (fun b => ε a ≠ ε b), ‖E a b x‖ ^ 2 ≤ ((R + √2 * k) ^ 2 - d) * ‖x‖ ^ 2 := by
    intro k x hx
    have := hR k x hx
    simpa only [d, sub_sub] using this
  rw [genSub_eq_iSup_layer hE hVK, Submodule.mem_iSup_of_directed _ (show Monotone (layer ε E V) from fun _ _ h => layer_mono h).directed_le] at hv
  obtain ⟨k, hk⟩ := hv
  set S : ℝ := √(∑ a, ∑ b, ‖X a b‖ ^ 2)
  set A : ℝ := R + √(max 0 (-d))
  have hA : 0 ≤ A := add_nonneg hR0 (Real.sqrt_nonneg _)
  have hS : 0 ≤ S := Real.sqrt_nonneg _
  refine ⟨fun m => S ^ m * (∏ l ∈ range m, (A + √2 * ((k : ℝ) + l))) * ‖v‖, ?_, ?_, ?_⟩
  · intro m
    have := norm_actM_pow_le hE hVK hR0 hR' hX k hk m
    simpa only [Submodule.coe_norm] using this
  · intro m
    refine mul_nonneg (mul_nonneg (pow_nonneg hS _) ?_) (norm_nonneg _)
    exact prod_nonneg fun l _ => add_nonneg hA (mul_nonneg (Real.sqrt_nonneg _) (by positivity))
  · intro r hr hrS
    have h1 := summable_prod_mul_pow_div_factorial hA (Real.sqrt_nonneg 2) (mul_nonneg hr hS)
      (by nlinarith) k
    have h2 := h1.mul_left ‖v‖
    refine h2.congr fun m => ?_
    rw [mul_pow]
    ring

theorem orbit_hasSum_taylor (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E)
    {V : Submodule ℂ D} (hVf : FiniteDimensional ℂ V) (hVK : IsKStableSub ε E V) {c : ℝ}
    (hc : ∀ v ∈ V, casimir E v = (c : ℂ) • v) {X : Matrix (Fin n) (Fin n) ℂ}
    (hX : inP ε X) {v : D} (hv : v ∈ genSub E V) (t₀ t : ℝ)
    (ht : |t - t₀| * (√2 * √(∑ a, ∑ b, ‖X a b‖ ^ 2)) < 1) :
    HasSum (fun m : ℕ => (((t - t₀) ^ m / (m.factorial : ℝ) : ℝ) : ℂ) •
        σ (NormedSpace.exp ((t₀ : ℂ) • X)) ((((actM E X) ^ m) v : D) : H))
      (σ (NormedSpace.exp ((t : ℂ) • X)) (v : H)) := by
  obtain ⟨a, ha, -, hs⟩ := exists_orbit_bound hσ hD hVf hVK hc hX hv
  exact hasSum_orbit_of_bound hσ hD hX.1 v a ha t₀ t (hs _ (abs_nonneg _) ht)

end Rep

end ReciprocityTheory.ChartRestriction.DS
