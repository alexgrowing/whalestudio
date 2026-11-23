import Mathlib

noncomputable section

open NumberField NumberField.InfinitePlace NumberField.Units NumberField.Units.dirichletUnitTheorem

namespace PositivityTheory.KB.CentralizerFixed

variable (L : Type) [Field L] [NumberField L]

open Classical in

private def lamS : ({w : InfinitePlace L // w ≠ w₀} → ℝ) →ₗ[ℝ] (InfinitePlace L → ℝ) :=
  LinearMap.pi fun w => if h : w = w₀ then (-((mult (w₀ : InfinitePlace L) : ℝ))⁻¹) •
      ∑ w' : {w : InfinitePlace L // w ≠ w₀}, LinearMap.proj w'
    else ((mult w : ℝ))⁻¹ • LinearMap.proj (⟨w, h⟩ : {w : InfinitePlace L // w ≠ w₀})

open Classical in
private theorem lamS_apply (x : {w : InfinitePlace L // w ≠ w₀} → ℝ) (w : InfinitePlace L) :
    lamS L x w = if h : w = w₀ then -((mult (w₀ : InfinitePlace L) : ℝ))⁻¹ * ∑ w', x w'
      else ((mult w : ℝ))⁻¹ * x ⟨w, h⟩ := by
  unfold lamS
  by_cases h : w = w₀
  · simp [h, LinearMap.pi_apply, LinearMap.sum_apply]
  · simp [h, LinearMap.pi_apply]

omit [NumberField L] in
private theorem mult_ne (w : InfinitePlace L) : (mult w : ℝ) ≠ 0 := by
  have := mult_pos (w := w)
  exact_mod_cast this.ne'

private theorem lamS_log (u : (𝓞 L)ˣ) :
    lamS L (logEmbedding L (Additive.ofMul u)) = fun w => Real.log (w ((u : 𝓞 L) : L)) := by
  classical
  funext w
  rw [lamS_apply]
  by_cases h : w = w₀
  · subst h
    rw [dif_pos rfl]
    have hs := sum_logEmbedding_component (K := L) u
    have : (∑ w' : {w : InfinitePlace L // w ≠ w₀}, logEmbedding L (Additive.ofMul u) w') =
        -(mult (w₀ : InfinitePlace L) : ℝ) * Real.log (w₀ ((u : 𝓞 L) : L)) := by
      convert hs
    rw [this]
    field_simp [mult_ne L w₀]
  · rw [dif_neg h, logEmbedding_component]
    field_simp [mult_ne L w]

private theorem span_fund :
    Submodule.span ℝ (Set.range fun i => logEmbedding L (Additive.ofMul (fundSystem L i))) = ⊤ := by
  rw [eq_top_iff, ← unitLattice_span_eq_top, Submodule.span_le]
  intro x hx
  have e : (Set.range fun i => logEmbedding L (Additive.ofMul (fundSystem L i))) =
      (unitLattice L).subtype '' Set.range (basisUnitLattice L) := by
    rw [← Set.range_comp]
    congr 1
    funext i
    simp [logEmbedding_fundSystem]
  have h2 : x ∈ Submodule.span ℤ (Set.range fun i => logEmbedding L (Additive.ofMul (fundSystem L i))) := by
    rw [e, ← Submodule.map_span, (basisUnitLattice L).span_eq, Submodule.map_top,
      Submodule.range_subtype]
    exact hx
  exact Submodule.span_subset_span ℤ ℝ _ h2

theorem span_units : ∃ l : List (𝓞 L)ˣ, ∀ t : InfinitePlace L → ℝ,
    t ∈ Submodule.span ℝ (insert (fun _ => (1 : ℝ))
      {x | ∃ u ∈ l, (fun w : InfinitePlace L => Real.log (w ((u : 𝓞 L) : L))) = x}) := by
  classical
  refine ⟨List.ofFn (fundSystem L), fun t => ?_⟩
  set S := {x | ∃ u ∈ List.ofFn (fundSystem L),
    (fun w : InfinitePlace L => Real.log (w ((u : 𝓞 L) : L))) = x}
  set M : ℝ := ∑ w : InfinitePlace L, (mult w : ℝ)
  have hM : 0 < M := by
    obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace L))
    exact Finset.sum_pos (fun w _ => by exact_mod_cast mult_pos) ⟨w, Finset.mem_univ _⟩
  set c : ℝ := (∑ w, (mult w : ℝ) * t w) / M
  let t' : {w : InfinitePlace L // w ≠ w₀} → ℝ := fun w => (mult w.1 : ℝ) * (t w.1 - c)
  have h1 : lamS L t' ∈ Submodule.span ℝ S := by
    have ht' : t' ∈ Submodule.span ℝ (Set.range fun i => logEmbedding L (Additive.ofMul (fundSystem L i))) := by
      rw [span_fund]; trivial
    have := Submodule.mem_map_of_mem (f := lamS L) ht'
    rw [Submodule.map_span] at this
    refine Submodule.span_mono ?_ this
    rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
    exact ⟨fundSystem L i, List.mem_ofFn.2 ⟨i, rfl⟩, (lamS_log L _).symm⟩
  have h2 : lamS L t' = t - c • (fun _ => (1 : ℝ)) := by
    funext w
    rw [lamS_apply]
    by_cases h : w = w₀
    · subst h
      rw [dif_pos rfl]
      have hsum : (∑ w : InfinitePlace L, (mult w : ℝ) * (t w - c)) = 0 := by
        simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul]
        change _ - M * c = 0
        simp only [c]; field_simp; ring
      rw [Fintype.sum_eq_add_sum_subtype_ne _ w₀] at hsum
      have : (∑ w' : {w : InfinitePlace L // w ≠ w₀}, t' w') =
          -((mult (w₀ : InfinitePlace L) : ℝ) * (t w₀ - c)) := by
        simp only [t']; linarith
      rw [this]
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, mul_one]
      field_simp [mult_ne L w₀]
    · rw [dif_neg h]
      simp only [t', Pi.sub_apply, Pi.smul_apply, smul_eq_mul, mul_one]
      field_simp [mult_ne L w]
  have : t = lamS L t' + c • (fun _ => (1 : ℝ)) := by rw [h2]; abel
  rw [this]
  refine Submodule.add_mem _ (Submodule.span_mono (Set.subset_insert _ _) h1) ?_
  exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_insert _ _))

end PositivityTheory.KB.CentralizerFixed

end
