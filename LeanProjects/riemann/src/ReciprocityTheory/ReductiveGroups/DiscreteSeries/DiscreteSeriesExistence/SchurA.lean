import ReciprocityTheory.ReductiveGroups.DiscreteSeries.RigidityTheorems.RorthFunctionalEqZero
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.CFCoreA

noncomputable section

open Finset Matrix

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

section Alg

variable {M : Type*} [NormedAddCommGroup M] [InnerProductSpace ℂ M] {ε : Fin n → Bool}
  {E : Fin n → Fin n → Module.End ℂ M} {V : Submodule ℂ M}

theorem schA_genSub_le {Λ : Fin n → ℝ} (hV : IsKIrrHW ε E Λ V) (X : Submodule ℂ M)
    (hX : ∀ a b, ∀ x ∈ X, E a b x ∈ X) {x : M} (hxV : x ∈ V) (hxX : x ∈ X) (hx0 : x ≠ 0) :
    genSub E V ≤ X := by
  obtain ⟨-, hVk, hirr, -⟩ := hV
  have hst : IsKStableSub ε E (V ⊓ X) := fun a b hab v hv => ⟨hVk a b hab v hv.1, hX a b v hv.2⟩
  have hVX : V ≤ X := by
    rcases hirr (V ⊓ X) inf_le_left hst with h | h
    · have hx : x ∈ V ⊓ X := ⟨hxV, hxX⟩
      rw [h] at hx
      exact absurd ((Submodule.mem_bot ℂ).1 hx) hx0
    · exact inf_eq_left.1 h
  unfold genSub
  exact sInf_le ⟨hVX, hX⟩

theorem schA_riesz (hE : IsGlRep E) (hU : IsInfUnitary ε E) (hVf : FiniteDimensional ℂ V)
    (hVk : IsKStableSub ε E V) (T : Submodule ℂ M) (hT : T ≤ genSub E V)
    (hTk : IsKStableSub ε E T) (f : M →ₗ[ℂ] ℂ) (μ : Fin n → ℝ)
    (hfd : ∀ a, ∀ y ∈ T, f (E a a y) = (μ a : ℂ) * f y)
    (hfl : ∀ a b, a < b → ε a = ε b → ∀ y ∈ T, f (E b a y) = 0) {y₀ : M} (hy₀ : y₀ ∈ T) :
    ∃ u ∈ T, IsKHWVec ε E μ u ∧ inner ℂ u y₀ = f y₀ ∧ ∀ v ∈ T ⊓ V, inner ℂ u v = f v := by
  obtain ⟨m, hm⟩ := exists_layer_of_mem_genSub hE hVk (hT hy₀)
  have hVle : ∀ k, V ≤ layer ε E V k := by
    intro k
    induction k with
    | zero => exact le_rfl
    | succ k ih =>
      show V ≤ layer ε E V k ⊔ ⨆ (a : Fin n) (b : Fin n) (_ : ε a ≠ ε b), (layer ε E V k).map (E a b)
      exact ih.trans le_sup_left
  set F : Submodule ℂ M := T ⊓ layer ε E V m with hF
  haveI : FiniteDimensional ℂ (layer ε E V m) := finiteDimensional_layer hVf m
  haveI : FiniteDimensional ℂ F := Submodule.finiteDimensional_of_le inf_le_right
  have hFk : IsKStableSub ε E F := fun a b hab v hv =>
    ⟨hTk a b hab v hv.1, layer_kStable hE hVk m a b hab v hv.2⟩
  let ℓ : F →L[ℂ] ℂ := LinearMap.toContinuousLinearMap (f.comp F.subtype)
  set u' : F := (InnerProductSpace.toDual ℂ F).symm ℓ with hu'
  have hrep : ∀ y ∈ F, inner ℂ (u' : M) y = f y := by
    intro y hy
    have h1 := InnerProductSpace.toDual_symm_apply (𝕜 := ℂ) (E := F) (x := ⟨y, hy⟩) (y := ℓ)
    rw [← hu'] at h1
    exact h1
  have hzero : ∀ z ∈ F, (∀ y ∈ F, inner ℂ z y = 0) → z = 0 := fun z hz h =>
    inner_self_eq_zero.mp (h z hz)
  refine ⟨u', u'.2.1, ⟨?_, ?_⟩, hrep y₀ ⟨hy₀, hm⟩, fun v hv => hrep v ⟨hv.1, hVle m hv.2⟩⟩
  · intro a
    have hsa : adjSign ε a a = 1 := if_pos rfl
    have hmem : E a a u' - (μ a : ℂ) • (u' : M) ∈ F :=
      F.sub_mem (hFk a a rfl _ u'.2) (F.smul_mem _ u'.2)
    have h0 := hzero _ hmem (fun y hy => by
      rw [inner_sub_left, inner_smul_left, hU a a, hsa, one_mul, hrep _ (hFk a a rfl y hy),
        hrep y hy, hfd a y hy.1, Complex.conj_ofReal, sub_self])
    exact sub_eq_zero.mp h0
  · intro a b hab hεab
    have hmem : E a b u' ∈ F := hFk a b hεab _ u'.2
    exact hzero _ hmem (fun y hy => by
      rw [hU a b, hrep _ (hFk b a hεab.symm y hy), hfl a b hab hεab y hy.1, mul_zero])

theorem schA_adjSign_sq (ε : Fin n → Bool) (a b : Fin n) : adjSign ε a b * adjSign ε a b = 1 := by
  unfold adjSign
  split_ifs <;> norm_num

end Alg

end ReciprocityTheory.ChartRestriction.DS
