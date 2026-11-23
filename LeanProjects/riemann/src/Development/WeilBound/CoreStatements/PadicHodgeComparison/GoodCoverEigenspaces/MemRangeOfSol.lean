import Mathlib

open Matrix

namespace PositivityTheory.AutomorphicGaloisHodgeTate.G8

variable {k C : Type*} [Field k] [Field C] [Algebra k C]

theorem mem_range_of_sol {m d J : Type*} [Fintype m] [Fintype d] (M : J → Matrix m m k) (B : Matrix m d k)
    (hB : ∀ v : m → k, (∀ j, M j *ᵥ v = 0) → ∃ w, B *ᵥ w = v) (x : m → C)
    (hx : ∀ j, (M j).map (algebraMap k C) *ᵥ x = 0) : ∃ z : d → C, B.map (algebraMap k C) *ᵥ z = x := by
  classical
  let e := Module.Basis.ofVectorSpace k C
  have h1 : ∀ α j, M j *ᵥ (fun p => e.repr (x p) α) = 0 := fun α j => funext fun p => by
    have := congrArg (fun t => e.repr t α) (congrFun (hx j) p)
    simpa [mulVec, dotProduct, ← Algebra.smul_def, map_sum, Finsupp.finset_sum_apply] using this
  choose w hw using fun α => hB _ (h1 α)
  let S := Finset.univ.biUnion fun p => (e.repr (x p)).support
  refine ⟨fun q => ∑ α ∈ S, w α q • e α, funext fun p => ?_⟩
  have h2 : ∑ α ∈ S, e.repr (x p) α • e α = x p := by
    conv_rhs => rw [← e.linearCombination_repr (x p), Finsupp.linearCombination_apply]
    exact (Finsupp.sum_of_support_subset _ (Finset.subset_biUnion_of_mem (fun p => (e.repr (x p)).support) (Finset.mem_univ p))
      (fun α c => c • e α) fun α _ => zero_smul _ _).symm
  rw [← h2]
  simp only [mulVec, dotProduct, map_apply, ← Algebra.smul_def, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [← Finset.sum_smul]
  exact congrArg (· • e α) (congrFun (hw α) p)

theorem map_injective {m d : Type*} [Fintype m] [Fintype d] (B : Matrix m d k) (h : Function.Injective B.mulVec) :
    Function.Injective (B.map (algebraMap k C)).mulVec := by
  classical
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective (Matrix.toLin' B) (LinearMap.ker_eq_bot.2 h)
  have h1 : LinearMap.toMatrix' g * B = 1 := by
    rw [← LinearMap.toMatrix'_toLin' B, ← LinearMap.toMatrix'_comp, hg, LinearMap.toMatrix'_id]
  intro x y hxy
  have := congrArg (((LinearMap.toMatrix' g).map (algebraMap k C)) *ᵥ ·) hxy
  simpa only [mulVec_mulVec, ← Matrix.map_mul, h1, Matrix.map_one _ (map_zero _) (map_one _), one_mulVec] using this

end PositivityTheory.AutomorphicGaloisHodgeTate.G8
