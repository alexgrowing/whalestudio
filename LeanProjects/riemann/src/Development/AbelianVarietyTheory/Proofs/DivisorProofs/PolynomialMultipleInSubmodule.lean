import Mathlib
open SchwartzMap

namespace GlobalTheory

theorem schwartz_submodule_multilinear_mem (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (N : Submodule ℂ (SchwartzMap V ℂ)) (g : SchwartzMap V ℂ) (hg : g ∈ N)
    (hN : ∀ f ∈ N, ∀ ℓ : V →ₗ[ℝ] ℝ, ∃ f₁ ∈ N, ∀ x, f₁ x = (ℓ x : ℂ) * f x) :
    ∀ (j : ℕ) (M : ContinuousMultilinearMap ℝ (fun _ : Fin j => V) ℂ),
      ∃ f ∈ N, ∀ x, f x = M (fun _ => x) * g x := by
  intro j
  induction j with
  | zero =>
    intro M
    refine ⟨M (fun _ => 0) • g, N.smul_mem _ hg, fun x => ?_⟩
    have h : (fun _ : Fin 0 => x) = (fun _ => 0) := Subsingleton.elim _ _
    rw [h, SchwartzMap.smul_apply, smul_eq_mul]
  | succ j ih =>
    intro M
    let b := Module.finBasis ℝ V
    have key : ∀ i, ∃ f ∈ N, ∀ x, f x = ((b.coord i x : ℝ) : ℂ) * ((M.curryLeft (b i)) (fun _ => x) * g x) := by
      intro i
      obtain ⟨f, hf, hfx⟩ := ih (M.curryLeft (b i))
      obtain ⟨f₁, hf₁, hf₁x⟩ := hN f hf (b.coord i)
      exact ⟨f₁, hf₁, fun x => by rw [hf₁x, hfx]⟩
    choose F hF hFx using key
    refine ⟨∑ i, F i, N.sum_mem (fun i _ => hF i), fun x => ?_⟩
    have hcons : (fun _ : Fin (j+1) => x) = Fin.cons x (fun _ : Fin j => x) := by
      funext i; refine Fin.cases ?_ ?_ i <;> simp
    have hlin : M.curryLeft x = ∑ i, b.repr x i • M.curryLeft (b i) := by
      conv_lhs => rw [← b.sum_repr x]
      rw [map_sum]
      simp only [map_smul]
    have hx : M (fun _ => x) = ∑ i, ((b.coord i x : ℝ) : ℂ) * (M.curryLeft (b i)) (fun _ => x) := by
      rw [hcons, ← ContinuousMultilinearMap.curryLeft_apply, hlin, ContinuousMultilinearMap.sum_apply]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [ContinuousMultilinearMap.smul_apply, Module.Basis.coord_apply, Complex.real_smul]
    have hs : (∑ i, F i) x = ∑ i, F i x := by
      simp
    rw [hs, hx, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hFx, mul_assoc]

end GlobalTheory
