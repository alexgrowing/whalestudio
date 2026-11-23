import Mathlib

open Polynomial
namespace GlobalTheory
theorem finrank_le_of_first_order_kernel (k V U : Type) [Field k] [AddCommGroup V] [Module k V] [Module.Finite k V]
    [AddCommGroup U] [Module k U] [Module.Finite k U] (e : ℕ) (t u : V →ₗ[k] U)
    (h : ∀ x0 x1 : Fin (e + 1) → V, (∀ j, t (x0 j) = 0 ∧ t (x1 j) = u (x0 j)) → ¬ LinearIndependent k x0) :
    Module.finrank k V ≤ Module.finrank k U + e := by
  classical
  set q : LinearMap.ker t →ₗ[k] U ⧸ LinearMap.range t :=
    (LinearMap.range t).mkQ ∘ₗ u ∘ₗ (LinearMap.ker t).subtype

  have hq : Module.finrank k (LinearMap.ker q) ≤ e := by
    by_contra hlt
    push_neg at hlt
    obtain ⟨f, hf⟩ := exists_linearIndependent_of_le_finrank (R := k) (M := LinearMap.ker q)
      (n := e + 1) hlt
    have hmem : ∀ j, u ((f j : LinearMap.ker t) : V) ∈ LinearMap.range t := by
      intro j
      have hj : (LinearMap.range t).mkQ (u ((f j : LinearMap.ker t) : V)) = 0 :=
        LinearMap.mem_ker.mp (f j).2
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hj
      exact hj
    choose y hy using fun j => LinearMap.mem_range.mp (hmem j)
    have hli : LinearIndependent k (fun j => ((f j : LinearMap.ker t) : V)) :=
      (hf.map' _ (Submodule.ker_subtype _)).map' _ (Submodule.ker_subtype _)
    exact h (fun j => ((f j : LinearMap.ker t) : V)) y
      (fun j => ⟨LinearMap.mem_ker.mp (f j : LinearMap.ker t).2, hy j⟩) hli
  have h1 := LinearMap.finrank_range_add_finrank_ker t
  have h2 := LinearMap.finrank_range_add_finrank_ker q
  have h3 := Submodule.finrank_le (LinearMap.range q)
  have h4 := Submodule.finrank_quotient_add_finrank (LinearMap.range t)
  omega

theorem rank_le_rank_map_algebraMap (k K : Type) [Field k] [Field K] [Algebra k K] (a : ℕ)
    (Φ : Matrix (Fin a) (Fin a) k) : Φ.rank ≤ (Φ.map (algebraMap k K)).rank := by
  classical
  obtain ⟨f, hf⟩ := exists_linearIndependent_of_le_finrank (R := k)
    (M := LinearMap.range Φ.mulVecLin) (n := Φ.rank) le_rfl
  have hv : LinearIndependent k (fun i => ((f i : LinearMap.range Φ.mulVecLin) : Fin a → k)) :=
    hf.map' _ (Submodule.ker_subtype _)

  have hw : LinearIndependent K
      (fun i => algebraMap k K ∘ ((f i : LinearMap.range Φ.mulVecLin) : Fin a → k)) :=
    linearIndependent_algebraMap_comp_iff.mpr hv
  have hmem : ∀ i, algebraMap k K ∘ ((f i : LinearMap.range Φ.mulVecLin) : Fin a → k) ∈
      LinearMap.range (Φ.map (algebraMap k K)).mulVecLin := by
    intro i
    obtain ⟨y, hy⟩ := LinearMap.mem_range.mp (f i).2
    refine ⟨algebraMap k K ∘ y, ?_⟩
    rw [← hy]
    funext j
    simp only [Matrix.mulVecLin_apply, Function.comp_apply]
    exact (RingHom.map_mulVec _ _ _ j).symm
  let g : Fin Φ.rank → LinearMap.range (Φ.map (algebraMap k K)).mulVecLin := fun i => ⟨_, hmem i⟩
  have hg : LinearIndependent K g := LinearIndependent.of_comp (LinearMap.range _).subtype hw
  have hc := hg.fintype_card_le_finrank
  rw [Fintype.card_fin] at hc
  exact hc

theorem finrank_ker_map_le_of_first_order_kernel : ∀ (k K : Type) [Field k] [Field K] [Algebra k K] (a e : ℕ) (Φ : Matrix (Fin a) (Fin a) k) (U : Type) [AddCommGroup U] [Module k U] [Module.Finite k U] (t u : LinearMap.ker Φ.mulVecLin →ₗ[k] U), (∀ x0 x1 : Fin (e + 1) → LinearMap.ker Φ.mulVecLin, (∀ j, t (x0 j) = 0 ∧ t (x1 j) = u (x0 j)) → ¬ LinearIndependent k x0) → Module.finrank K (LinearMap.ker (Φ.map (algebraMap k K)).mulVecLin) ≤ Module.finrank k U + e := by
  intro k K _ _ _ a e Φ U _ _ _ t u h
  have h1 := finrank_le_of_first_order_kernel k (LinearMap.ker Φ.mulVecLin) U e t u h
  have h2 := rank_le_rank_map_algebraMap k K a Φ
  have hk := LinearMap.finrank_range_add_finrank_ker Φ.mulVecLin
  have hK := LinearMap.finrank_range_add_finrank_ker (Φ.map (algebraMap k K)).mulVecLin
  rw [Module.finrank_fin_fun] at hk hK
  unfold Matrix.rank at h2
  omega
end GlobalTheory
