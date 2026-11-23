import Mathlib

open scoped Classical

namespace GlobalTheory.RightInvCompl

noncomputable def splitEquiv {K V W : Type} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] (f : V →ₗ[K] W) (s : W →ₗ[K] V) (h : ∀ w, f (s w) = w) :
    V ≃ₗ[K] (LinearMap.ker f × W) where
  toFun v := (⟨v - s (f v), by simp [h]⟩, f v)
  invFun p := p.1.1 + s p.2
  map_add' x y := by
    ext
    · simp; abel
    · simp
  map_smul' a x := by
    ext
    · simp [smul_sub]
    · simp
  left_inv v := by simp
  right_inv p := by
    have hp : f p.1.1 = 0 := p.1.2
    ext
    · simp [h, hp]
    · simp [h, hp]

theorem exists_equiv {K V W : Type} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] [FiniteDimensional K V]
    (f f' : V →ₗ[K] W) (s s' : W →ₗ[K] V) (h : ∀ w, f (s w) = w) (h' : ∀ w, f' (s' w) = w) :
    ∃ e : V ≃ₗ[K] V, ∀ v, f (e v) = f' v := by
  have r : LinearMap.range f = ⊤ := LinearMap.range_eq_top.2 (fun w => ⟨_, h w⟩)
  have r' : LinearMap.range f' = ⊤ := LinearMap.range_eq_top.2 (fun w => ⟨_, h' w⟩)
  have a := LinearMap.finrank_range_add_finrank_ker f
  have a' := LinearMap.finrank_range_add_finrank_ker f'
  rw [r] at a
  rw [r'] at a'
  have hk : Module.finrank K (LinearMap.ker f') = Module.finrank K (LinearMap.ker f) := by omega
  let k := LinearEquiv.ofFinrankEq _ _ hk
  refine ⟨(splitEquiv f' s' h').trans ((k.prodCongr (LinearEquiv.refl K W)).trans
    (splitEquiv f s h).symm), fun v => ?_⟩
  have hz : ∀ x : LinearMap.ker f, f x.1 = 0 := fun x => x.2
  show f ((k _).1 + s (f' v)) = f' v
  rw [map_add, hz, h, zero_add]

theorem exists_mul_eq_inclusion : ∀ (K : Type) [Field K] (N n : ℕ) (g : Matrix (Fin N) (Fin n) K) (c : Matrix (Fin n) (Fin N) K), g * c = 1 →
    N ≤ n ∧ ∃ M P : Matrix (Fin n) (Fin n) K, M * P = 1 ∧ P * M = 1 ∧ g * M = (Matrix.of fun (j : Fin N) (k : Fin n) => if (j : ℕ) = (k : ℕ) then (1 : K) else 0) := by
  intro K _ N n g c hgc
  have h : ∀ w, Matrix.toLin' g (Matrix.toLin' c w) = w := by
    intro w
    simp [Matrix.mulVec_mulVec, hgc]
  have hle : N ≤ n := by
    have := LinearMap.finrank_le_finrank_of_surjective (f := Matrix.toLin' g) (fun w => ⟨_, h w⟩)
    simpa using this
  refine ⟨hle, ?_⟩
  set J : Matrix (Fin N) (Fin n) K :=
    Matrix.of fun (j : Fin N) (k : Fin n) => if (j : ℕ) = (k : ℕ) then (1 : K) else 0 with hJ
  have hJJ : J * J.transpose = 1 := by
    ext i j
    rw [Matrix.mul_apply, Finset.sum_eq_single (Fin.castLE hle i)]
    · simp [hJ, Matrix.one_apply, Fin.ext_iff, eq_comm]
    · intro b _ hb
      have : (i : ℕ) ≠ b := fun e => hb (Fin.ext e.symm)
      simp [hJ, this]
    · simp
  have h' : ∀ w, Matrix.toLin' J (Matrix.toLin' J.transpose w) = w := by
    intro w
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply, Matrix.mulVec_mulVec, hJJ, Matrix.one_mulVec]
  obtain ⟨e, he⟩ := exists_equiv _ _ _ _ h h'
  refine ⟨LinearMap.toMatrix' e.toLinearMap, LinearMap.toMatrix' e.symm.toLinearMap, ?_, ?_, ?_⟩
  · rw [← LinearMap.toMatrix'_comp]; simp
  · rw [← LinearMap.toMatrix'_comp]; simp
  · apply Matrix.toLin'.injective
    rw [Matrix.toLin'_mul, Matrix.toLin'_toMatrix']
    exact LinearMap.ext he

end GlobalTheory.RightInvCompl
