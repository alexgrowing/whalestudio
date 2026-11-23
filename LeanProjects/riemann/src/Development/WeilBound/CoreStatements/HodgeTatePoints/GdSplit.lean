import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LeadMinor

open Module NumberField GlobalTheory.CompanionTheory.Ar.HT TensorProduct

noncomputable section

namespace PositivityTheory.HtPt.Gd

private theorem isTorsionFree_of_projective {A P : Type*} [CommRing A] [AddCommGroup P] [Module A P]
    [Module.Projective A P] : Module.IsTorsionFree A P := by
  obtain ⟨s, hs⟩ := Module.projective_def'.mp ‹Module.Projective A P›
  have hinj : Function.Injective s :=
    Function.LeftInverse.injective (g := Finsupp.linearCombination A id)
      (fun x => LinearMap.congr_fun hs x)
  refine ⟨fun r hr p p' h => hinj ?_⟩
  have h' : r • s p = r • s p' := by
    rw [← map_smul, ← map_smul]
    exact congrArg s h
  ext x
  have hx := congrArg (fun g => g x) h'
  simp only [Finsupp.smul_apply, smul_eq_mul] at hx
  exact hr.left hx

theorem inj_mod_of_surj_mod {A : Type} [CommRing A] [IsDomain A] {P : Type} [AddCommGroup P]
    [Module A P] [Module.Finite A P] [Module.IsTorsionFree A P] {N : ℕ} (a : A)
    (φ : (Fin N → A) →ₗ[A] P) (hN : (N : Cardinal) ≤ Module.rank A P)
    (hs : ∀ y, ∃ x y', y = φ x + a • y') (x : Fin N → A) (y : P) (hx : φ x = a • y) :
    ∃ x', x = a • x' := by
  haveI : Module.IsTorsionFree A (Fin N → A) := isTorsionFree_of_projective
  obtain ⟨r, hr1, hrP⟩ := Submodule.exists_sub_one_mem_and_smul_le_of_fg_of_le_sup
    (I := Ideal.span {a}) (N := LinearMap.range φ) (Module.Finite.fg_top (R := A) (M := P)) le_rfl
    (by
      intro z _
      obtain ⟨x₀, z', rfl⟩ := hs z
      exact Submodule.add_mem_sup (LinearMap.mem_range_self φ x₀)
        (Submodule.smul_mem_smul (Ideal.mem_span_singleton_self a) Submodule.mem_top))
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hr1
  by_cases hr : r = 0
  · refine ⟨-(c • x), ?_⟩
    rw [smul_neg, smul_smul, mul_comm, hc, hr]
    simp
  have hrange : ∀ p : P, r • p ∈ LinearMap.range φ := fun p =>
    hrP (Submodule.smul_mem_pointwise_smul p r ⊤ Submodule.mem_top)
  let f : P →ₗ[A] LinearMap.range φ :=
    LinearMap.codRestrict (LinearMap.range φ) (r • LinearMap.id) (fun p => hrange p)
  have hf : Function.Injective f := by
    intro p p' h
    have h' : r • p = r • p' := congrArg Subtype.val h
    exact smul_right_injective P hr h'
  have hrk : (N : Cardinal) ≤ Module.rank A (LinearMap.range φ) :=
    hN.trans (LinearMap.rank_le_of_injective f hf)
  have hsum := LinearMap.rank_range_add_rank_ker φ
  rw [rank_fin_fun] at hsum
  have hker : Module.rank A (LinearMap.ker φ) = 0 := by
    have hle : Module.rank A (LinearMap.range φ) ≤ N := by
      rw [← hsum]
      exact le_self_add
    rw [le_antisymm hle hrk, add_comm] at hsum
    exact (Cardinal.add_right_inj_of_lt_aleph0 Cardinal.natCast_lt_aleph0).mp (by rw [hsum, zero_add])
  have hinj : Function.Injective φ := LinearMap.ker_eq_bot.mp (Submodule.rank_eq_zero.mp hker)
  obtain ⟨z, hz⟩ := hrange y
  have hxz : r • x = a • z :=
    hinj (by rw [map_smul, map_smul, hx, hz, smul_smul, smul_smul, mul_comm])
  refine ⟨z - c • x, ?_⟩
  rw [smul_sub, ← hxz, smul_smul, ← sub_smul, mul_comm a c, hc]
  simp

theorem split_exact : ∀ (A : Type) [CommRing A] [IsDomain A] (P₁ P₂ : Type) [AddCommGroup P₁] [Module A P₁] [Module.Finite A P₁] [Module.Projective A P₁] [AddCommGroup P₂] [Module A P₂] [Module.Finite A P₂] [Module.Projective A P₂] (N : ℕ) (a : A) (i : P₁ →ₗ[A] (Fin N → A)) (r : (Fin N → A) →ₗ[A] P₁) (q : (Fin N → A) →ₗ[A] P₂), Module.finrank A P₁ + Module.finrank A P₂ = N → (∀ w, ∃ w', r (i w) = w + a • w') → (∀ y, ∃ x y', y = q x + a • y') → (∀ w, ∃ y, q (i w) = a • y) → ∀ x, (∃ y, q x = a • y) → ∃ w x', x = i w + a • x' := by
  intro A _ _ P₁ P₂ _ _ _ _ _ _ _ _ N a i r q hrank hri hq hqi x hx
  haveI : Module.IsTorsionFree A (P₁ × P₂) := isTorsionFree_of_projective
  have hN : (N : Cardinal) ≤ Module.rank A (P₁ × P₂) := by
    rw [← hrank, Nat.cast_add, Module.finrank_eq_rank, Module.finrank_eq_rank]
    exact rank_add_rank_le_rank_prod A P₁
  have hs : ∀ y : P₁ × P₂, ∃ x y', y = (r.prod q) x + a • y' := by
    rintro ⟨w, y⟩
    obtain ⟨x₀, y₀, rfl⟩ := hq y
    obtain ⟨w', hw'⟩ := hri (w - r x₀)
    obtain ⟨y'', hy''⟩ := hqi (w - r x₀)
    refine ⟨x₀ + i (w - r x₀), (-w', y₀ - y''), Prod.ext ?_ ?_⟩
    · show w = r (x₀ + i (w - r x₀)) + a • -w'
      rw [map_add, hw', smul_neg]
      abel
    · show q x₀ + a • y₀ = q (x₀ + i (w - r x₀)) + a • (y₀ - y'')
      rw [map_add, hy'', smul_sub]
      abel
  obtain ⟨w', hw'⟩ := hri (r x)
  obtain ⟨y'', hy''⟩ := hqi (r x)
  obtain ⟨y, hy⟩ := hx
  have hφ : (r.prod q) (x - i (r x)) = a • (-w', y - y'') := by
    refine Prod.ext ?_ ?_
    · show r (x - i (r x)) = a • -w'
      rw [map_sub, hw', smul_neg]
      abel
    · show q (x - i (r x)) = a • (y - y'')
      rw [map_sub, hy, hy'', smul_sub]
  obtain ⟨x', hx'⟩ := PositivityTheory.HtPt.Gd.inj_mod_of_surj_mod a (r.prod q) hN hs _ _ hφ
  refine ⟨r x, x', ?_⟩
  rw [← hx']
  abel

end PositivityTheory.HtPt.Gd
