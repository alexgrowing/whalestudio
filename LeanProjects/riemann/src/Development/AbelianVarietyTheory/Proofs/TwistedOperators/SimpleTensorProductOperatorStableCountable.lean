import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SimpleOver
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DixmierSchurOfRankLeAleph0

open scoped TensorProduct

namespace GlobalTheory.TensHead

theorem exists_adjoin_agree {V : Type} [AddCommGroup V] [Module ℂ V] [Nontrivial V]
    (A : Set (Module.End ℂ V)) (hrank : Module.rank ℂ V ≤ Cardinal.aleph0)
    (hA : ∀ U : Submodule ℂ V, Stab A U → U = ⊥ ∨ U = ⊤) (p : Module.End ℂ V) (s : Finset V) :
    ∃ r ∈ Algebra.adjoin ℂ A, ∀ m ∈ s, p m = r m := by
  set R := Algebra.adjoin ℂ A with hR
  haveI : IsSimpleModule R V := by
    rw [isSimpleModule_iff]
    refine { eq_bot_or_eq_top := fun N => ?_ }
    have h := hA (N.restrictScalars ℂ) (fun g hg x hx =>
      N.smul_mem (⟨g, Algebra.subset_adjoin hg⟩ : R) hx)
    rcases h with h | h
    · left; exact (Submodule.restrictScalars_eq_bot_iff ℂ R V).1 h
    · right; exact (Submodule.restrictScalars_eq_top_iff ℂ R V).1 h
  have hsc : ∀ φ : Module.End R V, ∃ c : ℂ, ∀ x, φ x = c • x := by
    intro φ
    obtain ⟨c, hc⟩ := GlobalTheory.dixmier_schur_of_rank_le_aleph0 V A (fun g => g.1)
      (LinearMap.restrictScalars ℂ φ) inferInstance hrank
      (fun N hN => hA N (fun g hg x hx => hN ⟨g, hg⟩ x hx))
      (fun g => LinearMap.ext fun x =>
        φ.map_smul (⟨g.1, Algebra.subset_adjoin g.2⟩ : R) x)
    exact ⟨c, fun x => LinearMap.congr_fun hc x⟩
  let f : Module.End (Module.End R V) V :=
    { toFun := p
      map_add' := p.map_add
      map_smul' := fun φ x => by
        obtain ⟨c, hc⟩ := hsc φ
        change p (φ x) = φ (p x)
        rw [hc, hc, map_smul] }
  obtain ⟨r, hr⟩ := jacobson_density f s
  exact ⟨r.1, r.2, hr⟩

theorem simple_tensor :
    ∀ {S₀ S₁ : Type} [AddCommGroup S₀] [Module ℂ S₀] [AddCommGroup S₁] [Module ℂ S₁]
    (A : Set (Module.End ℂ S₀)) (B : Set (Module.End ℂ S₁)),
    Module.rank ℂ S₀ ≤ Cardinal.aleph0 →
    (∀ U : Submodule ℂ S₀, GlobalTheory.TensHead.Stab A U → U = ⊥ ∨ U = ⊤) →
    (∀ U : Submodule ℂ S₁, GlobalTheory.TensHead.Stab B U → U = ⊥ ∨ U = ⊤) →
    ∀ U : Submodule ℂ (S₀ ⊗[ℂ] S₁), GlobalTheory.TensHead.Stab (GlobalTheory.TensHead.tensOps A B) U →
      U = ⊥ ∨ U = ⊤ := by
  classical
  intro S₀ S₁ _ _ _ _ A B hrank hA hB U hU
  rcases eq_or_ne U ⊥ with h0 | h0
  · exact Or.inl h0
  right
  obtain ⟨t, htU, ht0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h0
  have hadj : ∀ r ∈ Algebra.adjoin ℂ A, ∀ z ∈ U, TensorProduct.map r LinearMap.id z ∈ U := by
    intro r hr
    induction hr using Algebra.adjoin_induction with
    | mem g hg => exact hU _ (Or.inl ⟨g, hg, rfl⟩)
    | algebraMap c =>
      intro z hz
      rw [Algebra.algebraMap_eq_smul_one, TensorProduct.map_smul_left, LinearMap.smul_apply,
        Module.End.one_eq_id, TensorProduct.map_id]
      exact U.smul_mem c hz
    | add f g _ _ hf hg =>
      intro z hz
      rw [TensorProduct.map_add_left]
      exact U.add_mem (hf z hz) (hg z hz)
    | mul f g _ _ hf hg =>
      intro z hz
      have : TensorProduct.map (f * g) (LinearMap.id : S₁ →ₗ[ℂ] S₁) =
          (TensorProduct.map f LinearMap.id) ∘ₗ (TensorProduct.map g LinearMap.id) := by
        rw [← TensorProduct.map_comp]; rfl
      rw [this]
      exact hf _ (hg z hz)
  let b := Module.Basis.ofVectorSpace ℂ S₀
  set c := TensorProduct.equivFinsuppOfBasisLeft b t with hc
  have ht : t = c.sum fun i n => b i ⊗ₜ[ℂ] n := by
    rw [hc, ← TensorProduct.equivFinsuppOfBasisLeft_symm_apply, LinearEquiv.symm_apply_apply]
  have hc0 : c ≠ 0 := by
    intro h
    apply ht0
    rw [ht, h, Finsupp.sum_zero_index]
  obtain ⟨i, hi⟩ := Finsupp.support_nonempty_iff.2 hc0
  have hbi : b i ≠ 0 := b.ne_zero i
  haveI : Nontrivial S₀ := ⟨⟨b i, 0, hbi⟩⟩
  obtain ⟨r, hr, hrp⟩ := exists_adjoin_agree A hrank hA ((b.coord i).smulRight (b i))
    (c.support.image b)
  have h1 : b i ⊗ₜ[ℂ] c i ∈ U := by
    have h2 := hadj r hr t htU
    have h3 : TensorProduct.map r LinearMap.id t = b i ⊗ₜ[ℂ] c i := by
      conv_lhs => rw [ht]
      rw [Finsupp.sum, map_sum, Finset.sum_eq_single i]
      · rw [TensorProduct.map_tmul, ← hrp _ (Finset.mem_image_of_mem b hi)]
        simp
      · intro j hj hji
        rw [TensorProduct.map_tmul, ← hrp _ (Finset.mem_image_of_mem b hj)]
        simp [Finsupp.single_apply, hji]
      · intro h; exact absurd hi h
    rwa [h3] at h2
  have h4 : U.comap (TensorProduct.mk ℂ S₀ S₁ (b i)) = ⊤ := by
    refine (hB _ ?_).resolve_left ?_
    · intro g hg y hy
      exact hU _ (Or.inr ⟨g, hg, rfl⟩) _ hy
    · intro h
      have : c i ∈ U.comap (TensorProduct.mk ℂ S₀ S₁ (b i)) := h1
      rw [h, Submodule.mem_bot] at this
      exact Finsupp.mem_support_iff.1 hi this
  have h5 : ∀ y, U.comap ((TensorProduct.mk ℂ S₀ S₁).flip y) = ⊤ := by
    intro y
    refine (hA _ ?_).resolve_left ?_
    · intro g hg x hx
      exact hU _ (Or.inl ⟨g, hg, rfl⟩) _ hx
    · intro h
      have h6 : y ∈ U.comap (TensorProduct.mk ℂ S₀ S₁ (b i)) := by rw [h4]; trivial
      have : b i ∈ U.comap ((TensorProduct.mk ℂ S₀ S₁).flip y) := h6
      rw [h, Submodule.mem_bot] at this
      exact hbi this
  rw [eq_top_iff]
  rintro z -
  induction z using TensorProduct.induction_on with
  | zero => exact U.zero_mem
  | tmul x y =>
    have : x ∈ U.comap ((TensorProduct.mk ℂ S₀ S₁).flip y) := by rw [h5]; trivial
    exact this
  | add x y hx hy => exact U.add_mem hx hy

end GlobalTheory.TensHead
