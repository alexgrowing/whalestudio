import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IwahoriProjSurjective

open GlobalTheory.PRep GlobalTheory.SmGL
open scoped TensorProduct Topology

namespace GlobalTheory.CompanionTheory.EvalTensor

variable {G S V : Type} [Group G] [AddCommGroup S] [Module ℂ S] [AddCommGroup V] [Module ℂ V]

theorem eq_zero_of_sum_apply_eq_zero (σ : Representation ℂ G S) (π : Representation ℂ G V)
    (hirr : σ.IsIrreducible)
    (hschur : ∀ A : S →ₗ[ℂ] S, (∀ g s, A (σ g s) = σ g (A s)) → ∃ c : ℂ, A = c • LinearMap.id)
    {ι : Type} (b : ι → (S →ₗ[ℂ] V)) (hli : LinearIndependent ℂ b)
    (hb : ∀ i g s, b i (σ g s) = π g (b i s)) (J : Finset ι) :
    ∀ t : ι → S, ∑ j ∈ J, b j (t j) = 0 → ∀ j ∈ J, t j = 0 := by
  classical
  haveI : IsSimpleOrder (Subrepresentation σ) := hirr
  induction J using Finset.induction_on with
  | empty => intro t _ j hj; simp at hj
  | insert a J ha ih =>
    intro t ht
    rw [Finset.sum_insert ha] at ht
    have hta : t a = 0 := by
      by_contra hne
      let Φ : (J → S) →ₗ[ℂ] V := ∑ j : J, (b j.1).comp (LinearMap.proj j)
      have hΦ : ∀ f : J → S, Φ f = ∑ j : J, b j.1 (f j) := fun f => by
        simp [Φ, LinearMap.sum_apply]
      have hinj : Function.Injective Φ := by
        rw [injective_iff_map_eq_zero]
        intro f hf
        rw [hΦ] at hf
        funext j
        have h0 := ih (fun i => if h : i ∈ J then f ⟨i, h⟩ else 0) (by
          rw [← Finset.sum_coe_sort J]
          simpa using hf) j.1 j.2
        simpa using h0
      have hequi : ∀ (g : G) (f : J → S), Φ (fun j => σ g (f j)) = π g (Φ f) := fun g f => by
        rw [hΦ, hΦ, map_sum]
        exact Finset.sum_congr rfl fun j _ => hb j.1 g (f j)
      let W : Subrepresentation σ :=
        { toSubmodule := (LinearMap.range Φ).comap (b a)
          apply_mem_toSubmodule := by
            rintro g v ⟨f, hf⟩
            exact ⟨fun j => σ g (f j), by rw [hequi, hf, hb]⟩ }
      have hmem : t a ∈ W := by
        refine ⟨fun j => - t j.1, ?_⟩
        rw [hΦ]
        have h1 : ∑ j : J, b j.1 (- t j.1) = - ∑ j ∈ J, b j (t j) := by
          rw [← Finset.sum_coe_sort J, ← Finset.sum_neg_distrib]
          exact Finset.sum_congr rfl fun j _ => map_neg _ _
        rw [h1]
        exact (eq_neg_of_add_eq_zero_left ht).symm ▸ rfl
      have htop : W = ⊤ := by
        rcases IsSimpleOrder.eq_bot_or_eq_top W with h | h
        · exfalso
          apply hne
          rw [h] at hmem
          exact hmem
        · exact h
      have hall : ∀ s, b a s ∈ LinearMap.range Φ := fun s => by
        have : s ∈ W := by rw [htop]; trivial
        exact this
      let e := LinearEquiv.ofInjective Φ hinj
      let B : S →ₗ[ℂ] (J → S) := e.symm.toLinearMap ∘ₗ (b a).codRestrict (LinearMap.range Φ) hall
      have hB : ∀ s, Φ (B s) = b a s := fun s => by
        have h1 : ((e (B s) : LinearMap.range Φ) : V) = Φ (B s) := LinearEquiv.ofInjective_apply _ _
        rw [← h1]
        simp [B]
      have hBc : ∀ g s, B (σ g s) = fun j => σ g (B s j) := fun g s => by
        apply hinj
        rw [hB, hequi, hB, hb]
      have hsc : ∀ j : J, ∃ c : ℂ, (LinearMap.proj j) ∘ₗ B = c • (LinearMap.id : S →ₗ[ℂ] S) := fun j =>
        hschur _ fun g s => by
          simp only [LinearMap.comp_apply, LinearMap.proj_apply]
          rw [hBc]
      choose c hc using hsc
      have hsum : b a = ∑ j : J, c j • b j.1 := by
        ext s
        rw [← hB, hΦ, LinearMap.sum_apply]
        refine Finset.sum_congr rfl fun j _ => ?_
        have h1 : B s j = c j • s := by
          simpa using LinearMap.congr_fun (hc j) s
        rw [h1, map_smul, LinearMap.smul_apply]
      refine hli.notMem_span_image (s := (J : Set ι)) (x := a) (by simpa using ha) ?_
      rw [hsum]
      exact Submodule.sum_mem _ fun j _ =>
        Submodule.smul_mem _ _ (Submodule.subset_span ⟨j.1, j.2, rfl⟩)
    have hrest : ∑ j ∈ J, b j (t j) = 0 := by
      simpa [hta] using ht
    intro j hj
    rcases Finset.mem_insert.1 hj with rfl | hj
    · exact hta
    · exact ih t hrest j hj

theorem lift_flip_subtype_injective : ∀ {G S V : Type} [Group G] [AddCommGroup S] [Module ℂ S] [AddCommGroup V] [Module ℂ V] (σ : Representation ℂ G S) (π : Representation ℂ G V), σ.IsIrreducible → (∀ A : S →ₗ[ℂ] S, (∀ g s, A (σ g s) = σ g (A s)) → ∃ c : ℂ, A = c • LinearMap.id) → ∀ M : Submodule ℂ (S →ₗ[ℂ] V), (∀ f ∈ M, ∀ g s, f (σ g s) = π g (f s)) → Function.Injective (TensorProduct.lift (LinearMap.flip (M.subtype)) : S ⊗[ℂ] M →ₗ[ℂ] V) := by
  intro G S V _ _ _ _ _ σ π hirr hschur M hM
  classical
  let β := Module.Basis.ofVectorSpace ℂ M
  have hli : LinearIndependent ℂ (fun i => ((β i : M) : S →ₗ[ℂ] V)) :=
    β.linearIndependent.map' M.subtype (Submodule.ker_subtype M)
  rw [injective_iff_map_eq_zero]
  intro x hx
  let E := TensorProduct.equivFinsuppOfBasisRight (M := S) β
  have hxs : x = (E x).sum fun i s => s ⊗ₜ[ℂ] β i := by
    rw [← TensorProduct.equivFinsuppOfBasisRight_symm_apply, LinearEquiv.symm_apply_apply]
  have hsum : ∑ i ∈ (E x).support, ((β i : M) : S →ₗ[ℂ] V) (E x i) = 0 := by
    rw [hxs, Finsupp.sum, map_sum] at hx
    simpa using hx
  have h0 := eq_zero_of_sum_apply_eq_zero σ π hirr hschur _ hli
    (fun i g s => hM _ (β i).2 g s) (E x).support (fun i => E x i) hsum
  have hE : E x = 0 := by
    ext i
    by_cases hi : i ∈ (E x).support
    · simpa using h0 i hi
    · simpa using hi
  exact E.map_eq_zero_iff.1 hE

end GlobalTheory.CompanionTheory.EvalTensor
