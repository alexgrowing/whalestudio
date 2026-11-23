import Mathlib
import Development.AbelianVarietyTheory.Proofs.HermitianTraceForms.IsLocallyConstantRankAtStalkEigenSub

open scoped TensorProduct
open GlobalTheory.EigenSplit

namespace GlobalTheory.EigenLine

variable {K : Type} [Field K] {O : Type} [CommRing O] {L : Type} [AddCommGroup L] [Module K L]

theorem action_one_tmul (ρ : O →+* Module.End K L) (a : O) :
    tensorAction ρ ((1 : K) ⊗ₜ[ℤ] a) = ρ a := by
  ext x
  simp

theorem action_mem (ρ : O →+* Module.End K L) (P : Submodule K L)
    (hP : ∀ a, ∀ x ∈ P, ρ a x ∈ P) (t : K ⊗[ℤ] O) : ∀ x ∈ P, tensorAction ρ t x ∈ P := by
  induction t using TensorProduct.induction_on with
  | zero => intro x _; simp
  | tmul r a => intro x hx; rw [tensorAction_tmul]; exact P.smul_mem _ (hP a x hx)
  | add s t hs ht =>
    intro x hx
    rw [map_add, LinearMap.add_apply]
    exact P.add_mem (hs x hx) (ht x hx)

theorem action_eigen_right (ρ : O →+* Module.End K L) (χ : O →+* K) (ε : K ⊗[ℤ] O)
    (hε : ∀ a, ε * ((1 : K) ⊗ₜ[ℤ] a) = χ a • ε) (a : O) (x : L) :
    tensorAction ρ ε (ρ a x) = χ a • tensorAction ρ ε x := by
  have h := congrArg (fun t => tensorAction ρ t x) (hε a)
  simpa only [map_mul, Module.End.mul_apply, action_one_tmul, map_smul,
    LinearMap.smul_apply] using h

theorem action_eigen_left (ρ : O →+* Module.End K L) (χ : O →+* K) (ε : K ⊗[ℤ] O)
    (hε : ∀ a, ε * ((1 : K) ⊗ₜ[ℤ] a) = χ a • ε) (a : O) (x : L) :
    ρ a (tensorAction ρ ε x) = χ a • tensorAction ρ ε x := by
  have h := congrArg (fun t => tensorAction ρ t x) ((mul_comm _ _).trans (hε a))
  simpa only [map_mul, Module.End.mul_apply, action_one_tmul, map_smul,
    LinearMap.smul_apply] using h

noncomputable def twist (c : O →+* O) : K ⊗[ℤ] O →ₐ[ℤ] K ⊗[ℤ] O :=
  Algebra.TensorProduct.map (AlgHom.id ℤ K) c.toIntAlgHom

theorem twist_twist (c : O →+* O) (hcc : ∀ a, c (c a) = a) (t : K ⊗[ℤ] O) :
    twist c (twist c t) = t := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul r a => simp [twist, hcc]
  | add s t hs ht => simp only [map_add, hs, ht]

theorem form_action (ρ : O →+* Module.End K L) (c : O →+* O) (B : LinearMap.BilinForm K L)
    (hadj : ∀ a x y, B x (ρ a y) = B (ρ (c a) x) y) (t : K ⊗[ℤ] O) (x y : L) :
    B x (tensorAction ρ t y) = B (tensorAction ρ (twist c t) x) y := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul r a => simp [twist, hadj]
  | add s t hs ht => simp only [map_add, LinearMap.add_apply, hs, ht]

theorem finrank_ker_add_one {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (f : V →ₗ[K] K) (hf : f ≠ 0) :
    Module.finrank K (LinearMap.ker f) + 1 = Module.finrank K V := by
  obtain ⟨y, hy⟩ : ∃ y, f y ≠ 0 := by
    by_contra h
    push_neg at h
    exact hf (LinearMap.ext h)
  have htop : LinearMap.range f = ⊤ := by
    refine LinearMap.range_eq_top.2 fun k => ⟨(k / f y) • y, ?_⟩
    rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hy]
  have h := LinearMap.finrank_range_add_finrank_ker f
  rw [htop, finrank_top, Module.finrank_self] at h
  omega

theorem line_hyperplane_cut (K : Type) [Field K] (O : Type) [CommRing O] (L : Type)
    [AddCommGroup L] [Module K L]
    [FiniteDimensional K L] (ρ : O →+* Module.End K L) (c : O →+* O) (B : LinearMap.BilinForm K L)
    (χ : O →+* K) (ε : K ⊗[ℤ] O) (M M' : Submodule K L) (n₀ : L)
    (hcc : ∀ a, c (c a) = a) (hadj : ∀ a x y, B x (ρ a y) = B (ρ (c a) x) y)
    (hnd : ∀ x, (∀ y, B x y = 0) → x = 0)
    (hε : ∀ a, ε * ((1 : K) ⊗ₜ[ℤ] a) = χ a • ε) (hε0 : ε ≠ 0) (hMM : IsCompl M M')
    (hM : ∀ a, ∀ x ∈ M, ρ a x ∈ M) (hM' : ∀ a, ∀ x ∈ M', ρ a x ∈ M')
    (hspan : M = Submodule.span K (Set.range fun a => ρ a n₀))
    (hinj : ∀ t : K ⊗[ℤ] O, tensorAction ρ t n₀ = 0 → t = 0) :
    Module.finrank K ↥(M ⊓ LinearMap.range (tensorAction ρ ε)) = 1 ∧
    Module.finrank K ↥(B.orthogonal M ⊓ LinearMap.range (tensorAction ρ ε)) + 1 =
      Module.finrank K ↥(LinearMap.range (tensorAction ρ ε)) := by
  set T := tensorAction ρ ε with hT
  set E := LinearMap.range T with hE
  have hn₀ : n₀ ∈ M := by
    rw [hspan]
    exact Submodule.subset_span ⟨1, by simp⟩
  have hTn : T n₀ ≠ 0 := fun h => hε0 (hinj ε h)

  have hTM : ∀ m ∈ M, T m ∈ K ∙ T n₀ := by
    intro m hm
    rw [hspan] at hm
    induction hm using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨a, rfl⟩ := hx
      have : T (ρ a n₀) = χ a • T n₀ := action_eigen_right ρ χ ε hε a n₀
      rw [this]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
    | zero => simp
    | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
    | smul r x _ hx => rw [map_smul]; exact Submodule.smul_mem _ _ hx
  have hline : M ⊓ E = K ∙ T n₀ := by
    apply le_antisymm
    · rintro x ⟨hxM, z, rfl⟩
      have hz : z ∈ M ⊔ M' := by rw [hMM.sup_eq_top]; trivial
      obtain ⟨m, hm, m', hm', rfl⟩ := Submodule.mem_sup.1 hz
      have h1 : T m' ∈ M' := action_mem ρ M' hM' ε m' hm'
      have h2 : T m ∈ M := action_mem ρ M hM ε m hm
      have h3 : T m' ∈ M := by
        have : T m' = T (m + m') - T m := by rw [map_add]; abel
        rw [this]
        exact M.sub_mem hxM h2
      have h4 : T m' = 0 := by
        have : T m' ∈ M ⊓ M' := ⟨h3, h1⟩
        rwa [hMM.inf_eq_bot, Submodule.mem_bot] at this
      rw [map_add, h4, add_zero]
      exact hTM m hm
    · rw [Submodule.span_singleton_le_iff_mem]
      exact ⟨action_mem ρ M hM ε n₀ hn₀, n₀, rfl⟩
  refine ⟨by rw [hline]; exact finrank_span_singleton hTn, ?_⟩

  let f : E →ₗ[K] K := (B n₀).comp E.subtype
  have hf : f ≠ 0 := by
    have h1 : twist c ε ≠ 0 := by
      intro h
      apply hε0
      rw [← twist_twist c hcc ε, h, map_zero]
    have h2 : tensorAction ρ (twist c ε) n₀ ≠ 0 := fun h => h1 (hinj _ h)
    obtain ⟨z, hz⟩ : ∃ z, B (tensorAction ρ (twist c ε) n₀) z ≠ 0 := by
      by_contra h
      push_neg at h
      exact h2 (hnd _ h)
    intro h0
    apply hz
    rw [← form_action ρ c B hadj]
    exact LinearMap.congr_fun h0 ⟨T z, z, rfl⟩
  have hmap : (LinearMap.ker f).map E.subtype = B.orthogonal M ⊓ E := by
    ext x
    constructor
    · rintro ⟨⟨y, hy⟩, hyk, rfl⟩
      refine ⟨?_, hy⟩
      change y ∈ B.orthogonal M
      rw [LinearMap.BilinForm.mem_orthogonal_iff]
      intro n hn
      have hy0 : B n₀ y = 0 := hyk
      rw [hspan] at hn
      induction hn using Submodule.span_induction with
      | mem n hn =>
        obtain ⟨a, rfl⟩ := hn
        obtain ⟨z, rfl⟩ := hy
        have h1 := hadj (c a) n₀ (T z)
        rw [hcc] at h1
        show B (ρ a n₀) (T z) = 0
        rw [← h1, action_eigen_left ρ χ ε hε, map_smul, hy0, smul_zero]
      | zero => simp [LinearMap.BilinForm.IsOrtho]
      | add u v _ _ hu hv =>
        simp only [LinearMap.BilinForm.IsOrtho, map_add, LinearMap.add_apply] at *
        rw [hu, hv, add_zero]
      | smul r u _ hu =>
        simp only [LinearMap.BilinForm.IsOrtho, map_smul, LinearMap.smul_apply] at *
        rw [hu, smul_zero]
    · rintro ⟨hx, hxE⟩
      refine ⟨⟨x, hxE⟩, ?_, rfl⟩
      have hx' : x ∈ B.orthogonal M := hx
      rw [LinearMap.BilinForm.mem_orthogonal_iff] at hx'
      exact hx' n₀ hn₀
  rw [← hmap, Submodule.finrank_map_subtype_eq]
  exact finrank_ker_add_one f hf

end GlobalTheory.EigenLine
