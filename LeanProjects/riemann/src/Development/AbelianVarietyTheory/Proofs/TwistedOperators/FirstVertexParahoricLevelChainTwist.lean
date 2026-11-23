import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.FramePositiveSum

open MeasureTheory ValuativeRel Matrix Topology GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum

noncomputable section
namespace GlobalTheory.TwistVertex

section Plain
variable {k : Type*} [Field k] {n : Type*} [Fintype n] [DecidableEq n] {c p : ℕ}

theorem toBlocks₁₁_eq_one {u : GL (n ⊕ Fin c) k} (hu : u ∈ N k n c p) : u.val.toBlocks₁₁ = 1 := by
  ext i j
  have := RootEx.Model.mem_N_iff.1 hu (.inl i) (.inl j) le_rfl
  simpa [toBlocks₁₁, Matrix.one_apply] using this

theorem val_embX (g : GL n k) : (embX c g).val = fromBlocks g.val 0 0 1 := rfl

end Plain

variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

section General
variable {n : Type*} [Fintype n] [DecidableEq n] {c p : ℕ}

theorem embX_mem_KO {g : GL n k} (hg : g ∈ KO k n) : embX c g ∈ KO k (n ⊕ Fin c) := by
  obtain ⟨h1, h2⟩ := mem_KO.1 hg
  refine mem_KO.2 ⟨?_, ?_⟩
  · rw [val_embX]; exact intM_fromBlocks.2 ⟨h1, intM_zero, intM_zero, intM_one⟩
  · rw [← map_inv, val_embX]; exact intM_fromBlocks.2 ⟨h2, intM_zero, intM_zero, intM_one⟩

theorem mem_KO_of_mul_embX {u : GL (n ⊕ Fin c) k} (hu : u ∈ N k n c p) {g : GL n k}
    (h : u * embX c g ∈ KO k (n ⊕ Fin c)) : g ∈ KO k n := by
  obtain ⟨h1, h2⟩ := mem_KO.1 h
  have e1 : (u * embX c g).val.toBlocks₁₁ = g.val := by
    rw [Units.val_mul, mul_toBlocks₁₁, toBlocks₁₁_eq_one hu, val_embX]; simp
  have e2 : ((u * embX c g)⁻¹).val.toBlocks₁₁ = (g⁻¹).val := by
    rw [_root_.mul_inv_rev, ← map_inv, Units.val_mul, mul_toBlocks₁₁, toBlocks₁₁_eq_one (inv_mem hu), val_embX]; simp
  exact mem_KO.2 ⟨e1 ▸ fun i j => h1 _ _, e2 ▸ fun i j => h2 _ _⟩

theorem simpleSum_mem {u : GL (n ⊕ Fin c) k} (hu : u ∈ KO k (n ⊕ Fin c)) : simpleSum u ∈ 𝒪[k] := by
  refine sum_mem fun i _ => sum_mem fun j _ => ?_
  split_ifs
  · exact intM_of_mem_KO hu _ _
  · exact zero_mem _

end General

section Empty
variable {r e n : Type*} [Fintype r] [DecidableEq r] [Fintype e] [DecidableEq e] [IsEmpty e]
  [Fintype n] [DecidableEq n] {c : ℕ} {δ : kˣ →* ℂˣ} {hδ : IsTame δ}

theorem mem_level_iff (o : r ⊕ e ≃ n ⊕ Fin c) (x : GL (n ⊕ Fin c) k) :
    x ∈ ((parahoric r e δ hδ).toLevel.map (plainFrame o).conj).J ↔ x ∈ KO k (n ⊕ Fin c) := by
  have e0 : ∀ y : GL (n ⊕ Fin c) k, ((plainFrame (k := k) o).conj.symm y).val = y.val.submatrix o o := by
    intro y
    have : (plainFrame (k := k) o).conj.symm y = (reGL o).symm y := by
      rw [MulEquiv.symm_apply_eq, LatFrame.conj_apply]; simp [plainFrame]
    rw [this, reGL_symm_val]
  rw [Level.mem_map, mem_parahoric, mem_KO, mem_KO, ← map_inv, e0, e0]
  refine ⟨fun ⟨⟨h1, h2⟩, _⟩ => ⟨fun i j => ?_, fun i j => ?_⟩,
    fun ⟨h1, h2⟩ => ⟨⟨fun i j => h1 _ _, fun i j => h2 _ _⟩, fun i => isEmptyElim i⟩⟩
  · simpa using h1 (o.symm i) (o.symm j)
  · have := h2 (o.symm i) (o.symm j)
    rwa [submatrix_apply, o.apply_symm_apply, o.apply_symm_apply] at this

theorem level_lam (o : r ⊕ e ≃ n ⊕ Fin c)
    (x : ((parahoric r e δ hδ).toLevel.map (plainFrame o).conj).J) :
    ((parahoric r e δ hδ).toLevel.map (plainFrame o).conj).lam x = 1 := by
  rw [Level.map_lam, parahoric_lam _ 1 (by ext i; exact isEmptyElim i), map_one, map_one]

end Empty

theorem firstVertex_twist : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle), HasConductor ψ 1 → ∀ (s : ℕ) (t : Type) [Fintype t] [DecidableEq t] (κ : Type) [Fintype κ] [DecidableEq κ] (δ : kˣ →* ℂˣ) (hδ : IsTame δ) (η : ℕ → kˣ →* ℂˣ) (c : ℕ) (H : 0 + c = s + 1), (prX (Cgrp ((twistChain s t κ δ hδ η).lev 0 c H).J 1) : Set (GL (XIx κ t 0) k)) = KO k (XIx κ t 0) ∧ (∀ γ ∈ KO k (XIx κ t 0), ∃ hm : embX c γ ∈ ((twistChain s t κ δ hδ η).lev 0 c H).J, (((twistChain s t κ δ hδ η).lev 0 c H).lam ⟨_, hm⟩ : ℂ) = 1) ∧ ∀ u ∈ N k (XIx κ t 0) c 1, ∀ hm : u ∈ ((twistChain s t κ δ hδ η).lev 0 c H).J, (((twistChain s t κ δ hδ η).lev 0 c H).lam ⟨u, hm⟩ : ℂ) = ψ (simpleSum u) := by
  intro k _ _ _ _ ψ hψ s t _ _ κ _ _ δ hδ η c H
  have hJ : ∀ x, x ∈ ((twistChain s t κ δ hδ η).lev 0 c H).J ↔ x ∈ KO k (XIx κ t 0 ⊕ Fin c) :=
    fun x => mem_level_iff (hδ := hδ) (stdOrd κ t 0 c H) x
  have hl : ∀ x, ((twistChain s t κ δ hδ η).lev 0 c H).lam x = 1 :=
    fun x => level_lam (hδ := hδ) (stdOrd κ t 0 c H) x
  refine ⟨?_, fun γ hγ => ⟨(hJ _).2 (embX_mem_KO hγ), by rw [hl]; rfl⟩, fun u _ hm => ?_⟩
  · ext g
    simp only [SetLike.mem_coe, mem_prX, mem_Cgrp, hJ, inv_one, one_mul, mul_one]
    refine ⟨fun ⟨u, hu, _, h⟩ => mem_KO_of_mul_embX hu h, fun hg => ⟨1, one_mem _, ?_, ?_⟩⟩
    · rw [one_mul]; exact (le_sup_left : (embX c).range ≤ R k _ c 1) ⟨g, rfl⟩
    · rw [one_mul]; exact embX_mem_KO hg
  · rw [hl, hψ.eq_one (show _ ∈ cball (1 : kˣ) from simpleSum_mem ((hJ u).1 hm))]; rfl

end GlobalTheory.TwistVertex
