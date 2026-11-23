import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BorelParam
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SupportParahoricBiTransformingLeviDoubleCoset

noncomputable section

open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection
  GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound

namespace GlobalTheory.ChainStepSupp

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

open MeasureTheory ValuativeRel Matrix in
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in

theorem _root_.GlobalTheory.ChainStepSupp.det_lower_ne_zero {A D : Type} [Fintype A] [DecidableEq A]
    [Fintype D] [DecidableEq D]
    {j : GL (A ⊕ D) k} (hj : j ∈ _root_.GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection.parahoric k A D) : j.1.toBlocks₂₂.det ≠ 0 :=
  (_root_.GlobalTheory.ParahoricLowerBlock.lower_block_tame k A D 1 (fun _ _ => rfl) j hj).1

variable (k) in

def reGL {m n : Type} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n] (e : m ≃ n) : GL m k ≃* GL n k :=
  Units.mapEquiv (Matrix.reindexAlgEquiv k k e).toMulEquiv

theorem val_reGL {m n : Type} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n] (e : m ≃ n) (g : GL m k) :
    (reGL k e g).1 = reindex e e g.1 := rfl

open MeasureTheory ValuativeRel Matrix in
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem _root_.GlobalTheory.ChainStepSupp.reGL_mem_KO {m n : Type} [Fintype m] [DecidableEq m]
    [Fintype n] [DecidableEq n] (e : m ≃ n)
    {g : GL m k} (hg : g ∈ _root_.GlobalTheory.SplitWeil.KO k m) :
    _root_.GlobalTheory.ChainStepSupp.reGL k e g ∈ _root_.GlobalTheory.SplitWeil.KO k n := by
  rw [_root_.GlobalTheory.SplitFlip.mem_KO_iff] at hg ⊢
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · simpa [_root_.GlobalTheory.ChainStepSupp.val_reGL, Matrix.reindex_apply] using hg.1 (e.symm i) (e.symm j)
  · rw [← map_inv]
    simpa [_root_.GlobalTheory.ChainStepSupp.val_reGL, Matrix.reindex_apply] using hg.2 (e.symm i) (e.symm j)

open MeasureTheory ValuativeRel Matrix in
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem _root_.GlobalTheory.ChainStepSupp.reGL_torusElt {m n : Type} [Fintype m]
    [DecidableEq m] [Fintype n] [DecidableEq n] (e : m ≃ n)
    (ϖ : kˣ) (f : m → ℤ) :
    _root_.GlobalTheory.ChainStepSupp.reGL k e (_root_.GlobalTheory.GLDoubling.torusElt k m ϖ f) =
      _root_.GlobalTheory.GLDoubling.torusElt k n ϖ (f ∘ e.symm) := by
  ext i j
  simp [_root_.GlobalTheory.ChainStepSupp.val_reGL, _root_.GlobalTheory.GLDoubling.val_torusElt, Matrix.reindex_apply,
    Matrix.diagonal_apply]

open MeasureTheory ValuativeRel Matrix in
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem _root_.GlobalTheory.ChainStepSupp.reGL_reGL_symm {m n : Type} [Fintype m] [DecidableEq m] [Fintype n]
    [DecidableEq n] (e : m ≃ n)
    (g : GL n k) : _root_.GlobalTheory.ChainStepSupp.reGL k e (_root_.GlobalTheory.ChainStepSupp.reGL k e.symm g) = g := by
  ext i j
  simp [_root_.GlobalTheory.ChainStepSupp.val_reGL, Matrix.reindex_apply]

open MeasureTheory ValuativeRel Matrix in
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in

theorem _root_.GlobalTheory.ChainStepSupp.emb₂_mem_parahoric {A D : Type} [Fintype A] [DecidableEq A]
    [Fintype D] [DecidableEq D]
    {x : GL A k} {y : GL D k} (hx : x ∈ _root_.GlobalTheory.SplitWeil.KO k A)
    (hy : y ∈ _root_.GlobalTheory.SplitWeil.KO k D) :
    _root_.GlobalTheory.SmGL.emb₂ k (Equiv.refl (A ⊕ D)) (x, y) ∈ _root_.GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection.parahoric k A D := by
  rw [_root_.GlobalTheory.SplitFlip.mem_KO_iff] at hx hy
  rw [_root_.GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection.mem_parahoric, _root_.GlobalTheory.SplitFlip.mem_KO_iff]
  refine ⟨⟨fun i j => ?_, fun i j => ?_⟩, fun i j => ?_⟩
  · rcases i with i | i <;> rcases j with j | j <;>
      simp [_root_.GlobalTheory.SmGL.val_emb₂, hx.1, hy.1]
  · have hx₂ := hx.2
    have hy₂ := hy.2
    simp only [Matrix.coe_units_inv] at hx₂ hy₂
    rw [← map_inv, Prod.inv_mk]
    rcases i with i | i <;> rcases j with j | j <;>
      simp [_root_.GlobalTheory.SmGL.val_emb₂, hx₂, hy₂]
  · simp [_root_.GlobalTheory.SmGL.val_emb₂]

open MeasureTheory ValuativeRel Matrix in
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in

theorem _root_.GlobalTheory.ChainStepSupp.emb₂_one_torusElt {A D : Type} [Fintype A] [DecidableEq A]
    [Fintype D] [DecidableEq D] (ϖ : kˣ)
    (f : D → ℤ) :
    _root_.GlobalTheory.SmGL.emb₂ k (Equiv.refl (A ⊕ D)) (1, _root_.GlobalTheory.GLDoubling.torusElt k D ϖ f) =
      (_root_.GlobalTheory.ZonalCellDecomposition.mtor ϖ f : GL (A ⊕ D) k) := by
  have h : (_root_.GlobalTheory.ZonalCellDecomposition.mtor ϖ f : GL (A ⊕ D) k) =
      _root_.GlobalTheory.GLDoubling.torusElt k (A ⊕ D) ϖ (0 ⊕ᵥ f) := rfl
  rw [h]
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [_root_.GlobalTheory.SmGL.val_emb₂, _root_.GlobalTheory.GLDoubling.val_torusElt, Matrix.diagonal_apply,
      Matrix.one_apply]

open MeasureTheory ValuativeRel Matrix in
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in

theorem _root_.GlobalTheory.ChainStepSupp.support_dcell : ∀ (k : Type) [Field k] [ValuativeRel k]
    [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ϖ : kˣ),
    valuation k (ϖ : k) = uniformizer k →
  ∀ (r l t : ℕ) (ξ : kˣ →* ℂˣ), _root_.GlobalTheory.SplitWeil.IsTame ξ → ¬ _root_.GlobalTheory.SplitWeil.IsUnram ξ →
  ∀ φ : GL (Fin r ⊕ _root_.GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection.Blocks l t) k → ℂ, _root_.GlobalTheory.ZonalCellDecomposition.IsBiType ξ φ →
    (∀ x y, φ (_root_.GlobalTheory.SmGL.emb₂ k (Equiv.refl (Fin r ⊕ _root_.GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection.Blocks l t)) (x, y)) ≠ 0 →
      x ∈ _root_.GlobalTheory.SplitWeil.KO k (Fin r)) →
    ∀ g, φ g ≠ 0 → ∃ e : Fin (l * t) → ℤ, Antitone e ∧
      g ∈ _root_.GlobalTheory.ZonalCellDecomposition.dcell ϖ (e ∘ (_root_.GlobalTheory.ZonalCellDecomposition.blkEquiv l t).symm) := by
  intro k _ _ _ _ ϖ hϖ r l t ξ hT hU φ hφ hL g hg
  obtain ⟨x, y, j, hj, j', hj', rfl⟩ :=
    _root_.GlobalTheory.ParHeckeSupp.support_levi k (Fin r) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection.Blocks l t) ξ hT hU φ hφ
      g hg
  have hne : φ (_root_.GlobalTheory.SmGL.emb₂ k (Equiv.refl _) (x, y)) ≠ 0 := by
    intro h0
    apply hg
    have hd := _root_.GlobalTheory.ChainStepSupp.det_lower_ne_zero hj
    have hd' := _root_.GlobalTheory.ChainStepSupp.det_lower_ne_zero hj'
    rw [mul_assoc, (hφ j hj (Units.mk0 _ hd) rfl _).1, (hφ j' hj' (Units.mk0 _ hd') rfl _).2, h0,
      mul_zero, mul_zero]
  have hx := hL x y hne
  set E := _root_.GlobalTheory.ZonalCellDecomposition.blkEquiv l t
  obtain ⟨⟨e, he⟩, hy⟩ := Set.mem_iUnion.1 ((Set.eq_univ_iff_forall.1
    (_root_.GlobalTheory.GLDoubling.iUnion_cell (N := l * t) hϖ)) (_root_.GlobalTheory.ChainStepSupp.reGL k E.symm y))
  unfold _root_.GlobalTheory.GLDoubling.cell at hy
  rw [DoubleCoset.mem_doubleCoset] at hy
  obtain ⟨κ₁, hκ₁, κ₂, hκ₂, hyeq⟩ := hy
  refine ⟨e, he, ?_⟩
  unfold _root_.GlobalTheory.ZonalCellDecomposition.dcell
  rw [DoubleCoset.mem_doubleCoset]
  have hy' : y = _root_.GlobalTheory.ChainStepSupp.reGL k E κ₁ *
      _root_.GlobalTheory.GLDoubling.torusElt k _ ϖ (e ∘ E.symm) * _root_.GlobalTheory.ChainStepSupp.reGL k E κ₂ := by
    rw [← _root_.GlobalTheory.ChainStepSupp.reGL_torusElt, ← map_mul, ← map_mul, ← hyeq]
    exact (_root_.GlobalTheory.ChainStepSupp.reGL_reGL_symm E y).symm
  refine ⟨j * _root_.GlobalTheory.SmGL.emb₂ k (Equiv.refl _) (x, _root_.GlobalTheory.ChainStepSupp.reGL k E κ₁),
    (_root_.GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection.parahoric k _ _).mul_mem hj
      (_root_.GlobalTheory.ChainStepSupp.emb₂_mem_parahoric hx
        (_root_.GlobalTheory.ChainStepSupp.reGL_mem_KO E hκ₁)),
    _root_.GlobalTheory.SmGL.emb₂ k (Equiv.refl _) (1, _root_.GlobalTheory.ChainStepSupp.reGL k E κ₂) * j',
    (_root_.GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection.parahoric k _ _).mul_mem
      (_root_.GlobalTheory.ChainStepSupp.emb₂_mem_parahoric (Subgroup.one_mem _)
        (_root_.GlobalTheory.ChainStepSupp.reGL_mem_KO E hκ₂)) hj', ?_⟩
  rw [← _root_.GlobalTheory.ChainStepSupp.emb₂_one_torusElt, hy']
  have hprod : ((x, _root_.GlobalTheory.ChainStepSupp.reGL k E κ₁ *
      _root_.GlobalTheory.GLDoubling.torusElt k _ ϖ (e ∘ E.symm) * _root_.GlobalTheory.ChainStepSupp.reGL k E κ₂) :
        GL (Fin r) k × GL (_root_.GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection.Blocks l t) k) =
      (x, _root_.GlobalTheory.ChainStepSupp.reGL k E κ₁) * (1, _root_.GlobalTheory.GLDoubling.torusElt k _ ϖ (e ∘ E.symm)) *
        (1, _root_.GlobalTheory.ChainStepSupp.reGL k E κ₂) := by
    simp [Prod.mk_mul_mk]
  rw [hprod, map_mul, map_mul]
  simp only [mul_assoc]

end GlobalTheory.ChainStepSupp
