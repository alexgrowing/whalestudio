import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.IsClosedEmbeddingOfLocallyCompact
import GroundTheory.AutomorphicForms.DixmierMalliavin
import GroundTheory.AutomorphicForms.HarishChandraRegularity.ExpHaar
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsSmoothLogMemLieAlg
set_option maxSynthPendingDepth 1
open scoped Manifold ContDiff Topology
open MeasureTheory Set GroundTheory.Automorphic
open scoped Matrix.Norms.L2Operator

noncomputable section

namespace GlobalTheory.CompanionTheory.ClosedSubgroupUnits

open Matrix

variable {n : Type} [Fintype n] [DecidableEq n] {m : ℕ}

def blk (e : n ⊕ n ≃ Fin m) : Matrix n n ℂ × Matrix n n ℂ →+* Matrix (Fin m) (Fin m) ℂ where
  toFun p := Matrix.reindex e e (Matrix.fromBlocks p.1 0 0 p.2)
  map_one' := by simp
  map_mul' p q := by
    simp [Matrix.fromBlocks_multiply, Matrix.submatrix_mul_equiv]
  map_zero' := by simp
  map_add' p q := by
    have h : Matrix.fromBlocks (p + q).1 0 0 (p + q).2 =
        Matrix.fromBlocks p.1 0 0 p.2 + Matrix.fromBlocks q.1 0 0 q.2 := by
      simp [Matrix.fromBlocks_add]
    rw [h]
    rfl

theorem blk_apply (e : n ⊕ n ≃ Fin m) (a b : Matrix n n ℂ) :
    blk e (a, b) = Matrix.reindex e e (Matrix.fromBlocks a 0 0 b) := rfl

def unblk (e : n ⊕ n ≃ Fin m) (g : Matrix (Fin m) (Fin m) ℂ) : Matrix n n ℂ × Matrix n n ℂ :=
  ((Matrix.reindex e.symm e.symm g).toBlocks₁₁, (Matrix.reindex e.symm e.symm g).toBlocks₂₂)

theorem unblk_blk (e : n ⊕ n ≃ Fin m) (p : Matrix n n ℂ × Matrix n n ℂ) :
    unblk e (blk e p) = p := by
  ext i j <;> simp [unblk, blk, Matrix.toBlocks₁₁, Matrix.toBlocks₂₂]

theorem continuous_blk (e : n ⊕ n ≃ Fin m) : Continuous (blk e) := by
  refine continuous_matrix fun i j => ?_
  change Continuous fun p : Matrix n n ℂ × Matrix n n ℂ =>
    Matrix.fromBlocks p.1 0 0 p.2 (e.symm i) (e.symm j)
  rcases e.symm i with a | a <;> rcases e.symm j with b | b <;> simp only [Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂]
  · exact (continuous_apply_apply a b).comp continuous_fst
  · exact continuous_const
  · exact continuous_const
  · exact (continuous_apply_apply a b).comp continuous_snd

theorem continuous_unblk (e : n ⊕ n ≃ Fin m) : Continuous (unblk e) := by
  refine Continuous.prodMk (continuous_matrix fun i j => ?_) (continuous_matrix fun i j => ?_)
  · exact continuous_apply_apply _ _
  · exact continuous_apply_apply _ _

theorem isClosedEmbedding_blk (e : n ⊕ n ≃ Fin m) : Topology.IsClosedEmbedding (blk e) :=
  Function.LeftInverse.isClosedEmbedding (f := unblk e) (unblk_blk e) (continuous_unblk e)
    (continuous_blk e)

theorem exp_blk (e : n ⊕ n ≃ Fin m) (a b : Matrix n n ℂ) :
    NormedSpace.exp (blk e (a, b)) = blk e (NormedSpace.exp a, NormedSpace.exp b) := by
  letI : NormedAlgebra ℚ (Matrix n n ℂ) := NormedAlgebra.restrictScalars ℚ ℝ (Matrix n n ℂ)
  rw [← NormedSpace.map_exp (blk e) (continuous_blk e) (a, b)]
  congr 1
  exact Prod.ext (Prod.fst_exp _) (Prod.snd_exp _)

def jHom (e : n ⊕ n ≃ Fin m) : (Matrix n n ℂ)ˣ →* Matrix (Fin m) (Fin m) ℂ where
  toFun u := blk e ((u : Matrix n n ℂ), (((u⁻¹ : (Matrix n n ℂ)ˣ) : Matrix n n ℂ))ᵀ)
  map_one' := by
    have h : blk e ((1 : Matrix n n ℂ), (1 : Matrix n n ℂ)) = 1 := map_one (blk e)
    simpa using h
  map_mul' u v := by
    rw [← map_mul]
    simp [Matrix.transpose_mul]

theorem jHom_apply (e : n ⊕ n ≃ Fin m) (u : (Matrix n n ℂ)ˣ) :
    jHom e u = blk e ((u : Matrix n n ℂ), (((u⁻¹ : (Matrix n n ℂ)ˣ) : Matrix n n ℂ))ᵀ) := rfl

theorem isClosedEmbedding_jHom (e : n ⊕ n ≃ Fin m) : Topology.IsClosedEmbedding (jHom e) := by
  have h1 : Topology.IsClosedEmbedding
      (fun p : Matrix n n ℂ × (Matrix n n ℂ)ᵐᵒᵖ => (p.1, (MulOpposite.unop p.2)ᵀ)) :=
    Function.LeftInverse.isClosedEmbedding
      (f := fun p : Matrix n n ℂ × Matrix n n ℂ => (p.1, MulOpposite.op p.2ᵀ))
      (fun p => by simp)
      (continuous_fst.prodMk (MulOpposite.continuous_op.comp continuous_snd.matrix_transpose))
      (continuous_fst.prodMk
        ((MulOpposite.continuous_unop.comp continuous_snd).matrix_transpose))
  exact (isClosedEmbedding_blk e).comp (h1.comp Units.isClosedEmbedding_embedProduct)

def dLin (e : n ⊕ n ≃ Fin m) : Matrix n n ℂ →ₗ[ℝ] Matrix (Fin m) (Fin m) ℂ where
  toFun X := blk e (X, -Xᵀ)
  map_add' X Y := by
    rw [← map_add]
    simp [Matrix.transpose_add, add_comm]
  map_smul' r X := by
    ext i j
    simp only [blk_apply, Matrix.reindex_apply, Matrix.submatrix_apply, RingHom.id_apply,
      Matrix.smul_apply]
    rcases e.symm i with a | a <;> rcases e.symm j with b | b <;> simp

theorem dLin_apply (e : n ⊕ n ≃ Fin m) (X : Matrix n n ℂ) : dLin e X = blk e (X, -Xᵀ) := rfl

theorem continuous_dLin (e : n ⊕ n ≃ Fin m) : Continuous (dLin e) :=
  (continuous_blk e).comp (continuous_id.prodMk continuous_id.matrix_transpose.neg)

theorem exp_dLin (e : n ⊕ n ≃ Fin m) (X : Matrix n n ℂ) :
    NormedSpace.exp (dLin e X) = jHom e (expUnit ℝ (Matrix n n ℂ) X) := by
  rw [dLin_apply, exp_blk, jHom_apply, coe_expUnit, coe_expUnit_inv, ← Matrix.transpose_neg,
    Matrix.exp_transpose]

theorem isClosedMatrixGroup_image (e : n ⊕ n ≃ Fin m) (H : Subgroup (Matrix n n ℂ)ˣ)
    (hH : IsClosed (H : Set (Matrix n n ℂ)ˣ)) :
    SmoothVectors.IsClosedMatrixGroup (jHom e '' (H : Set (Matrix n n ℂ)ˣ)) := by
  refine ⟨(isClosedEmbedding_jHom e).isClosedMap _ hH, ⟨1, H.one_mem, map_one _⟩, ?_, ?_⟩
  · rintro _ ⟨u, hu, rfl⟩ _ ⟨v, hv, rfl⟩
    exact ⟨u * v, H.mul_mem hu hv, map_mul _ _ _⟩
  · rintro _ ⟨u, hu, rfl⟩
    refine ⟨jHom e u⁻¹, ⟨u⁻¹, H.inv_mem hu, rfl⟩, ?_, ?_⟩
    · rw [← map_mul, inv_mul_cancel, map_one]
    · rw [← map_mul, mul_inv_cancel, map_one]

theorem exists_isExpLieAlgebra {n : Type} [Fintype n] [DecidableEq n]
    (H : Subgroup (Matrix n n ℂ)ˣ) (hH : IsClosed (H : Set (Matrix n n ℂ)ˣ)) :
    ∃ 𝔤 : Submodule ℝ (Matrix n n ℂ), IsExpLieAlgebra H 𝔤 := by
  let e : n ⊕ n ≃ Fin (Fintype.card (n ⊕ n)) := Fintype.equivFin _
  have hJ := isClosedMatrixGroup_image e H hH
  obtain ⟨S, hS⟩ := GlobalTheory.CompanionTheory.MatrixLie.exists_submodule_eq_lieAlg _ _ hJ
  have hsm : ∀ (t : ℝ) (Z : Matrix (Fin (Fintype.card (n ⊕ n))) (Fin (Fintype.card (n ⊕ n))) ℂ),
      (t : ℂ) • Z = t • Z := by
    intro t Z
    ext a b
    simp
  have hS' : ∀ X, X ∈ S ↔ ∀ t : ℝ, NormedSpace.exp (t • X) ∈ jHom e '' (H : Set (Matrix n n ℂ)ˣ) := by
    intro X
    have h2 : X ∈ S ↔ X ∈ SmoothVectors.lieAlg (jHom e '' (H : Set (Matrix n n ℂ)ˣ)) := by
      rw [← hS]
      exact Iff.rfl
    rw [h2]
    refine forall_congr' fun t => ?_
    rw [hsm]
  have hinj := (isClosedEmbedding_jHom e).injective
  have hmem : ∀ X, NormedSpace.exp (dLin e X) ∈ jHom e '' (H : Set (Matrix n n ℂ)ˣ) →
      expUnit ℝ (Matrix n n ℂ) X ∈ H := by
    intro X hX
    rw [exp_dLin] at hX
    obtain ⟨u, hu, hue⟩ := hX
    rwa [← hinj hue]
  refine ⟨S.comap (dLin e), fun X hX => hmem X ?_, ?_⟩
  · simpa using (hS' _).1 hX 1
  · set 𝔢 := expPartialHomeomorph ℝ (Matrix n n ℂ) with h𝔢
    set 𝔣 := expPartialHomeomorph ℝ
      (Matrix (Fin (Fintype.card (n ⊕ n))) (Fin (Fintype.card (n ⊕ n))) ℂ) with h𝔣
    have hev := GlobalTheory.CompanionTheory.ClosedSubgroup.eventually_exp_of_mem hJ.1 hJ.2.1 hJ.2.2.1 hJ.2.2.2 hS'
      (𝔣.open_source.mem_nhds (zero_mem_expPartialHomeomorph_source ℝ _))
    obtain ⟨V, hV, hVo, h1V⟩ := eventually_nhds_iff.1 hev
    have hcD := continuous_dLin e
    have hcE : Continuous fun X => NormedSpace.exp (dLin e X) :=
      (contDiff_exp ℝ _ (n := 0)).continuous.comp hcD
    refine ⟨𝔢.source ∩ (dLin e ⁻¹' 𝔣.source ∩ (fun X => NormedSpace.exp (dLin e X)) ⁻¹' V),
      𝔢.open_source.inter ((𝔣.open_source.preimage hcD).inter (hVo.preimage hcE)),
      ⟨zero_mem_expPartialHomeomorph_source ℝ _, ?_, ?_⟩, Set.inter_subset_left, ?_⟩
    · simpa using zero_mem_expPartialHomeomorph_source ℝ
        (Matrix (Fin (Fintype.card (n ⊕ n))) (Fin (Fintype.card (n ⊕ n))) ℂ)
    · simpa using h1V
    · rintro X ⟨-, hXs, hXV⟩ hXH
      obtain ⟨Y, hYS, hYs, hYe⟩ := hV _ hXV ⟨_, hXH, (exp_dLin e X).symm⟩
      have hDY : dLin e X = Y := 𝔣.injOn hXs hYs hYe.symm
      change dLin e X ∈ S
      rwa [hDY]

end GlobalTheory.CompanionTheory.ClosedSubgroupUnits
