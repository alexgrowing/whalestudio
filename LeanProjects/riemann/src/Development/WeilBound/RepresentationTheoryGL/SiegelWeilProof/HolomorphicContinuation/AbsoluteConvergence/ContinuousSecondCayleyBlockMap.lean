import Mathlib
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.FarRightAlt

noncomputable section

open MeasureTheory Matrix Set Filter Topology
open scoped NNReal

namespace PositivityTheory.Rg.Sw.AbsSt.Far

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.AbsSt

variable {n : ℕ}

theorem continuous_mR : Continuous (mR : GR n → M2 n) :=
  Units.continuous_val.comp continuous_subtype_val

def KMat (n : ℕ) : Set (M2 n) := {M | Mᴴ * M = 1 ∧ Mᴴ * JJ n * M = JJ n}

theorem isCompact_KMat : IsCompact (KMat n) := by
  have hsub : KMat n ⊆ Set.pi univ (fun _ : Fin n ⊕ Fin n => Set.pi univ (fun _ : Fin n ⊕ Fin n => Metric.closedBall (0:ℂ) 1)) := by
    intro M hM
    have hU : M ∈ Matrix.unitaryGroup (Fin n ⊕ Fin n) ℂ := Matrix.mem_unitaryGroup_iff'.mpr hM.1
    intro i _ j _
    simpa using entry_norm_bound_of_unitary hU i j
  have hc : IsCompact (Set.pi univ (fun _ : Fin n ⊕ Fin n => Set.pi univ (fun _ : Fin n ⊕ Fin n => Metric.closedBall (0:ℂ) 1))) :=
    isCompact_univ_pi (fun _ => isCompact_univ_pi (fun _ => isCompact_closedBall 0 1))
  refine hc.of_isClosed_subset ?_ hsub
  have hA : Continuous fun M : M2 n => Mᴴ * M :=
    continuous_id.matrix_conjTranspose.matrix_mul continuous_id
  have hB : Continuous fun M : M2 n => Mᴴ * JJ n * M :=
    (continuous_id.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul continuous_id
  exact (isClosed_eq hA continuous_const).inter (isClosed_eq hB continuous_const)

theorem isCompact_KR : IsCompact ((KR n : Subgroup (GR n)) : Set (GR n)) := by
  let φ : KMat n → GR n := fun M =>
    ⟨⟨M.1, M.1ᴴ, (mul_eq_one_comm).mp M.2.1, M.2.1⟩, M.2.2⟩
  have hφ : Continuous φ :=
    Continuous.subtype_mk (Units.continuous_iff.mpr
      ⟨continuous_subtype_val, continuous_subtype_val.matrix_conjTranspose⟩) _
  have hK : IsCompact (univ : Set (KMat n)) := isCompact_iff_isCompact_univ.mp isCompact_KMat
  have himg : φ '' univ = ((KR n : Subgroup (GR n)) : Set (GR n)) := by
    ext k
    constructor
    · rintro ⟨M, -, rfl⟩
      exact ⟨M.2.2, M.2.1⟩
    · intro hk
      refine ⟨⟨mR k, hk.2, hk.1⟩, trivial, ?_⟩
      apply Subtype.ext
      apply Units.ext
      rfl
  rw [← himg]
  exact hK.image hφ

instance compactSpace_KR_far : CompactSpace (KR n) := isCompact_iff_compactSpace.mp isCompact_KR

theorem continuous_first_cayley_block_map : Continuous (fun M : M2 n => u1 M) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  simp only [u1, Matrix.add_apply, Matrix.smul_apply, Matrix.toBlocks₂₁, Matrix.toBlocks₂₂, Matrix.of_apply]
  fun_prop

theorem continuous_second_cayley_block_map : Continuous (fun M : M2 n => u2 M) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  simp only [u2, Matrix.add_apply, Matrix.neg_apply, Matrix.smul_apply, Matrix.toBlocks₂₁, Matrix.toBlocks₂₂, Matrix.of_apply]
  fun_prop

theorem det_mR_ne (g : GR n) : (mR g).det ≠ 0 := by
  exact ((Matrix.isUnit_iff_isUnit_det _).mp g.1.isUnit).ne_zero

theorem continuous_weight_factor (hD : CayleyBlocksInvertible) (p q : ℕ) (e : ℤ) : Continuous (F0 (n := n) p q e) := by
  have hm : Continuous (mR : GR n → M2 n) := continuous_mR
  have hd : Continuous fun g : GR n => (mR g).det := hm.matrix_det
  have h1 : Continuous fun g : GR n => (u1 (mR g)).det := (continuous_first_cayley_block_map.comp hm).matrix_det
  have h2 : Continuous fun g : GR n => (u2 (mR g)).det := (continuous_second_cayley_block_map.comp hm).matrix_det
  unfold F0 f0
  exact (hd.zpow₀ e fun g => Or.inl (det_mR_ne g)).mul
    ((h1.zpow₀ _ fun g => Or.inl (hD n g).1).mul (h2.zpow₀ _ fun g => Or.inl (hD n g).2))

theorem weight_factor_ne_zero (hD : CayleyBlocksInvertible) (p q : ℕ) (e : ℤ) (g : GR n) : F0 p q e g ≠ 0 := by
  unfold F0 f0
  refine mul_ne_zero (zpow_ne_zero _ (det_mR_ne g)) (mul_ne_zero (zpow_ne_zero _ (hD n g).1) (zpow_ne_zero _ (hD n g).2))

theorem hLoc_pos (hD : CayleyBlocksInvertible) (g : GR n) : 0 < hLoc g := by
  unfold hLoc
  exact inv_pos.mpr (pow_pos (norm_pos_iff.mpr (hD n g).1) 2)

theorem continuous_hLoc (hD : CayleyBlocksInvertible) : Continuous (hLoc (n := n)) := by
  have h1 : Continuous fun g : GR n => (u1 (mR g)).det := (continuous_first_cayley_block_map.comp continuous_mR).matrix_det
  unfold hLoc
  exact (h1.norm.pow 2).inv₀ fun g => pow_ne_zero 2 (norm_ne_zero_iff.mpr (hD n g).1)

end PositivityTheory.Rg.Sw.AbsSt.Far
