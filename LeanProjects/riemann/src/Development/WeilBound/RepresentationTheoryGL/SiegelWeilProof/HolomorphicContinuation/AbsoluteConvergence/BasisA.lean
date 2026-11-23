import Mathlib
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.FlatEq

noncomputable section

open MeasureTheory Matrix Set Filter Topology
open scoped NNReal

namespace PositivityTheory.Rg.Sw.AbsSt.BasisPf

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.AbsSt

variable {n : ℕ}

theorem mR_one : mR (1 : GR n) = 1 := rfl

theorem continuous_mR : Continuous (fun g : GR n => mR g) := by
  unfold mR; fun_prop

theorem det_mR_ne (g : GR n) : (mR g).det ≠ 0 :=
  IsUnit.ne_zero ((Matrix.isUnit_iff_isUnit_det _).1 g.1.isUnit)

theorem continuous_group_lower_left_block : Continuous (fun M : M2 n => M.toBlocks₂₁) := by
  have : (fun M : M2 n => M.toBlocks₂₁) = fun M => M.submatrix Sum.inr Sum.inl := by funext M; rfl
  rw [this]; exact continuous_id.matrix_submatrix _ _

theorem continuous_group_lower_right_block : Continuous (fun M : M2 n => M.toBlocks₂₂) := by
  have : (fun M : M2 n => M.toBlocks₂₂) = fun M => M.submatrix Sum.inr Sum.inr := by funext M; rfl
  rw [this]; exact continuous_id.matrix_submatrix _ _

theorem continuous_first_cayley_block_map : Continuous (fun M : M2 n => u1 M) := by
  unfold u1
  exact ((continuous_const : Continuous fun _ : M2 n => Complex.I).smul continuous_group_lower_left_block).add continuous_group_lower_right_block

theorem continuous_second_cayley_block_map : Continuous (fun M : M2 n => u2 M) := by
  unfold u2
  exact ((continuous_const : Continuous fun _ : M2 n => Complex.I).smul continuous_group_lower_left_block).neg.add continuous_group_lower_right_block

theorem continuous_weight_factor (hD : CayleyBlocksInvertible) (p q : ℕ) (e : ℤ) : Continuous (F0 (n := n) p q e) := by
  unfold F0 f0
  refine Continuous.mul ((continuous_mR.matrix_det).zpow₀ e fun g => Or.inl (det_mR_ne g)) (Continuous.mul ?_ ?_)
  · exact ((continuous_first_cayley_block_map.comp continuous_mR).matrix_det).zpow₀ _ fun g => Or.inl (hD n g).1
  · exact ((continuous_second_cayley_block_map.comp continuous_mR).matrix_det).zpow₀ _ fun g => Or.inl (hD n g).2

theorem hLoc_pos (hD : CayleyBlocksInvertible) (g : GR n) : 0 < hLoc g := by
  unfold hLoc
  have : (u1 (mR g)).det ≠ 0 := (hD n g).1
  positivity

theorem continuous_hLoc (hD : CayleyBlocksInvertible) : Continuous (hLoc (n := n)) := by
  unfold hLoc
  refine Continuous.inv₀ ?_ fun g => ?_
  · exact (((continuous_first_cayley_block_map.comp continuous_mR).matrix_det).norm).pow 2
  · have : (u1 (mR g)).det ≠ 0 := (hD n g).1
    positivity

theorem hLoc_one : hLoc (1 : GR n) = 1 := by
  have h1 : u1 (1 : M2 n) = 1 := by
    ext i j
    simp [u1, Matrix.toBlocks₂₁, Matrix.toBlocks₂₂, Matrix.one_apply]
  simp [hLoc, mR_one, h1]

theorem hLoc_K (hM : Mult) (k : GR n) (hk : k ∈ KR n) : hLoc k = 1 := by
  have := ((hM n 0 0 0).1 1 k hk).2
  rw [one_mul, hLoc_one] at this
  exact this

def uSet (n : ℕ) : Set (M2 n) := {u | uᴴ * u = 1 ∧ InG u}

theorem isCompact_uSet (n : ℕ) : IsCompact (uSet n) := by
  have hbox : IsCompact (Set.pi univ fun _ : Fin n ⊕ Fin n => Set.pi univ fun _ : Fin n ⊕ Fin n =>
      Metric.closedBall (0 : ℂ) 1) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall _ _
  refine hbox.of_isClosed_subset ?_ ?_
  · refine IsClosed.inter ?_ ?_
    · exact isClosed_eq (continuous_id.matrix_conjTranspose.matrix_mul continuous_id) continuous_const
    · exact isClosed_eq ((continuous_id.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul continuous_id)
        continuous_const
  · intro u hu
    have hU : u ∈ Matrix.unitaryGroup (Fin n ⊕ Fin n) ℂ := Matrix.mem_unitaryGroup_iff'.2 hu.1
    simp only [Set.mem_pi, Set.mem_univ, true_implies, Metric.mem_closedBall, dist_zero_right]
    intro i j
    exact entry_norm_bound_of_unitary hU i j

def toK (u : uSet n) : KR n :=
  ⟨⟨⟨u.1, u.1ᴴ, mul_eq_one_comm.1 u.2.1, u.2.1⟩, u.2.2⟩, ⟨u.2.2, u.2.1⟩⟩

theorem continuous_toK : Continuous (toK (n := n)) := by
  refine Continuous.subtype_mk (Continuous.subtype_mk ?_ _) _
  rw [Units.continuous_iff]
  exact ⟨continuous_subtype_val, continuous_subtype_val.matrix_conjTranspose⟩

instance compactKR (n : ℕ) : CompactSpace (KR n) := by
  have : CompactSpace (uSet n) := isCompact_iff_compactSpace.1 (isCompact_uSet n)
  refine ⟨?_⟩
  have : (univ : Set (KR n)) = toK '' univ := by
    ext k
    simp only [mem_univ, mem_image, true_and, true_iff]
    refine ⟨⟨mR (k : GR n), ⟨k.2.2, k.2.1⟩⟩, ?_⟩
    apply Subtype.ext; apply Subtype.ext; apply Units.ext; rfl
  rw [this]
  exact isCompact_univ.image continuous_toK

theorem exists_pts {X : Type*} : ∀ (N : ℕ) (f : Fin N → X → ℂ), LinearIndependent ℂ f →
    ∃ x : Fin N → X, (Matrix.of fun j l => f j (x l)).det ≠ 0 := by
  intro N
  induction N with
  | zero => intro f _; exact ⟨Fin.elim0, by simp⟩
  | succ N ih =>
    intro f hf
    obtain ⟨x', hx'⟩ := ih (fun j => f (Fin.castSucc j)) (hf.comp _ (Fin.castSucc_injective N))
    let c : Fin (N + 1) → ℂ := fun i => (-1) ^ ((i : ℕ) + N) * (Matrix.of fun a b => f (i.succAbove a) (x' b)).det
    have hdet : ∀ y : X, (Matrix.of fun j l => f j (Fin.lastCases (motive := fun _ => X) y x' l)).det =
        ∑ i, c i * f i y := by
      intro y
      rw [Matrix.det_succ_column _ (Fin.last N)]
      refine Finset.sum_congr rfl fun i _ => ?_
      have hs : (Matrix.of fun j l => f j (Fin.lastCases (motive := fun _ => X) y x' l)).submatrix i.succAbove
          (Fin.last N).succAbove = Matrix.of fun a b => f (i.succAbove a) (x' b) := by
        ext a b
        simp [Fin.succAbove_last]
      rw [hs]
      simp only [c, Matrix.of_apply, Fin.lastCases_last, Fin.val_last]
      ring
    by_contra hcon
    push Not at hcon
    have key : ∑ i, c i • f i = 0 := by
      funext y
      have h := hcon (Fin.lastCases (motive := fun _ => X) y x')
      rw [hdet y] at h
      simpa [Finset.sum_apply] using h
    have h0 := Fintype.linearIndependent_iff.1 hf c key (Fin.last N)
    have hc : c (Fin.last N) ≠ 0 := by
      simp only [c, Fin.val_last, Fin.succAbove_last]
      refine mul_ne_zero (pow_ne_zero _ (by norm_num)) ?_
      simpa using hx'
    exact hc h0

end PositivityTheory.Rg.Sw.AbsSt.BasisPf
