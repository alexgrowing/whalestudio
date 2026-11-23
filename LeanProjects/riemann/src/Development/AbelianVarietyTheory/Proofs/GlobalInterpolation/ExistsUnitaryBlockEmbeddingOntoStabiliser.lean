import Mathlib
import Formalism.LocalRingCardinality.DataCD
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.PerpendicularEmbedding
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ContinuousMatrixEntryAbsSum
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UpqLocallyCompactGroup

noncomputable section

namespace GlobalTheory.BlockEmbedding

open MeasureTheory Matrix Filter Topology Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding
  GlobalTheory.CompactDualQuot GlobalTheory.UpqTopology
open scoped ENNReal NNReal

variable {P Q P' Q' : ℕ}

def blk (e : Option (Fin P' ⊕ Fin Q') ≃ (Fin P ⊕ Fin Q))
    (m : Matrix (Fin P' ⊕ Fin Q') (Fin P' ⊕ Fin Q') ℂ) : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ :=
  Matrix.of fun i l => (e.symm i).elim ((e.symm l).elim 1 fun _ => 0)
    fun a => (e.symm l).elim 0 fun b => m a b

theorem ext_e (e : Option (Fin P' ⊕ Fin Q') ≃ (Fin P ⊕ Fin Q))
    {u v : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ} (h : ∀ x y, u (e x) (e y) = v (e x) (e y)) :
    u = v := by
  ext i l
  simpa using h (e.symm i) (e.symm l)

theorem blk_mul (e : Option (Fin P' ⊕ Fin Q') ≃ (Fin P ⊕ Fin Q))
    (m n : Matrix (Fin P' ⊕ Fin Q') (Fin P' ⊕ Fin Q') ℂ) : blk e (m * n) = blk e m * blk e n := by
  refine ext_e e fun x y => ?_
  rw [Matrix.mul_apply, ← e.sum_comp, Fintype.sum_option]
  rcases x with _ | x <;> rcases y with _ | y <;> simp [blk, Matrix.mul_apply, -Fintype.sum_sum_type]

open MeasureTheory Matrix Filter Topology in
open scoped ENNReal NNReal in
variable {P Q P' Q' : ℕ} in
private lemma Jpq_eq_diagonal_sg (P Q : ℕ) :
    _root_.Formalism.UG.Jpq P Q = diagonal fun i => (_root_.GlobalTheory.CompactDualQuot.sg i : ℂ) := by
  unfold _root_.Formalism.UG.Jpq _root_.GlobalTheory.CompactDualQuot.sg
  ext i k
  rcases i with i | i <;> rcases k with k | k <;>
    simp [Matrix.fromBlocks, Matrix.diagonal, Matrix.one_apply] <;> split_ifs <;> simp

open MeasureTheory Matrix Filter Topology in
open scoped ENNReal NNReal in
variable {P Q P' Q' : ℕ} in
private lemma conjTranspose_mul_diagonal_mul_apply {ι : Type*} [Fintype ι] [DecidableEq ι]
    (u : Matrix ι ι ℂ) (d : ι → ℂ) (a b : ι) :
    (uᴴ * diagonal d * u) a b = ∑ k, star (u k a) * d k * u k b := by
  rw [Matrix.mul_apply]
  congr 1
  ext k
  rw [Matrix.mul_diagonal, conjTranspose_apply]

open MeasureTheory Matrix Filter Topology in
open scoped ENNReal NNReal in
variable {P Q P' Q' : ℕ} in
variable (e : Option (Fin P' ⊕ Fin Q') ≃ (Fin P ⊕ Fin Q))
  (m : Matrix (Fin P' ⊕ Fin Q') (Fin P' ⊕ Fin Q') ℂ) in
private lemma sum_eq_none_add_sum_some {M : Type*} [AddCommMonoid M] (f : Fin P ⊕ Fin Q → M) :
    ∑ i, f i = f (e none) + ∑ a, f (e (some a)) := by
  rw [← e.sum_comp, Fintype.sum_option]

open MeasureTheory Matrix Filter Topology in
open scoped ENNReal NNReal in
variable {P Q P' Q' : ℕ} in
variable (e : Option (Fin P' ⊕ Fin Q') ≃ (Fin P ⊕ Fin Q))
  (m : Matrix (Fin P' ⊕ Fin Q') (Fin P' ⊕ Fin Q') ℂ) in
private lemma blk_none_none : _root_.GlobalTheory.BlockEmbedding.blk e m (e none) (e none) = 1 := by
  simp [_root_.GlobalTheory.BlockEmbedding.blk]

open MeasureTheory Matrix Filter Topology in
open scoped ENNReal NNReal in
variable {P Q P' Q' : ℕ} in
variable (e : Option (Fin P' ⊕ Fin Q') ≃ (Fin P ⊕ Fin Q))
  (m : Matrix (Fin P' ⊕ Fin Q') (Fin P' ⊕ Fin Q') ℂ) in
private lemma blk_some_none (a : Fin P' ⊕ Fin Q') :
    _root_.GlobalTheory.BlockEmbedding.blk e m (e (some a)) (e none) = 0 := by
  simp [_root_.GlobalTheory.BlockEmbedding.blk]

open MeasureTheory Matrix Filter Topology in
open scoped ENNReal NNReal in
variable {P Q P' Q' : ℕ} in
variable (e : Option (Fin P' ⊕ Fin Q') ≃ (Fin P ⊕ Fin Q))
  (m : Matrix (Fin P' ⊕ Fin Q') (Fin P' ⊕ Fin Q') ℂ) in
private lemma blk_none_some (b : Fin P' ⊕ Fin Q') :
    _root_.GlobalTheory.BlockEmbedding.blk e m (e none) (e (some b)) = 0 := by
  simp [_root_.GlobalTheory.BlockEmbedding.blk]

open MeasureTheory Matrix Filter Topology in
open scoped ENNReal NNReal in
variable {P Q P' Q' : ℕ} in
variable (e : Option (Fin P' ⊕ Fin Q') ≃ (Fin P ⊕ Fin Q))
  (m : Matrix (Fin P' ⊕ Fin Q') (Fin P' ⊕ Fin Q') ℂ) in
private lemma blk_some_some (a b : Fin P' ⊕ Fin Q') :
    _root_.GlobalTheory.BlockEmbedding.blk e m (e (some a)) (e (some b)) = m a b := by
  simp [_root_.GlobalTheory.BlockEmbedding.blk]

open MeasureTheory Matrix Filter Topology in
open scoped ENNReal NNReal in
variable {P Q P' Q' : ℕ} in
private lemma blk_preserves_Jpq (e : Option (Fin P' ⊕ Fin Q') ≃ (Fin P ⊕ Fin Q))
    (hs : _root_.GlobalTheory.CompactDualQuot.SignCompat e) (m : Matrix (Fin P' ⊕ Fin Q') (Fin P' ⊕ Fin Q') ℂ)
    (hm : mᴴ * _root_.Formalism.UG.Jpq P' Q' * m = _root_.Formalism.UG.Jpq P' Q') :
    (_root_.GlobalTheory.BlockEmbedding.blk e m)ᴴ * _root_.Formalism.UG.Jpq P Q * _root_.GlobalTheory.BlockEmbedding.blk e m =
      _root_.Formalism.UG.Jpq P Q := by
  unfold _root_.GlobalTheory.CompactDualQuot.SignCompat at hs
  rw [Jpq_eq_diagonal_sg] at hm ⊢
  ext i k
  obtain ⟨o, rfl⟩ := e.surjective i
  obtain ⟨o', rfl⟩ := e.surjective k
  rw [conjTranspose_mul_diagonal_mul_apply, sum_eq_none_add_sum_some e]
  rcases o with _ | a <;> rcases o' with _ | b
  · simp [blk_none_none, blk_some_none]
  · simp [blk_none_none, blk_some_none, blk_none_some]
  · simp [blk_none_some, blk_some_none]
  · have := congrFun₂ hm a b
    rw [conjTranspose_mul_diagonal_mul_apply] at this
    simp only [blk_none_some, blk_some_some, hs, star_zero, zero_mul, zero_add]
    rw [this]
    simp [Matrix.diagonal_apply, hs]

open MeasureTheory Matrix Filter Topology in
open scoped ENNReal NNReal in
variable {P Q P' Q' : ℕ} in
private lemma blk_one_global_interpolation (e : Option (Fin P' ⊕ Fin Q') ≃ (Fin P ⊕ Fin Q)) :
    _root_.GlobalTheory.BlockEmbedding.blk e 1 = 1 := by
  ext i k
  obtain ⟨o, rfl⟩ := e.surjective i
  obtain ⟨o', rfl⟩ := e.surjective k
  rcases o with _ | a <;> rcases o' with _ | b <;>
    simp [blk_none_none, blk_none_some, blk_some_none, blk_some_some,
      Matrix.one_apply]

open MeasureTheory Matrix Filter Topology in
open scoped ENNReal NNReal in
variable {P Q P' Q' : ℕ} in
private lemma blk_mul_global_interpolation (e : Option (Fin P' ⊕ Fin Q') ≃ (Fin P ⊕ Fin Q))
    (m n : Matrix (Fin P' ⊕ Fin Q') (Fin P' ⊕ Fin Q') ℂ) :
    _root_.GlobalTheory.BlockEmbedding.blk e (m * n) =
      _root_.GlobalTheory.BlockEmbedding.blk e m * _root_.GlobalTheory.BlockEmbedding.blk e n := by
  ext i k
  obtain ⟨o, rfl⟩ := e.surjective i
  obtain ⟨o', rfl⟩ := e.surjective k
  rw [Matrix.mul_apply, sum_eq_none_add_sum_some e]
  rcases o with _ | a <;> rcases o' with _ | b <;>
    simp [blk_none_none, blk_none_some, blk_some_none, blk_some_some,
      Matrix.mul_apply]

open MeasureTheory Matrix Filter Topology in
open scoped ENNReal NNReal in
variable {P Q P' Q' : ℕ} in

theorem _root_.GlobalTheory.BlockEmbedding.exists_blockEmb : ∀ (P Q P' Q' : ℕ) (e : Option (Fin P' ⊕ Fin Q') ≃ (Fin P ⊕ Fin Q)),
    _root_.GlobalTheory.CompactDualQuot.SignCompat e → ∃ j : _root_.Formalism.BasicNotions.UpqT P' Q' →* _root_.Formalism.BasicNotions.UpqT P Q, _root_.GlobalTheory.CompactDualQuot.IsBlockEmb e j ∧ Topology.IsClosedEmbedding j ∧
      Set.range j = {g | _root_.GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding.act g (_root_.GlobalTheory.CompactDualQuot.baseVec e) = _root_.GlobalTheory.CompactDualQuot.baseVec e} := by
  intro P Q P' Q' e hs
  have hmatCE := _root_.GlobalTheory.UpqTopology.isClosedEmbedding_mat (P := P) (Q := Q)
  have hmat_inj : Function.Injective (_root_.Formalism.BasicNotions.UpqT.mat (P := P) (Q := Q)) := hmatCE.injective
  have hrange : ∀ g : _root_.Formalism.BasicNotions.UpqT P' Q', _root_.GlobalTheory.BlockEmbedding.blk e g.mat ∈ Set.range _root_.Formalism.BasicNotions.UpqT.mat := by
    intro g
    have hg : g.mat ∈ Set.range _root_.Formalism.BasicNotions.UpqT.mat := ⟨g, rfl⟩
    rw [_root_.GlobalTheory.UpqTopology.range_mat] at hg ⊢
    exact blk_preserves_Jpq e hs _ hg
  let j : _root_.Formalism.BasicNotions.UpqT P' Q' →* _root_.Formalism.BasicNotions.UpqT P Q :=
    { toFun := fun g => (hrange g).choose
      map_one' := by
        apply hmat_inj
        rw [(hrange 1).choose_spec]
        exact (congrArg _ rfl).trans ((blk_one_global_interpolation e).trans rfl)
      map_mul' := fun g h => by
        apply hmat_inj
        rw [(hrange (g * h)).choose_spec]
        change _root_.GlobalTheory.BlockEmbedding.blk e (g.mat * h.mat) = (hrange g).choose.mat * (hrange h).choose.mat
        rw [(hrange g).choose_spec, (hrange h).choose_spec, blk_mul_global_interpolation] }
  have hj : ∀ g, (j g).mat = _root_.GlobalTheory.BlockEmbedding.blk e g.mat := fun g => (hrange g).choose_spec
  refine ⟨j, ?_, ?_, ?_⟩
  · unfold _root_.GlobalTheory.CompactDualQuot.IsBlockEmb
    intro g
    rw [hj]
    exact ⟨blk_none_none e _, fun b => blk_none_some e _ b,
      fun a => blk_some_none e _ a, fun a b => blk_some_some e _ a b⟩
  · have hcomp : _root_.Formalism.BasicNotions.UpqT.mat ∘ ⇑j = _root_.GlobalTheory.BlockEmbedding.blk e ∘ _root_.Formalism.BasicNotions.UpqT.mat := funext hj
    have hblkCE : IsClosedEmbedding (_root_.GlobalTheory.BlockEmbedding.blk e) := by
      refine Function.LeftInverse.isClosedEmbedding
        (f := fun M : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ => fun a b => M (e (some a)) (e (some b)))
        ?_ ?_ ?_
      · intro m
        funext a b
        exact blk_some_some e m a b
      · fun_prop
      · refine continuous_pi fun i => continuous_pi fun l => ?_
        simp only [_root_.GlobalTheory.BlockEmbedding.blk, Matrix.of_apply]
        rcases e.symm i with _ | a <;> rcases e.symm l with _ | b <;> simp only [Option.elim] <;>
          fun_prop
    rw [← IsClosedEmbedding.of_comp_iff hmatCE, hcomp]
    exact hblkCE.comp _root_.GlobalTheory.UpqTopology.isClosedEmbedding_mat
  · ext g
    simp only [Set.mem_range, Set.mem_setOf_eq]
    unfold _root_.GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding.act _root_.GlobalTheory.CompactDualQuot.baseVec
    rw [Matrix.mulVec_single_one]
    constructor
    · rintro ⟨h, rfl⟩
      funext i
      obtain ⟨o, rfl⟩ := e.surjective i
      rw [Matrix.col_apply, hj]
      rcases o with _ | a
      · simp [blk_none_none]
      · simp [blk_some_none]
    · intro hg
      have hcol : ∀ i, g.mat i (e none) = (Pi.single (e none) (1 : ℂ) : Fin P ⊕ Fin Q → ℂ) i :=
        fun i => by simpa [Matrix.col_apply] using congrFun hg i
      have hU : g.matᴴ * _root_.Formalism.UG.Jpq P Q * g.mat = _root_.Formalism.UG.Jpq P Q := by
        have hmem : g.mat ∈ Set.range _root_.Formalism.BasicNotions.UpqT.mat := ⟨g, rfl⟩
        rwa [_root_.GlobalTheory.UpqTopology.range_mat] at hmem
      rw [Jpq_eq_diagonal_sg] at hU
      have hsn : (_root_.GlobalTheory.CompactDualQuot.sg (e none) : ℂ) ≠ 0 := by
        exact_mod_cast _root_.GlobalTheory.CompactDualQuot.sg_ne_zero _
      have hrow : ∀ l, g.mat (e none) l = (Pi.single (e none) (1 : ℂ) : Fin P ⊕ Fin Q → ℂ) l := by
        intro l
        have hl := congrFun₂ hU (e none) l
        rw [conjTranspose_mul_diagonal_mul_apply, Finset.sum_eq_single (e none)] at hl
        · rw [hcol, Pi.single_eq_same, star_one, one_mul, Matrix.diagonal_apply] at hl
          by_cases hnl : e none = l
          · subst hnl
            rw [if_pos rfl] at hl
            rw [Pi.single_eq_same]
            exact mul_left_cancel₀ hsn (hl.trans (mul_one _).symm)
          · rw [if_neg hnl] at hl
            have hz : (Pi.single (e none) (1 : ℂ) : Fin P ⊕ Fin Q → ℂ) l = 0 := by simp [Ne.symm hnl]
            rw [hz]
            exact (mul_eq_zero.mp hl).resolve_left hsn
        · intro k _ hk
          have hz : (Pi.single (e none) (1 : ℂ) : Fin P ⊕ Fin Q → ℂ) k = 0 := by simp [hk]
          rw [hcol, hz, star_zero, zero_mul, zero_mul]
        · intro hn
          exact absurd (Finset.mem_univ _) hn
      obtain ⟨m, hmdef⟩ : ∃ m : Matrix (Fin P' ⊕ Fin Q') (Fin P' ⊕ Fin Q') ℂ,
          ∀ a b, m a b = g.mat (e (some a)) (e (some b)) := ⟨Matrix.of fun a b => _, fun _ _ => rfl⟩
      have hm : mᴴ * _root_.Formalism.UG.Jpq P' Q' * m = _root_.Formalism.UG.Jpq P' Q' := by
        rw [Jpq_eq_diagonal_sg]
        ext a b
        have hab := congrFun₂ hU (e (some a)) (e (some b))
        rw [conjTranspose_mul_diagonal_mul_apply, sum_eq_none_add_sum_some e, hrow, hrow] at hab
        rw [conjTranspose_mul_diagonal_mul_apply]
        have hs' : ∀ i, _root_.GlobalTheory.CompactDualQuot.sg (e (some i)) = _root_.GlobalTheory.CompactDualQuot.sg i := hs
        simpa [hmdef, hs', Matrix.diagonal_apply] using hab
      obtain ⟨h, hh⟩ : m ∈ Set.range _root_.Formalism.BasicNotions.UpqT.mat := by
        rw [_root_.GlobalTheory.UpqTopology.range_mat]
        exact hm
      refine ⟨h, hmat_inj ?_⟩
      rw [hj, hh]
      ext i k
      obtain ⟨o, rfl⟩ := e.surjective i
      obtain ⟨o', rfl⟩ := e.surjective k
      rcases o with _ | a <;> rcases o' with _ | b
      · rw [blk_none_none, hrow]
        simp
      · rw [blk_none_some, hrow]
        simp
      · rw [blk_some_none, hcol]
        simp
      · rw [blk_some_some, hmdef]

end GlobalTheory.BlockEmbedding
