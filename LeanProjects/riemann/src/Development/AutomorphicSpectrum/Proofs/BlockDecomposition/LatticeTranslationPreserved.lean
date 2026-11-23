import Mathlib
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.HeckeEta
import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasWeil
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaLiftEisensteinLevelSubgroup
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TsumMeas
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BlockMatrixInjective
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PartialConstantTermBound

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.FJE.Transport

open GlobalTheory.StdUnn.Model (submatrix_fromBlocks_mul)
open GlobalTheory.CompanionTheory.ThTw (block_mul₂ bl_add mat_nzx_sh block_matrix_injective adj_sub')
open GlobalTheory.CompanionTheory.PcB (mat_mul' rational_map_block_matrix rat_one' rat_zero' rat_neg')
open GlobalTheory.CompanionTheory.FourierN (mat_injective)

variable {D : D7} {n ρ p : ℕ} {hn : ρ + p = n}

theorem adelicConjTranspose_blockMatrixTwoByTwoFin {k : ℕ} (a b c d : Mx D k k) :
    adj (blk4 a b c d) = blk4 (adj a) (adj c) (adj b) (adj d) := by
  simp only [adj, blk4]
  rw [← Matrix.submatrix_map, Matrix.transpose_submatrix, Matrix.fromBlocks_map, Matrix.fromBlocks_transpose]

theorem block_matrix_diagonal_one_eq_one {k : ℕ} : blk4 (1 : Mx D k k) 0 0 1 = 1 := by
  simp only [blk4, Matrix.fromBlocks_one, Matrix.submatrix_one_equiv]

theorem jr_eq {k : ℕ} : JR (AF D.host.F) (Jst D k) = (blk4 0 1 (-1) 0 : Mx D (k + k) (k + k)) := by
  show rat (blk4 0 1 (-1) 0) = _
  rw [rational_map_block_matrix, rat_one', rat_zero', rat_neg', rat_one']

theorem rel_left {k : ℕ} (g : G D k) {a b c d : Mx D k k} (h : mat g = blk4 a b c d) :
    adj d ⬝ a - adj b ⬝ c = 1 ∧ adj a ⬝ c = adj c ⬝ a ∧ adj b ⬝ d = adj d ⬝ b ∧ adj a ⬝ d - adj c ⬝ b = 1 := by
  have h2 : adj (mat g) * JR (AF D.host.F) (Jst D k) * mat g = JR (AF D.host.F) (Jst D k) := g.2
  rw [jr_eq, h, adelicConjTranspose_blockMatrixTwoByTwoFin, submatrix_fromBlocks_mul, submatrix_fromBlocks_mul] at h2
  obtain ⟨e1, e2, e3, e4⟩ := block_matrix_injective h2
  simp only [Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_one, Matrix.mul_neg, add_zero, zero_add, Matrix.neg_mul] at e1 e2 e3 e4
  refine ⟨?_, (neg_add_eq_zero.1 e1).symm, (neg_add_eq_zero.1 e4).symm, ?_⟩
  · have : adj d ⬝ a - adj b ⬝ c = -(-(adj d ⬝ a) + adj b ⬝ c) := by abel
    rw [this, e3, neg_neg]
  · rw [sub_eq_neg_add, e2]

theorem rel_right {k : ℕ} (g : G D k) {a b c d : Mx D k k} (h : mat g = blk4 a b c d) :
    a ⬝ adj d - b ⬝ adj c = 1 ∧ c ⬝ adj d = d ⬝ adj c ∧ b ⬝ adj a = a ⬝ adj b ∧ d ⬝ adj a - c ⬝ adj b = 1 := by
  obtain ⟨l1, l2, l3, l4⟩ := rel_left g h
  have hL : (blk4 (adj d) (-adj b) (-adj c) (adj a) : Mx D (k + k) (k + k)) * blk4 a b c d = 1 := by
    rw [submatrix_fromBlocks_mul, ← block_matrix_diagonal_one_eq_one]
    congr 1
    · rw [Matrix.neg_mul, ← sub_eq_add_neg, l1]
    · rw [Matrix.neg_mul, ← sub_eq_add_neg, l3, sub_self]
    · rw [Matrix.neg_mul, l2, neg_add_cancel]
    · rw [Matrix.neg_mul, ← sub_eq_neg_add, l4]
  have hR := mul_eq_one_comm.1 hL
  rw [submatrix_fromBlocks_mul, ← block_matrix_diagonal_one_eq_one] at hR
  obtain ⟨e1, e2, e3, e4⟩ := block_matrix_injective hR
  simp only [Matrix.mul_neg] at e1 e2 e3 e4
  refine ⟨by rw [sub_eq_add_neg, e1], sub_eq_zero.1 (by rw [sub_eq_add_neg, e3]),
    (neg_add_eq_zero.1 e2).symm, by rw [sub_eq_neg_add, e4]⟩

theorem exists_rat_blocks {k : ℕ} (γ : G D k) (h : γ ∈ GF D k) :
    ∃ a b c d : Matrix (Fin k) (Fin k) D.host.E, mat γ = blk4 (rat a) (rat b) (rat c) (rat d) := by
  obtain ⟨x, -, hxe⟩ := h
  have hm : mat γ = rat x.1 := (congrArg Units.val hxe).symm
  refine ⟨(x.1.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₁₁,
    (x.1.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₁₂,
    (x.1.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₂₁,
    (x.1.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₂₂, ?_⟩
  rw [hm, ← rational_map_block_matrix]
  congr 1
  simp only [blk4, Matrix.fromBlocks_toBlocks, Matrix.submatrix_submatrix, Equiv.self_comp_symm, Matrix.submatrix_id_id]

theorem comb_sub (a b : Mx D ρ p) (P Q R S U V : Mx D p p) :
    (a ⬝ P - b ⬝ Q) ⬝ R + (b ⬝ S - a ⬝ U) ⬝ V = a ⬝ (P ⬝ R - U ⬝ V) + b ⬝ (S ⬝ V - Q ⬝ R) := by
  simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_assoc]
  abel

theorem comb_add (a b : Mx D ρ p) (P Q R S U V : Mx D p p) :
    (a ⬝ P + b ⬝ Q) ⬝ R - (a ⬝ S + b ⬝ U) ⬝ V = a ⬝ (P ⬝ R - S ⬝ V) + b ⬝ (Q ⬝ R - U ⬝ V) := by
  simp only [Matrix.add_mul, Matrix.mul_sub, Matrix.mul_assoc]
  abel

theorem cont_rmul (c : Mx D p p) : Continuous fun v : Mx D ρ p => v ⬝ c :=
  continuous_id.matrix_mul continuous_const

theorem cont_sub {X : Type*} [TopologicalSpace X] {f g : X → Mx D ρ p} (hf : Continuous f) (hg : Continuous g) :
    Continuous fun v => f v - g v := by
  have h₁ : IsTopologicalRing (AE D) := inferInstance
  have h₂ : IsTopologicalAddGroup (AE D) := inferInstance
  have h₃ : ContinuousSub (AE D) := IsTopologicalAddGroup.to_continuousSub
  exact continuous_matrix fun i j => (hf.matrix_elem i j).sub (hg.matrix_elem i j)

theorem cont_add {X : Type*} [TopologicalSpace X] {f g : X → Mx D ρ p} (hf : Continuous f) (hg : Continuous g) :
    Continuous fun v => f v + g v :=
  continuous_matrix fun i j => (hf.matrix_elem i j).add (hg.matrix_elem i j)

def tEquiv (a b c d : Mx D p p)
    (l1 : adj d ⬝ a - adj b ⬝ c = 1) (l2 : adj a ⬝ c = adj c ⬝ a) (l3 : adj b ⬝ d = adj d ⬝ b)
    (l4 : adj a ⬝ d - adj c ⬝ b = 1)
    (r1 : a ⬝ adj d - b ⬝ adj c = 1) (r2 : c ⬝ adj d = d ⬝ adj c) (r3 : b ⬝ adj a = a ⬝ adj b)
    (r4 : d ⬝ adj a - c ⬝ adj b = 1) :
    (Mx D ρ p × Mx D ρ p) ≃ₜ+ (Mx D ρ p × Mx D ρ p) where
  toFun v := (v.1 ⬝ adj d - v.2 ⬝ adj c, v.2 ⬝ adj a - v.1 ⬝ adj b)
  invFun v := (v.1 ⬝ a + v.2 ⬝ c, v.1 ⬝ b + v.2 ⬝ d)
  left_inv v := by
    refine Prod.ext ?_ ?_
    · show (v.1 ⬝ adj d - v.2 ⬝ adj c) ⬝ a + (v.2 ⬝ adj a - v.1 ⬝ adj b) ⬝ c = v.1
      rw [comb_sub, l1, l2, sub_self, Matrix.mul_one, Matrix.mul_zero, add_zero]
    · show (v.1 ⬝ adj d - v.2 ⬝ adj c) ⬝ b + (v.2 ⬝ adj a - v.1 ⬝ adj b) ⬝ d = v.2
      rw [comb_sub, l4, l3, sub_self, Matrix.mul_one, Matrix.mul_zero, zero_add]
  right_inv v := by
    refine Prod.ext ?_ ?_
    · show (v.1 ⬝ a + v.2 ⬝ c) ⬝ adj d - (v.1 ⬝ b + v.2 ⬝ d) ⬝ adj c = v.1
      rw [comb_add, r1, r2, sub_self, Matrix.mul_one, Matrix.mul_zero, add_zero]
    · show (v.1 ⬝ b + v.2 ⬝ d) ⬝ adj a - (v.1 ⬝ a + v.2 ⬝ c) ⬝ adj b = v.2
      rw [comb_add, r3, r4, sub_self, Matrix.mul_one, Matrix.mul_zero, zero_add]
  map_add' u v := by
    refine Prod.ext ?_ ?_
    · show (u.1 + v.1) ⬝ adj d - (u.2 + v.2) ⬝ adj c = (u.1 ⬝ adj d - u.2 ⬝ adj c) + (v.1 ⬝ adj d - v.2 ⬝ adj c)
      simp only [Matrix.add_mul]
      abel
    · show (u.2 + v.2) ⬝ adj a - (u.1 + v.1) ⬝ adj b = (u.2 ⬝ adj a - u.1 ⬝ adj b) + (v.2 ⬝ adj a - v.1 ⬝ adj b)
      simp only [Matrix.add_mul]
      abel
  continuous_toFun := by
    refine Continuous.prodMk ?_ ?_
    · exact cont_sub ((cont_rmul _).comp continuous_fst) ((cont_rmul _).comp continuous_snd)
    · exact cont_sub ((cont_rmul _).comp continuous_snd) ((cont_rmul _).comp continuous_fst)
  continuous_invFun := by
    refine Continuous.prodMk ?_ ?_
    · exact cont_add ((cont_rmul _).comp continuous_fst) ((cont_rmul _).comp continuous_snd)
    · exact cont_add ((cont_rmul _).comp continuous_fst) ((cont_rmul _).comp continuous_snd)

set_option maxHeartbeats 1000000 in

theorem emb_conj (M : Maps D hn) (g : G D p) {a b c d : Mx D p p} (hg : mat g = blk4 a b c d)
    (z' : hermA D ρ) (x y x' y' : Mx D ρ p)
    (h1 : y' ⬝ a + x' ⬝ c = y) (h2 : y' ⬝ b + x' ⬝ d = x)
    (h3 : adj x' = a ⬝ adj x - b ⬝ adj y) (h4 : adj y' = d ⬝ adj y - c ⬝ adj x)
    (h5 : z'.1 - x' ⬝ (d ⬝ adj y - c ⬝ adj x) = -(x ⬝ adj y)) :
    M.emb g * (M.nzx 0 x * M.sh y) = M.nzx z' x' * M.sh y' * M.emb g := by
  have hE := M.emb_mat g _ _ _ _ hg
  apply mat_injective
  rw [mat_mul' (M.emb g), mat_mul' _ (M.emb g), mat_nzx_sh, mat_nzx_sh, hE, submatrix_fromBlocks_mul, submatrix_fromBlocks_mul]
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, block_mul₂, bl_add, Matrix.one_mul, Matrix.mul_one,
    Matrix.mul_neg, Matrix.neg_mul, neg_zero, h1, h2, h3, h4, h5, neg_sub, AddSubgroup.coe_zero, zero_sub,
    sub_eq_add_neg (a ⬝ adj x), sub_eq_add_neg (c ⬝ adj x)]

def zTv (a b c d : Mx D p p) (x y : Mx D ρ p) : Mx D ρ ρ :=
  x ⬝ ((adj c ⬝ b) ⬝ adj y) + y ⬝ ((adj b ⬝ c) ⬝ adj x) - x ⬝ ((adj a ⬝ c) ⬝ adj x) - y ⬝ ((adj b ⬝ d) ⬝ adj y)

theorem zTv_herm {a b c d : Mx D p p} (l2 : adj a ⬝ c = adj c ⬝ a) (l3 : adj b ⬝ d = adj d ⬝ b) (x y : Mx D ρ p) :
    adj (zTv a b c d x y) = zTv a b c d x y := by
  simp only [zTv, adj_sub', adj_add, adj_mul, adj_adj, ← l2, ← l3]
  simp only [Matrix.mul_assoc]
  abel

theorem zTv_eq {a b c d : Mx D p p} (l4 : adj a ⬝ d - adj c ⬝ b = 1) (x y : Mx D ρ p) :
    zTv a b c d x y - (x ⬝ adj a - y ⬝ adj b) ⬝ (d ⬝ adj y - c ⬝ adj x) = -(x ⬝ adj y) := by
  have e : ∀ w : Mx D p ρ, adj a ⬝ (d ⬝ w) = w + adj c ⬝ (b ⬝ w) := fun w => by
    rw [← Matrix.mul_assoc, sub_eq_iff_eq_add.1 l4, Matrix.add_mul, Matrix.one_mul, Matrix.mul_assoc]
  simp only [zTv, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_assoc, e, Matrix.mul_add]
  abel

theorem rational_map_sub {k l : ℕ} (u v : Matrix (Fin k) (Fin l) D.host.E) : rat (D := D) (u - v) = rat u - rat v := by
  ext i j
  exact map_sub (incA D) _ _

theorem rational_map_add {k l : ℕ} (u v : Matrix (Fin k) (Fin l) D.host.E) : rat (D := D) (u + v) = rat u + rat v := by
  ext i j
  exact map_add (incA D) _ _

theorem transport {D : D7} {n ρ p : ℕ} {hn : ρ + p = n} (M : Maps D hn) (γ : G D p) (hγ : γ ∈ GF D p) :
    ∃ T : (Mx D ρ p × Mx D ρ p) ≃ₜ+ (Mx D ρ p × Mx D ρ p),
      (∀ ξ₁ ξ₂ : Matrix (Fin ρ) (Fin p) D.host.E, ∃ ξ₁' ξ₂' : Matrix (Fin ρ) (Fin p) D.host.E,
        T (GlobalTheory.CompanionTheory.FJE.rt ξ₁, GlobalTheory.CompanionTheory.FJE.rt ξ₂) = (GlobalTheory.CompanionTheory.FJE.rt ξ₁', GlobalTheory.CompanionTheory.FJE.rt ξ₂')) ∧
      (∀ ξ₁ ξ₂ : Matrix (Fin ρ) (Fin p) D.host.E, ∃ ξ₁' ξ₂' : Matrix (Fin ρ) (Fin p) D.host.E,
        T.symm (GlobalTheory.CompanionTheory.FJE.rt ξ₁, GlobalTheory.CompanionTheory.FJE.rt ξ₂) = (GlobalTheory.CompanionTheory.FJE.rt ξ₁', GlobalTheory.CompanionTheory.FJE.rt ξ₂')) ∧
      ∀ y x : Mx D ρ p, ∃ z' : hermA D ρ,
        M.emb γ * (M.nzx 0 x * M.sh y) = M.nzx z' (T (y, x)).2 * M.sh (T (y, x)).1 * M.emb γ := by
  obtain ⟨a, b, c, d, hm⟩ := exists_rat_blocks γ hγ
  obtain ⟨l1, l2, l3, l4⟩ := rel_left γ hm
  obtain ⟨r1, r2, r3, r4⟩ := rel_right γ hm
  refine ⟨tEquiv (ρ := ρ) _ _ _ _ l1 l2 l3 l4 r1 r2 r3 r4, ?_, ?_, ?_⟩
  · intro ξ₁ ξ₂
    refine ⟨ξ₁ * dᴴ - ξ₂ * cᴴ, ξ₂ * aᴴ - ξ₁ * bᴴ, ?_⟩
    show (rat ξ₁ ⬝ adj (rat d) - rat ξ₂ ⬝ adj (rat c), rat ξ₂ ⬝ adj (rat a) - rat ξ₁ ⬝ adj (rat b)) =
      (rat (ξ₁ * dᴴ - ξ₂ * cᴴ), rat (ξ₂ * aᴴ - ξ₁ * bᴴ))
    simp only [rational_map_sub, rat_mul, rat_conjTranspose]
  · intro ξ₁ ξ₂
    refine ⟨ξ₁ * a + ξ₂ * c, ξ₁ * b + ξ₂ * d, ?_⟩
    show (rat ξ₁ ⬝ rat a + rat ξ₂ ⬝ rat c, rat ξ₁ ⬝ rat b + rat ξ₂ ⬝ rat d) =
      (rat (ξ₁ * a + ξ₂ * c), rat (ξ₁ * b + ξ₂ * d))
    simp only [rational_map_add, rat_mul]
  · intro y x
    refine ⟨⟨zTv (rat a) (rat b) (rat c) (rat d) x y, zTv_herm l2 l3 x y⟩, ?_⟩
    refine emb_conj M γ hm _ x y _ _ ?_ ?_ ?_ ?_ (zTv_eq l4 x y)
    · show (y ⬝ adj (rat d) - x ⬝ adj (rat c)) ⬝ rat a + (x ⬝ adj (rat a) - y ⬝ adj (rat b)) ⬝ rat c = y
      rw [comb_sub, l1, l2, sub_self, Matrix.mul_one, Matrix.mul_zero, add_zero]
    · show (y ⬝ adj (rat d) - x ⬝ adj (rat c)) ⬝ rat b + (x ⬝ adj (rat a) - y ⬝ adj (rat b)) ⬝ rat d = x
      rw [comb_sub, l4, l3, sub_self, Matrix.mul_one, Matrix.mul_zero, zero_add]
    · show adj (x ⬝ adj (rat a) - y ⬝ adj (rat b)) = _
      rw [adj_sub', adj_mul, adj_mul, adj_adj, adj_adj]
    · show adj (y ⬝ adj (rat d) - x ⬝ adj (rat c)) = _
      rw [adj_sub', adj_mul, adj_mul, adj_adj, adj_adj]

end GlobalTheory.CompanionTheory.FJE.Transport
