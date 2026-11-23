import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocalL2IsometryAlt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExtensionAdeleRealComponentsCmType
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NondegenerateCharacterCellFactorization
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.AwayAA
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.AwayAC

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 100000

namespace PositivityTheory.Rg.Sw.Glob.AW

variable {D : D7} {n : ℕ}

def AG (θ : InfFam D) (τ : D.what₂.Tau) (x : G D n) : Prop :=
  IsTrivAt θ τ x ∧ ((∃ b, mat x = blk4 1 b 0 1) ∨ (∃ a d, mat x = blk4 a 0 0 d) ∨ (∃ c, mat x = blk4 1 0 c 1))

def AgreeAway {m k : ℕ} (θ : InfFam D) (τ : D.what₂.Tau) (x x' : Mx D m k) : Prop :=
  (∀ τ', τ' ≠ τ → compAt θ τ' x = compAt θ τ' x') ∧ x.map (finPart D) = x'.map (finPart D)

theorem mem_closure_AG (hG : GenA) (hDA : DecompAway) {θ : InfFam D} {τ : D.what₂.Tau} {ι : GR n →* G D n}
    (hθ : IsInfFam θ) (hι : IsPlaceEmb θ τ ι) (x : G D n) (hx : IsTrivAt θ τ x) :
    x ∈ Submonoid.closure {x : G D n | AG θ τ x} :=
  closure_triv hG hDA hθ hι x hx

theorem exists_w (D : D7) (n : ℕ) : ∃ w : G D n, mat w = blk4 0 1 (-1) 0 := by
  obtain ⟨g, hg⟩ := GlobalTheory.SiegelCells.exists_wPart (D := D) (n := n) n
  refine ⟨g, hg.trans ?_⟩
  have hL : GlobalTheory.SiegelCells.lastDiag (AE D) n n = 1 := by
    unfold GlobalTheory.SiegelCells.lastDiag
    rw [← Matrix.diagonal_one]
    congr 1; funext i; simp
  rw [GlobalTheory.SiegelCells.wMat, hL, sub_self]

theorem compAt_b_zero {θ : InfFam D} {τ : D.what₂.Tau} {x : G D n} {b : Mx D n n} (hx : IsTrivAt θ τ x)
    (h : mat x = blk4 1 b 0 1) : compAt θ τ b = 0 := by
  have h1 : compAt θ τ (mat x) = blk4 1 (compAt θ τ b) 0 1 := by rw [h, component_block_matrix, compAt_one', compAt_zero']
  have h2 : (blk4 1 0 0 1 : Matrix (Fin (n + n)) (Fin (n + n)) ℂ) = blk4 1 (compAt θ τ b) 0 1 := by
    rw [GlobalTheory.StdUnn.Model.block_matrix_one, ← h1]; exact hx.symm
  exact (GlobalTheory.StdUnn.Model.blockMatrixTwoByTwoFin_injective h2).2.1.symm

theorem compAt_a_one {θ : InfFam D} {τ : D.what₂.Tau} {x : G D n} {a d : Mx D n n} (hx : IsTrivAt θ τ x)
    (h : mat x = blk4 a 0 0 d) : compAt θ τ a = 1 := by
  have h1 : compAt θ τ (mat x) = blk4 (compAt θ τ a) 0 0 (compAt θ τ d) := by rw [h, component_block_matrix, compAt_zero']
  have h2 : (blk4 1 0 0 1 : Matrix (Fin (n + n)) (Fin (n + n)) ℂ) = blk4 (compAt θ τ a) 0 0 (compAt θ τ d) := by
    rw [GlobalTheory.StdUnn.Model.block_matrix_one, ← h1]; exact hx.symm
  exact (GlobalTheory.StdUnn.Model.blockMatrixTwoByTwoFin_injective h2).1.symm

theorem compAt_mul_of_one {θ : InfFam D} {τ : D.what₂.Tau} {m k : ℕ} (x : Mx D m k) (a : Mx D k k)
    (ha : compAt θ τ a = 1) : compAt θ τ (x ⬝ a : Mx D m k) = compAt θ τ x := by
  rw [compAt_mul', ha, Matrix.mul_one]

theorem agree_mul_right {θ : InfFam D} {τ : D.what₂.Tau} {m k : ℕ} {x x' : Mx D m k} (a : Mx D k k)
    (h : AgreeAway θ τ x x') : AgreeAway θ τ (x ⬝ a : Mx D m k) (x' ⬝ a : Mx D m k) := by
  refine ⟨fun τ' hτ' => ?_, ?_⟩
  · rw [compAt_mul', compAt_mul', h.1 τ' hτ']
  · rw [Matrix.map_mul, Matrix.map_mul, h.2]

theorem unipArg_away {θ : InfFam D} {τ : D.what₂.Tau} (hθ : IsInfFam θ) (V : HSp D) {b : Mx D n n}
    (hb : compAt θ τ b = 0) {x x' : Mx D V.rank n} (h : AgreeAway θ τ x x') :
    halfTr (Matrix.trace (b ⬝ inner V x x : Mx D n n)) = halfTr (Matrix.trace (b ⬝ inner V x' x' : Mx D n n)) := by
  have htr : ∀ (R : Type) [CommRing R] (f : AE D →+* R) (M : Mx D n n), f (Matrix.trace M) = Matrix.trace (M.map f) := by
    intro R _ f M
    simp only [Matrix.trace, Matrix.diag, Matrix.map_apply]
    exact map_sum f _ _
  have hinner : ∀ τ'', τ'' ≠ τ → compAt θ τ'' (inner V x x) = compAt θ τ'' (inner V x' x') := by
    intro τ'' hτ''
    have hx := h.1 τ'' hτ''
    have hadj : compAt θ τ'' (adj x) = compAt θ τ'' (adj x') := by
      ext i j
      have := congrFun (congrFun hx j) i
      simp only [compAt_eq, Matrix.map_apply] at this ⊢
      simp only [adj, Matrix.transpose_apply, Matrix.map_apply]
      rw [cθ_cA hθ, cθ_cA hθ, this]
    simp only [GlobalTheory.StdUnn.inner]
    rw [compAt_mul', compAt_mul', compAt_mul', compAt_mul', hadj, hx]
  have hfin : (inner V x x).map (finPart D) = (inner V x' x').map (finPart D) := by
    have hadj : (adj x).map (finPart D) = (adj x').map (finPart D) := by
      ext i j
      have := congrFun (congrFun h.2 j) i
      simp only [Matrix.map_apply] at this ⊢
      simp only [adj, Matrix.transpose_apply, Matrix.map_apply]
      rw [finPart_cA, finPart_cA, this]
    simp only [GlobalTheory.StdUnn.inner]
    rw [Matrix.map_mul, Matrix.map_mul, Matrix.map_mul, Matrix.map_mul, hadj, h.2]
  congr 1
  apply ae_ext hθ
  · intro τ''
    rw [htr, htr, ← compAt_eq, ← compAt_eq, compAt_mul', compAt_mul']
    by_cases hτ : τ'' = τ
    · subst hτ; rw [hb, Matrix.zero_mul, Matrix.zero_mul]
    · rw [hinner τ'' hτ]
  · rw [htr, htr, Matrix.map_mul, Matrix.map_mul, hfin]

theorem exists_change_tau {θ : InfFam D} {τ : D.what₂.Tau} (hθ : IsInfFam θ) {m k : ℕ} (xs x0 : Mx D m k) :
    ∃ x1 : Mx D m k, compAt θ τ x1 = compAt θ τ x0 ∧ AgreeAway θ τ x1 xs := by
  obtain ⟨-, hfin, hcomp⟩ := GlobalTheory.WeilVacMove.isLineAt_lineAt (D := D) hθ τ (compAt θ τ x0 - compAt θ τ xs)
  refine ⟨xs + lineAt θ τ (compAt θ τ x0 - compAt θ τ xs) 1, ?_, fun τ' hτ' => ?_, ?_⟩
  · rw [compAt_add', hcomp 1 τ, if_pos rfl]; simp
  · rw [compAt_add', hcomp 1 τ', if_neg hτ', add_zero]
  · rw [Matrix.map_add _ (map_add (finPart D)), hfin 1, add_zero]

theorem levi_blocks (g : G D n) {a d : Mx D n n} (h : mat g = blk4 a 0 0 d) :
    ∃ a' : GL (Fin n) (AE D), a'.1 = a ∧ d = adj (a'⁻¹).1 := by
  obtain ⟨-, h2, -, -⟩ := GlobalTheory.CompanionTheory.SwUnf.SmallCell.unitary_rel g h
  simp only [adj_zero, Matrix.zero_mul, neg_zero, zero_add] at h2
  have h3 : adj d * a = 1 := by
    have := congrArg adj h2
    rwa [adj_mul, adj_adj, adj_one] at this
  have h4 : a * adj d = 1 := mul_eq_one_comm.mp h3
  refine ⟨⟨a, adj d, h4, h3⟩, rfl, ?_⟩
  show d = adj (adj d)
  rw [adj_adj]

theorem mat_w_conj {w x : G D n} (hw : mat w = blk4 0 1 (-1) 0) {c : Mx D n n} (hx : mat x = blk4 1 0 c 1) :
    mat (w⁻¹ * x * w) = blk4 1 (-c) 0 1 := by
  rw [GlobalTheory.StdUnn.LeftInvSect.mat_mul, GlobalTheory.StdUnn.LeftInvSect.mat_mul, GlobalTheory.CompanionTheory.SwUnf.SmallCell.mat_inv w hw, hx, hw]
  simp [adj_zero, adj_one, adj_neg, GlobalTheory.StdUnn.Model.submatrix_fromBlocks_mul]

theorem trivAt_conj {θ : InfFam D} {τ : D.what₂.Tau} {x : G D n} (w : G D n) (hx : IsTrivAt θ τ x) :
    IsTrivAt θ τ (w⁻¹ * x * w) := by
  unfold IsTrivAt at *
  have hw : compAt θ τ (mat w⁻¹) * compAt θ τ (mat w) = 1 := by
    rw [← compAt_mul', ← GlobalTheory.StdUnn.LeftInvSect.mat_mul, inv_mul_cancel, GlobalTheory.StdUnn.LeftInvSect.mat_one, compAt_one']
  rw [GlobalTheory.StdUnn.LeftInvSect.mat_mul, GlobalTheory.StdUnn.LeftInvSect.mat_mul, compAt_mul', compAt_mul', hx, Matrix.mul_one, hw]

theorem exists_compAt {θ : InfFam D} {τ : D.what₂.Tau} (hθ : IsInfFam θ) {m k : ℕ} (M : Matrix (Fin m) (Fin k) ℂ) :
    ∃ x : Mx D m k, compAt θ τ x = M := by
  obtain ⟨-, -, hcomp⟩ := GlobalTheory.WeilVacMove.isLineAt_lineAt (D := D) hθ τ M
  exact ⟨lineAt θ τ M 1, by rw [hcomp 1 τ, if_pos rfl]; simp⟩

theorem exists_sch_ne {m k : ℕ} (u0 : Fin m → Fin k → ℂ) : ∃ f : (Fin m → Fin k → ℂ) → ℂ, IsSch f ∧ f u0 ≠ 0 := by
  let b : ContDiffBump u0 := ⟨1, 2, one_pos, one_lt_two⟩
  refine ⟨fun u => ((b u : ℝ) : ℂ), ?_, ?_⟩
  · have hc : HasCompactSupport (fun u => ((b u : ℝ) : ℂ)) := b.hasCompactSupport.comp_left Complex.ofReal_zero
    have hs : ContDiff ℝ (⊤ : ℕ∞) (fun u => ((b u : ℝ) : ℂ)) := Complex.ofRealCLM.contDiff.comp b.contDiff
    exact ⟨hc.toSchwartzMap hs, rfl⟩
  · have : b u0 = 1 := b.one_of_mem_closedBall (Metric.mem_closedBall_self b.rIn_pos.le)
    simp [this]

end PositivityTheory.Rg.Sw.Glob.AW
