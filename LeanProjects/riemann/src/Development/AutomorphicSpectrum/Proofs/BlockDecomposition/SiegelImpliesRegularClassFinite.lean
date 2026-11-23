import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.RegularClassTraces.RegClassFin
import Development.WeilBound.ThetaLifts.Reductions.SiegelCore
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ConstantTermVanishing
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.AdjointRadical
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspidalNoRadicalFixed
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.StandardMaximalParabolic
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CentralizerTensorForms
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ParabolicLeviDecomposition
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.IwahoriSubgroup
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StabUpTo
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SiegelCompactTranslateBoundStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RegularSemisimpleFlagStabilizerStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsWittComplementFrameStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FrameStabilizerFlagCriterionStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FrameStabilizerFlagConverseStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DeepConeWeightRatioBoundStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompactArchimedeanEntriesBoundedStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TorusArchimedeanFrameConjugationStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MinimalParabolicArchimedeanStabilizesStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArchimedeanMatrixPreservesFormStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArchimedeanRationalEmbeddingMapStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompactFiniteRationalDenominatorStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BoundedIntegralMatricesFiniteStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RationalPointsEqEmbeddingStatement
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ImportsSideFurther

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet
open Formalism.UG (cT)
open GlobalTheory.Orb (archMat)
open scoped TensorProduct NNReal ENNReal

noncomputable section

namespace GlobalTheory.CompanionTheory.CFin

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def swapIdx (r m : ℕ) : Idx r m ≃ Idx r m where
  toFun u := match u with
    | .inl i => .inr (.inr i)
    | .inr (.inl k) => .inr (.inl k)
    | .inr (.inr i) => .inl i
  invFun u := match u with
    | .inl i => .inr (.inr i)
    | .inr (.inl k) => .inr (.inl k)
    | .inr (.inr i) => .inl i
  left_inv u := by rcases u with i | k | i <;> rfl
  right_inv u := by rcases u with i | k | i <;> rfl

theorem lev_swapIdx {r m : ℕ} (S : Finset (Fin r)) (u : Idx r m) : lev m S (swapIdx r m u) = - lev m S u := by
  rcases u with i | k | i <;> simp [lev, swapIdx]

theorem frm_swap {A : Type} {n r m : ℕ} (X : Matrix (Fin n) (Fin r) A) (Z : Matrix (Fin n) (Fin m) A)
    (Y : Matrix (Fin n) (Fin r) A) : frm Y Z X = (frm X Z Y).submatrix id (swapIdx r m) := by
  ext a u
  rcases u with i | k | i <;> rfl

theorem bd_eq_self {L : Type} [Field L] (s : L →+* L) (hs : ∀ x, s (s x) = x) {n r m : ℕ}
    {J : Matrix (Fin n) (Fin n) L} {X Y : Matrix (Fin n) (Fin r) L} {Z : Matrix (Fin n) (Fin m) L}
    {Qi : Matrix (Idx r m) (Fin n) L} (hJ : cT s J = J) (xx : cT s X * J * X = 0) (yy : cT s Y * J * Y = 0)
    (xy : cT s X * J * Y = 1) (xz : cT s X * J * Z = 0) (yz : cT s Y * J * Z = 0)
    (hl : Qi * frm X Z Y = 1) (hr : frm X Z Y * Qi = 1) (S : Finset (Fin r)) {g : Matrix (Fin n) (Fin n) L}
    (hg : IsUnit g) (hu : cT s g * J * g = J) (h1 : ∀ j ∈ S, StabUpTo X g j) (h2 : ∀ j ∈ S, StabUpTo Y g j) :
    bd (lev m S) (Qi * g * frm X Z Y) = Qi * g * frm X Z Y := by
  have yx : cT s Y * J * X = 1 := by
    have cc : ∀ W : Matrix (Fin n) (Fin r) L, cT s (cT s W) = W := fun W => Matrix.ext fun i j => hs _
    have := congrArg (cT s) xy
    rwa [Formalism.UG.cT_mul, Formalism.UG.cT_mul, cc, hJ, Formalism.UG.cT_one, ← Matrix.mul_assoc] at this
  let sw := swapIdx r m
  have a1 : (Qi.submatrix sw id) * frm Y Z X = 1 := by
    rw [frm_swap, ← Matrix.submatrix_mul _ _ sw id sw Function.bijective_id, hl, Matrix.submatrix_one_equiv]
  have a2 : frm Y Z X * (Qi.submatrix sw id) = 1 := by
    rw [frm_swap, Matrix.submatrix_mul_equiv, hr]; rfl
  have b1 := GlobalTheory.T.frame_stabilizer_flag_criterion L s hs n r m J X Y Z Qi hJ xx yy xy xz yz hl hr S g hg hu h1
  have b2 := GlobalTheory.T.frame_stabilizer_flag_criterion L s hs n r m J Y X Z (Qi.submatrix sw id) hJ yy xx yx yz xz a1 a2 S g hg hu h2
  ext u v
  simp only [bd, Matrix.of_apply]
  split_ifs with h
  · rfl
  rcases lt_or_gt_of_ne h with h3 | h3
  · have h4 : lev m S (sw v) < lev m S (sw u) := by
      rw [lev_swapIdx, lev_swapIdx]; omega
    have := b2 (i := sw u) (j := sw v) h4
    rw [frm_swap] at this
    have e : (Qi.submatrix sw id * g * (frm X Z Y).submatrix id sw) (sw u) (sw v) = (Qi * g * frm X Z Y) (sw (sw u)) (sw (sw v)) := by
      simp [Matrix.mul_apply, Matrix.submatrix_apply]
    have e2 : ∀ w, sw (sw w) = w := fun w => (swapIdx r m).symm_apply_apply w
    rw [e, e2, e2] at this
    exact this.symm
  · exact (b1 h3).symm

section Levi

variable {σ : E →ₐ[F] E} {n r m : ℕ} {J : Matrix (Fin n) (Fin n) E} {X Y : Matrix (Fin n) (Fin r) E}
  {Z : Matrix (Fin n) (Fin m) E} {Qi : Matrix (Idx r m) (Fin n) E}

theorem block_frame_conjugation_identity {G : Type} [Group G] (a b c : G) : (a * b⁻¹) * c * (a * b⁻¹)⁻¹ = a * (b⁻¹ * c * b) * a⁻¹ := by group

theorem mul_eq_mul_conj_alt {G : Type} [Group G] (a b : G) : a * b = b * (b⁻¹ * a * b) := by group

omit [NumberField F] [NumberField E] in
theorem coord_mul (hr : frm X Z Y * Qi = 1) (a b : Matrix (Fin n) (Fin n) E) :
    Qi * (a * b) * frm X Z Y = (Qi * a * frm X Z Y) * (Qi * b * frm X Z Y) := by
  calc Qi * (a * b) * frm X Z Y = Qi * (a * (frm X Z Y * Qi) * b) * frm X Z Y := by rw [hr, Matrix.mul_one]
    _ = _ := by simp only [Matrix.mul_assoc]

theorem exists_conj_levi (h : IsCMExt F E σ) (hJ : IsHermND σ J) (hW : IsWittFrame σ J X Y)
    (xz : cT (σ : E →+* E) X * J * Z = 0) (yz : cT (σ : E →+* E) Y * J * Z = 0)
    (hl : Qi * frm X Z Y = 1) (hr : frm X Z Y * Qi = 1) (S : Finset (Fin r)) (δ : GRat σ J)
    (hδ : GlobalTheory.Orb.IsRegSS δ.1.1) (hst : ∀ j ∈ S, StabUpTo X δ.1.1 j) :
    ∃ δ' : GRat σ J, IsConj δ δ' ∧ Qi * δ'.1.1 * frm X Z Y = bd (lev m S) (Qi * δ.1.1 * frm X Z Y) := by
  have hs : ∀ x, (σ : E →+* E) ((σ : E →+* E) x) = x := sigma_sigma h
  have hJ' : cT (σ : E →+* E) J = J := Matrix.ext fun i j => hJ.1 _ _
  have tri := fun (g : GRat σ J) (hg : ∀ j ∈ S, StabUpTo X g.1.1 j) =>
    GlobalTheory.T.frame_stabilizer_flag_criterion E (σ : E →+* E) hs n r m J X Y Z Qi hJ' hW.xx hW.yy hW.xy xz yz hl hr S g.1.1 g.1.isUnit g.2 hg
  obtain ⟨g, hg, hμ⟩ := GlobalTheory.T.regular_semisimple_flag_stabilizer F E σ h n J hJ r X Y hW S δ hδ hst
  obtain ⟨μ, hμdef⟩ : ∃ μ : GRat σ J, μ = g⁻¹ * δ * g := ⟨_, rfl⟩
  rw [← hμdef] at hμ
  have hμb : bd (lev m S) (Qi * μ.1.1 * frm X Z Y) = Qi * μ.1.1 * frm X Z Y :=
    bd_eq_self (σ : E →+* E) hs hJ' hW.xx hW.yy hW.xy xz yz hl hr S μ.1.isUnit μ.2
      (fun j hj => (hμ j hj).1) (fun j hj => (hμ j hj).2)
  have tg := tri g hg
  have tδ := tri δ hst
  have tμ : (Qi * μ.1.1 * frm X Z Y).BlockTriangular (lev m S) := tri μ fun j hj => (hμ j hj).1
  have rel : δ * g = g * μ := by rw [hμdef]; exact mul_eq_mul_conj_alt δ g
  have cm : ∀ a b : GRat σ J, Qi * (a * b).1.1 * frm X Z Y = (Qi * a.1.1 * frm X Z Y) * (Qi * b.1.1 * frm X Z Y) :=
    fun a b => coord_mul hr a.1.1 b.1.1
  have rel' : (Qi * δ.1.1 * frm X Z Y) * (Qi * g.1.1 * frm X Z Y) = (Qi * g.1.1 * frm X Z Y) * (Qi * μ.1.1 * frm X Z Y) := by
    rw [← cm, ← cm, rel]
  have rel2 := congrArg (bd (lev m S)) rel'
  rw [bd_mul tδ tg, bd_mul tg tμ, hμb] at rel2
  obtain ⟨hU, hUJ⟩ := GlobalTheory.T.frame_stabilizer_flag_converse E (σ : E →+* E) hs n r m J X Y Z Qi hJ' hW.xx hW.yy hW.xy xz yz hl hr S g.1.1
    g.1.isUnit g.2 tg
  obtain ⟨g', hg'def⟩ : ∃ g' : GRat σ J, g'.1.1 = frm X Z Y * bd (lev m S) (Qi * g.1.1 * frm X Z Y) * Qi :=
    ⟨⟨hU.unit, hUJ⟩, rfl⟩
  set B := bd (lev m S) (Qi * g.1.1 * frm X Z Y) with hB
  have hg' : Qi * g'.1.1 * frm X Z Y = B := by
    rw [hg'def]
    calc _ = (Qi * frm X Z Y) * B * (Qi * frm X Z Y) := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hl, Matrix.one_mul, Matrix.mul_one]
  have e3 : B * (Qi * (g'⁻¹).1.1 * frm X Z Y) = 1 := by
    rw [← hg', ← cm, mul_inv_cancel]
    change Qi * 1 * frm X Z Y = 1
    rw [Matrix.mul_one, hl]
  have conj : (g' * g⁻¹) * δ * (g' * g⁻¹)⁻¹ = g' * μ * g'⁻¹ := by rw [hμdef]; exact block_frame_conjugation_identity g' g δ
  refine ⟨g' * μ * g'⁻¹, isConj_iff.2 ⟨g' * g⁻¹, conj⟩, ?_⟩
  have e1 : (g' * μ * g'⁻¹) * g' = g' * μ := inv_mul_cancel_right _ _
  have e2 : (Qi * (g' * μ * g'⁻¹).1.1 * frm X Z Y) * B = B * (Qi * μ.1.1 * frm X Z Y) := by
    rw [← hg', ← cm, ← cm, e1]
  calc Qi * (g' * μ * g'⁻¹).1.1 * frm X Z Y
      = (Qi * (g' * μ * g'⁻¹).1.1 * frm X Z Y) * B * (Qi * (g'⁻¹).1.1 * frm X Z Y) := by
        rw [Matrix.mul_assoc _ B, e3, Matrix.mul_one]
    _ = bd (lev m S) (Qi * δ.1.1 * frm X Z Y) * B * (Qi * (g'⁻¹).1.1 * frm X Z Y) := by
        rw [e2, rel2]
    _ = _ := by rw [Matrix.mul_assoc, e3, Matrix.mul_one]

end Levi

section Arch

variable {σ : E →ₐ[F] E} {n r m : ℕ} {J : Matrix (Fin n) (Fin n) E} {X Y : Matrix (Fin n) (Fin r) E}
  {Z : Matrix (Fin n) (Fin m) E} {Qi : Matrix (Idx r m) (Fin n) E}

omit [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] in

theorem norm_matrix_triple_product_le {a b c d : Type} [Fintype b] [Fintype c] (A : Matrix a b ℂ) (M : Matrix b c ℂ)
    (B : Matrix c d ℂ) {α μ β : ℝ} (hA : ∀ i j, ‖A i j‖ ≤ α) (hM : ∀ i j, ‖M i j‖ ≤ μ) (hB : ∀ i j, ‖B i j‖ ≤ β)
    (i : a) (j : d) : ‖(A * M * B) i j‖ ≤ Fintype.card b * Fintype.card c * (α * μ * β) :=
  _root_.UpperTheory.Reformulated.B.Yla6.main A M B hA hM hB i j

omit [Field F] [NumberField F] [Algebra F E] in

theorem entry_le_sum {a b : Type} [Fintype a] [Fintype b] (M : Matrix a b E) (φ : E →+* ℂ) (i : a) (j : b) :
    ‖φ (M i j)‖ ≤ ∑ ψ : E →+* ℂ, ∑ u, ∑ v, ‖ψ (M u v)‖ :=
  ((Finset.single_le_sum (f := fun v => ‖φ (M i v)‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ j)).trans
    (Finset.single_le_sum (f := fun u => ∑ v, ‖φ (M u v)‖) (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _)
      (Finset.mem_univ i))).trans
    (Finset.single_le_sum (f := fun ψ : E →+* ℂ => ∑ u, ∑ v, ‖ψ (M u v)‖)
      (fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ φ))

theorem block_diagonal_bound_weighted : ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (b : ι → ℤ) (P P' M : Matrix ι ι ℂ) (w : ι → ℝ) (B R : ℝ), (∀ u, 0 < w u) → P * P' = 1 → P.BlockTriangular b → (P * diagonal (fun u => (w u : ℂ)) * M * diagonal (fun u => (((w u)⁻¹ : ℝ) : ℂ)) * P').BlockTriangular b → (∀ u v, ‖P u v‖ ≤ B) → (∀ u v, ‖P' u v‖ ≤ B) → (∀ u v, ‖M u v‖ ≤ B) → (∀ u v, b u = b v → w u ≤ R * w v) → ∀ u v, ‖bd b (P * diagonal (fun u => (w u : ℂ)) * M * diagonal (fun u => (((w u)⁻¹ : ℝ) : ℂ)) * P') u v‖ ≤ (Fintype.card ι : ℝ) ^ 2 * B ^ 3 * R := by
  intro ι _ _ b P P' M w B R hw hPP hP hN hBP hBP' hBM hR u v
  set T := diagonal (fun u => (w u : ℂ)) * M * diagonal (fun u => (((w u)⁻¹ : ℝ) : ℂ)) with hTd
  have hdet : IsUnit P.det := Matrix.isUnit_det_of_right_inverse hPP
  have hinv : P⁻¹ = P' := Matrix.inv_eq_right_inv hPP
  have hP'P : P' * P = 1 := by rw [← hinv]; exact Matrix.nonsing_inv_mul P hdet
  have hP' : P'.BlockTriangular b := by
    haveI := P.invertibleOfIsUnitDet hdet
    rw [← hinv]
    exact Matrix.blockTriangular_inv_of_blockTriangular hP
  have e : P * diagonal (fun u => (w u : ℂ)) * M * diagonal (fun u => (((w u)⁻¹ : ℝ) : ℂ)) * P' = P * T * P' := by
    simp only [hTd, Matrix.mul_assoc]
  rw [e] at hN ⊢
  have hT : T.BlockTriangular b := by
    have e2 : T = P' * (P * T * P') * P := by
      calc T = (P' * P) * T * (P' * P) := by rw [hP'P, Matrix.one_mul, Matrix.mul_one]
        _ = _ := by simp only [Matrix.mul_assoc]
    rw [e2]
    exact (hP'.mul hN).mul hP
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hBM u u)
  have hR0 : 0 ≤ R := by
    have h1 := hR u u rfl
    by_contra hneg
    push_neg at hneg
    nlinarith [hw u]
  rw [bd_mul (hP.mul hT) hP', bd_mul hP hT]
  have hbP : ∀ x y, ‖bd b P x y‖ ≤ B := fun x y => by
    simp only [bd, Matrix.of_apply]
    split_ifs
    · exact hBP x y
    · simpa using hB0
  have hbP' : ∀ x y, ‖bd b P' x y‖ ≤ B := fun x y => by
    simp only [bd, Matrix.of_apply]
    split_ifs
    · exact hBP' x y
    · simpa using hB0
  have hbT : ∀ x y, ‖bd b T x y‖ ≤ B * R := fun x y => by
    simp only [bd, Matrix.of_apply]
    split_ifs with hxy
    · have eT : T x y = (w x : ℂ) * M x y * (((w y)⁻¹ : ℝ) : ℂ) := by
        simp only [hTd, Matrix.mul_diagonal, Matrix.diagonal_mul]
      rw [eT, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg (hw x).le,
        Real.norm_of_nonneg (inv_nonneg.2 (hw y).le)]
      have h1 := hR x y hxy
      have hwy := hw y
      calc w x * ‖M x y‖ * (w y)⁻¹ ≤ (R * w y) * B * (w y)⁻¹ :=
            mul_le_mul_of_nonneg_right (mul_le_mul h1 (hBM x y) (norm_nonneg _) ((hw x).le.trans h1))
              (inv_nonneg.2 hwy.le)
        _ = B * R := by field_simp
    · simpa using mul_nonneg hB0 hR0
  have := norm_matrix_triple_product_le (bd b P) (bd b T) (bd b P') hbP hbT hbP' u v
  refine this.trans (le_of_eq ?_)
  ring

theorem parabolic_triangular_frame : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n r m : ℕ) (J : Matrix (Fin n) (Fin n) E) (X Y : Matrix (Fin n) (Fin r) E) (Z : Matrix (Fin n) (Fin m) E) (Qi : Matrix (Idx r m) (Fin n) E), IsHermND σ J → IsWittFrame σ J X Y → cT (σ : E →+* E) X * J * Z = 0 → cT (σ : E →+* E) Y * J * Z = 0 → Qi * frm X Z Y = 1 → frm X Z Y * Qi = 1 → ∀ p ∈ minParOne σ J X, ∀ (w : InfinitePlace F) (τ : EmbOver E w) (S : Finset (Fin r)), (Qi.map τ.1 * archMat σ J τ (projArch σ J w p) * (frm X Z Y).map τ.1).BlockTriangular (lev m S) := by
  intro F E _ _ _ _ _ σ h n r m J X Y Z Qi hJ hW xz yz hl hr p hp w τ S
  have cTm : ∀ {a b : ℕ} (A : Matrix (Fin a) (Fin b) E),
      cT (starRingEnd ℂ) (A.map τ.1) = (cT (σ : E →+* E) A).map τ.1 :=
    fun A => Matrix.ext fun i j => (h.2.2.2 τ.1 (A j i)).symm
  have rel : ∀ {a b : ℕ} (A : Matrix (Fin n) (Fin a) E) (B : Matrix (Fin n) (Fin b) E) (M : Matrix (Fin a) (Fin b) E),
      cT (σ : E →+* E) A * J * B = M → cT (starRingEnd ℂ) (A.map τ.1) * J.map τ.1 * B.map τ.1 = M.map τ.1 :=
    fun A B M e => by rw [cTm, ← Matrix.map_mul, ← Matrix.map_mul, e]
  have hfrm : frm (X.map τ.1) (Z.map τ.1) (Y.map τ.1) = (frm X Z Y).map τ.1 := by
    ext a u
    rcases u with i | k | i <;> rfl
  have one_map : ∀ {ι : Type} [Fintype ι] [DecidableEq ι], ((1 : Matrix ι ι E).map τ.1) = 1 :=
    Matrix.map_one _ (map_zero _) (map_one _)
  have zero_map : ∀ {a b : Type}, ((0 : Matrix a b E).map τ.1) = 0 := Matrix.map_zero _ (map_zero _)
  have hJc : cT (starRingEnd ℂ) (J.map τ.1) = J.map τ.1 := by
    rw [cTm]; exact congrArg (Matrix.map · τ.1) (Matrix.ext fun i j => hJ.1 _ _)
  have hl' : Qi.map τ.1 * frm (X.map τ.1) (Z.map τ.1) (Y.map τ.1) = 1 := by
    rw [hfrm, ← Matrix.map_mul, hl, one_map]
  have hr' : frm (X.map τ.1) (Z.map τ.1) (Y.map τ.1) * Qi.map τ.1 = 1 := by
    rw [hfrm, ← Matrix.map_mul, hr, one_map]
  have t := GlobalTheory.T.frame_stabilizer_flag_criterion ℂ (starRingEnd ℂ) (fun x => star_star x) n r m (J.map τ.1) (X.map τ.1) (Y.map τ.1)
    (Z.map τ.1) (Qi.map τ.1) hJc ((rel X X 0 hW.xx).trans zero_map) ((rel Y Y 0 hW.yy).trans zero_map)
    ((rel X Y 1 hW.xy).trans one_map) ((rel X Z 0 xz).trans zero_map) ((rel Y Z 0 yz).trans zero_map) hl' hr' S
    (archMat σ J τ (projArch σ J w p)) ((Group.isUnit (projArch σ J w p)).map (archMat σ J τ))
    (GlobalTheory.T.archimedean_matrix_preserves_form F E σ h n J p w τ) (fun j _ => GlobalTheory.T.minimal_parabolic_archimedean_stabilizes F E σ h n r J X p hp w τ j)
  rwa [hfrm] at t

theorem arch_bound (h : IsCMExt F E σ) (hJ : IsHermND σ J) (hW : IsWittFrame σ J X Y)
    (xz : cT (σ : E →+* E) X * J * Z = 0) (yz : cT (σ : E →+* E) Y * J * Z = 0)
    (hl : Qi * frm X Z Y = 1) (hr : frm X Z Y * Qi = 1) {Ω C₁ : Set (GAd σ J)} (hΩ : IsCompact Ω)
    (hΩP : Ω ⊆ minParOne σ J X) (hC₁ : IsCompact C₁) (R : ℝ) :
    ∃ B : ℝ, ∀ p ∈ Ω, ∀ t : Fin r → ℝ, (∀ i, 0 < t i) → ∀ a, IsTorusElt σ J X Y t a → ∀ y ∈ C₁,
      ∀ S : Finset (Fin r), (∀ u v, lev m S u = lev m S v → wt m t u ≤ R * wt m t v) →
      ∀ δ : GRat σ J, ratEmb σ J δ = p * a * y * a⁻¹ * p⁻¹ → (∀ j ∈ S, StabUpTo X δ.1.1 j) →
      ∀ (w : InfinitePlace F) (τ : EmbOver E w) (u v : Idx r m),
        ‖τ.1 (bd (lev m S) (Qi * δ.1.1 * frm X Z Y) u v)‖ ≤ B := by
  obtain ⟨Bp, -, hBp⟩ := GlobalTheory.T.compact_archimedean_entries_bounded F E σ n J Ω hΩ
  obtain ⟨Bpi, -, hBpi⟩ := GlobalTheory.T.compact_archimedean_entries_bounded F E σ n J (Inv.inv '' Ω) (hΩ.image continuous_inv)
  obtain ⟨By, -, hBy⟩ := GlobalTheory.T.compact_archimedean_entries_bounded F E σ n J C₁ hC₁
  have hs : ∀ x, (σ : E →+* E) ((σ : E →+* E) x) = x := sigma_sigma h
  have hJ' : cT (σ : E →+* E) J = J := Matrix.ext fun i j => hJ.1 _ _
  set q1 := ∑ ψ : E →+* ℂ, ∑ u, ∑ v, ‖ψ (Qi u v)‖ with hq1
  set q2 := ∑ ψ : E →+* ℂ, ∑ u, ∑ v, ‖ψ (frm X Z Y u v)‖ with hq2
  have q1n : 0 ≤ q1 := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _
  have q2n : 0 ≤ q2 := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _
  set b0 := (n : ℝ) * n * (q1 * max Bp (max Bpi By) * q2) with hb0
  refine ⟨(Fintype.card (Idx r m) : ℝ) ^ 2 * b0 ^ 3 * R, ?_⟩
  intro p hp t ht a ha y hy S hR δ hδ hst w τ u v
  set φ : E →+* ℂ := τ.1 with hφ
  set Qc := (frm X Z Y).map φ with hQc
  set Qic := Qi.map φ with hQic
  have hlc : Qic * Qc = 1 := by rw [hQic, hQc, ← Matrix.map_mul, hl, Matrix.map_one _ (map_zero φ) (map_one φ)]
  have hrc : Qc * Qic = 1 := by rw [hQic, hQc, ← Matrix.map_mul, hr, Matrix.map_one _ (map_zero φ) (map_one φ)]
  set am : GAd σ J → Matrix (Fin n) (Fin n) ℂ := fun g => archMat σ J τ (projArch σ J w g) with ham
  have amul : ∀ g g', am (g * g') = am g * am g' := fun g g' => by simp only [ham, map_mul]
  have aone : am 1 = 1 := by simp only [ham, map_one]
  have ainv : ∀ g, am g * am g⁻¹ = 1 := fun g => by rw [← amul, mul_inv_cancel, aone]
  have ainv' : ∀ g, am g⁻¹ * am g = 1 := fun g => by rw [← amul, inv_mul_cancel, aone]
  set cd : Matrix (Fin n) (Fin n) ℂ → Matrix (Idx r m) (Idx r m) ℂ := fun M => Qic * M * Qc with hcd
  have cmul : ∀ M M', cd (M * M') = cd M * cd M' := fun M M' => by
    simp only [hcd]
    calc Qic * (M * M') * Qc = Qic * (M * (Qc * Qic) * M') * Qc := by rw [hrc, Matrix.mul_one]
      _ = _ := by simp only [Matrix.mul_assoc]
  have cone' : cd 1 = 1 := by simp only [hcd, Matrix.mul_one, hlc]
  have hD : (Qi * δ.1.1 * frm X Z Y).map φ = cd (am p) * cd (am a) * cd (am y) * cd (am a⁻¹) * cd (am p⁻¹) := by
    have e : δ.1.1.map φ = am (ratEmb σ J δ) := (GlobalTheory.T.archimedean_rational_embedding_map F E σ n J δ w τ).symm
    rw [Matrix.map_mul, Matrix.map_mul, e, hδ, amul, amul, amul, amul, ← hQic, ← hQc]
    change cd _ = _
    rw [cmul, cmul, cmul, cmul]
  have htor : am a * Qc = Qc * diagonal (fun u => ((wt m t u : ℝ) : ℂ)) := GlobalTheory.T.torus_archimedean_frame_conjugation F E σ n r m J X Y Z xz yz t a ha w τ
  have wpos : ∀ u, 0 < wt m t u := fun u => by rcases u with i | k | i <;> simp [wt, ht]
  have dd : diagonal (fun u => ((wt m t u : ℝ) : ℂ)) * diagonal (fun u => (((wt m t u)⁻¹ : ℝ) : ℂ)) = 1 := by
    rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext u
    rw [← Complex.ofReal_mul, mul_inv_cancel₀ (wpos u).ne', Complex.ofReal_one]
  have ca : cd (am a) = diagonal (fun u => ((wt m t u : ℝ) : ℂ)) := by
    simp only [hcd]; rw [Matrix.mul_assoc, htor, ← Matrix.mul_assoc, hlc, Matrix.one_mul]
  have cai : cd (am a⁻¹) = diagonal (fun u => (((wt m t u)⁻¹ : ℝ) : ℂ)) := by
    have e : cd (am a⁻¹) * cd (am a) = 1 := by rw [← cmul, ainv', cone']
    calc cd (am a⁻¹) = cd (am a⁻¹) * (diagonal (fun u => ((wt m t u : ℝ) : ℂ)) * diagonal (fun u => (((wt m t u)⁻¹ : ℝ) : ℂ))) := by
          rw [dd, Matrix.mul_one]
      _ = _ := by rw [← Matrix.mul_assoc, ← ca, e, Matrix.one_mul]
  rw [ca, cai] at hD
  have bM : ∀ (g : GAd σ J) (β : ℝ), (∀ i j, ‖am g i j‖ ≤ β) → β ≤ max Bp (max Bpi By) → ∀ i j, ‖cd (am g) i j‖ ≤ b0 :=
    fun g β hg hβ i j => by
      have := norm_matrix_triple_product_le Qic (am g) Qc (fun i j => entry_le_sum Qi φ i j) hg (fun i j => entry_le_sum (frm X Z Y) φ i j) i j
      simp only [Fintype.card_fin] at this
      refine this.trans ?_
      rw [hb0]
      gcongr
  have b1 := bM p Bp (fun i j => hBp p hp w τ i j) (le_max_left _ _)
  have b2 := bM p⁻¹ Bpi (fun i j => hBpi p⁻¹ ⟨p, hp, rfl⟩ w τ i j) ((le_max_left _ _).trans (le_max_right _ _))
  have b3 := bM y By (fun i j => hBy y hy w τ i j) ((le_max_right _ _).trans (le_max_right _ _))
  have tP := parabolic_triangular_frame F E σ h n r m J X Y Z Qi hJ hW xz yz hl hr p (hΩP hp) w τ S
  have tN : ((Qi * δ.1.1 * frm X Z Y).map φ).BlockTriangular (lev m S) := by
    have t0 := GlobalTheory.T.frame_stabilizer_flag_criterion E (σ : E →+* E) hs n r m J X Y Z Qi hJ' hW.xx hW.yy hW.xy xz yz hl hr S δ.1.1
      δ.1.isUnit δ.2 hst
    intro i j hij
    simp only [Matrix.map_apply, t0 hij, map_zero]
  have hPP : cd (am p) * cd (am p⁻¹) = 1 := by rw [← cmul, ainv, cone']
  rw [hD] at tN
  have := block_diagonal_bound_weighted (lev m S) (cd (am p)) (cd (am p⁻¹)) (cd (am y)) (wt m t) b0 R wpos hPP tP tN b1 b2 b3 hR u v
  rw [← hD, ← bd_map _ _ (map_zero φ)] at this
  exact this

end Arch

section Classes

variable {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E}

omit [NumberField F] [NumberField E] in

theorem isRegSS_of_isConj {γ δ : GRat σ J} (hc : IsConj γ δ) (hγ : GlobalTheory.Orb.IsRegSS γ.1.1) :
    GlobalTheory.Orb.IsRegSS δ.1.1 := by
  obtain ⟨c, rfl⟩ := isConj_iff.1 hc
  have e : (c * γ * c⁻¹).1.1 = (c.1 : GL (Fin n) E).1 * γ.1.1 * ((c.1)⁻¹ : GL (Fin n) E).1 := rfl
  unfold GlobalTheory.Orb.IsRegSS at *
  rw [e, Matrix.coe_units_inv, Matrix.charpoly_units_conj]
  exact hγ

theorem classes_finite (hS : PositivityTheory.ThKR.SiegelCore) (h : IsCMExt F E σ) (hJ : IsHermND σ J) {C : Set (GAd σ J)}
    (hC : IsCompact C) :
    {𝔬 : Set (GRat σ J) | (∃ γ : GRat σ J, GlobalTheory.Orb.IsRegSS γ.1.1 ∧ 𝔬 = {δ | IsConj γ δ}) ∧
      ∃ (x : GAd σ J) (δ : GRat σ J), δ ∈ 𝔬 ∧ x⁻¹ * ratEmb σ J δ * x ∈ C}.Finite := by
  classical
  obtain ⟨r, X, Y, hW⟩ := exists_isWittFrame h hJ
  obtain ⟨m, Z, Qi, xz, yz, hl, hr⟩ := GlobalTheory.T.exists_witt_complement_frame F E σ h n J hJ r X Y hW
  obtain ⟨K, Ω, c, hK, hΩ, hΩP, hc, -, -, hcov, -, -, -⟩ := hS F E σ h n J hJ r X Y hW
  have hcont : Continuous fun q : GAd σ J × GAd σ J => q.1 * q.2 * q.1⁻¹ :=
    (continuous_fst.mul continuous_snd).mul continuous_fst.inv
  set C₁ : Set (GAd σ J) := (fun q : GAd σ J × GAd σ J => q.1 * q.2 * q.1⁻¹) '' ((K : Set (GAd σ J)) ×ˢ C) with hC₁d
  have hC₁ : IsCompact C₁ := (hK.prod hC).image hcont
  obtain ⟨t0, ht0⟩ := GlobalTheory.T.siegel_compact_translate_bound F E σ h n J hJ r X Y hW Ω hΩ hΩP K hK c hc C hC
  obtain ⟨R, -, hR⟩ := GlobalTheory.T.deep_cone_weight_ratio_bound r m c (max t0 1) hc (le_max_right _ _)
  obtain ⟨B, hB⟩ := arch_bound (Z := Z) h hJ hW xz yz hl hr hΩ hΩP hC₁ R
  set 𝒞 : Set (GFin σ J) := projFin σ J '' ((fun q : GAd σ J × GAd σ J => q.1 * q.2 * q.1⁻¹) '' (Ω ×ˢ C₁)) with h𝒞d
  have h𝒞 : IsCompact 𝒞 := ((hΩ.prod hC₁).image hcont).image (continuous_projFin σ J)
  obtain ⟨dd, hdd, hint⟩ := GlobalTheory.T.compact_finite_rational_denominator F E σ n J 𝒞 h𝒞 Qi (frm X Z Y)
  have hfin := GlobalTheory.T.bounded_integral_matrices_finite F E h.1 (ι := Idx r m) dd B hdd
  have recon : ∀ M : Matrix (Fin n) (Fin n) E, frm X Z Y * (Qi * M * frm X Z Y) * Qi = M := fun M => by
    calc frm X Z Y * (Qi * M * frm X Z Y) * Qi = (frm X Z Y * Qi) * M * (frm X Z Y * Qi) := by simp only [Matrix.mul_assoc]
      _ = M := by rw [hr, Matrix.one_mul, Matrix.mul_one]
  have hinj : Set.InjOn (fun δ : GRat σ J => Qi * δ.1.1 * frm X Z Y) ((fun δ : GRat σ J => Qi * δ.1.1 * frm X Z Y) ⁻¹'
      {N : Matrix (Idx r m) (Idx r m) E | (∀ u v, IsIntegral ℤ ((dd : E) * N u v)) ∧
        ∀ (w : InfinitePlace F) (τ : EmbOver E w) (u v : Idx r m), ‖τ.1 (N u v)‖ ≤ B}) := by
    intro δ _ δ' _ e
    have e' : δ.1.1 = δ'.1.1 := by rw [← recon δ.1.1, ← recon δ'.1.1]; exact congrArg (fun M => frm X Z Y * M * Qi) e
    exact Subtype.ext (Units.ext e')
  refine ((hfin.preimage hinj).image fun δ' => {δ | IsConj δ' δ}).subset ?_
  rintro 𝔬 ⟨⟨γ, hγ, rfl⟩, x, δ, hδ, hx⟩
  obtain ⟨η, hη, s, hs, rfl⟩ := hcov x
  obtain ⟨η', rfl⟩ := GlobalTheory.T.rational_points_eq_embedding F E σ n J η hη
  obtain ⟨p, hp, t, ht, a, ha, k, hk, rfl⟩ := hs
  obtain ⟨δ₁, hδ₁d⟩ : ∃ δ₁ : GRat σ J, δ₁ = η'⁻¹ * δ * η' := ⟨_, rfl⟩
  have hδ₁ : (p * a * k)⁻¹ * ratEmb σ J δ₁ * (p * a * k) ∈ C := by
    convert hx using 1
    rw [hδ₁d, map_mul, map_mul, map_inv]
    group
  have hst : ∀ j ∈ deep (max t0 1) t, StabUpTo X δ₁.1.1 j := by
    intro j hj
    simp only [deep, Finset.mem_filter, Finset.mem_univ, true_and] at hj
    exact ht0 p hp t ht a ha k hk δ₁ hδ₁ j (lt_of_le_of_lt (le_max_left _ _) hj.1)
      (fun j' e => lt_of_le_of_lt (mul_le_mul_of_nonneg_right (le_max_left _ _) (ht.1 j').le) (hj.2 j' e))
  have c1 : IsConj γ δ₁ := (show IsConj γ δ from hδ).trans (isConj_iff.2 ⟨η'⁻¹, by rw [hδ₁d, inv_inv]⟩)
  obtain ⟨δ', hc', hδ'⟩ := exists_conj_levi h hJ hW xz yz hl hr (deep (max t0 1) t) δ₁ (isRegSS_of_isConj c1 hγ) hst
  set δ₀ := (p * a * k)⁻¹ * ratEmb σ J δ₁ * (p * a * k) with hδ₀
  have hy : k * δ₀ * k⁻¹ ∈ C₁ := ⟨(k, δ₀), ⟨hk, hδ₁⟩, rfl⟩
  have hid : ratEmb σ J δ₁ = p * a * (k * δ₀ * k⁻¹) * a⁻¹ * p⁻¹ := by rw [hδ₀]; group
  have hpa : projFin σ J a = 1 := mem_infPts.1 ha.1
  have hf𝒞 : projFin σ J (ratEmb σ J δ₁) ∈ 𝒞 := ⟨p * (k * δ₀ * k⁻¹) * p⁻¹, ⟨(p, k * δ₀ * k⁻¹), ⟨hp, hy⟩, rfl⟩, by
    rw [hid]; simp only [map_mul, map_inv, hpa, mul_one, inv_one]⟩
  refine ⟨δ', ⟨fun u v => ?_, fun w τ u v => ?_⟩, ?_⟩
  · simp only [hδ', bd, Matrix.of_apply]
    split_ifs
    · exact hint δ₁ hf𝒞 u v
    · rw [mul_zero]; exact isIntegral_zero
  · simp only
    rw [hδ']
    exact hB p hp t ht.1 a ha _ hy _ (hR t ht) δ₁ hid hst w τ u v
  · have c2 : IsConj γ δ' := c1.trans hc'
    ext z
    exact ⟨fun hz => c2.trans hz, fun hz => c2.symm.trans hz⟩

end Classes

theorem regClassFin : PositivityTheory.ThKR.SiegelCore → MainStatements.RegularCuspidalTrace.RegClassFin := by
  intro hS D V f hf
  obtain ⟨h, hJ⟩ := GlobalTheory.Mem.Vol.cmData_isCMExt_and_gram_isHermND _ _ D.sp.cm
  have hc := (GlobalTheory.Orb.continuous_of_mem_ccAd hf).2
  refine (classes_finite hS h (hJ V) hc.isCompact).subset ?_
  rintro 𝔬 ⟨h1, x, δ, hδ, hx⟩
  exact ⟨h1, x, δ, hδ, subset_tsupport f (Function.mem_support.2 hx)⟩

end GlobalTheory.CompanionTheory.CFin
end
