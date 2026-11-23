import Mathlib
import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.CoefDataExists
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CosetCell
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.AdelicConjTransposeBlockMatrixTwoByTwoFin
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SiegelParabolicUnnMatrixBlockUpperTriangular
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.SummableCell
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisensteinCellsDecomposition
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisensteinRationalPoints
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousHalfTr
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS GlobalTheory.Eis GlobalTheory.CompanionTheory.SwUnf
open PositivityTheory.GramSchwartzFunctions.EC GlobalTheory.StdUnn.Model GlobalTheory.StdUnn.LeftInvSect GlobalTheory.CompanionTheory.Hypotheses₂.WeilU

namespace GlobalTheory.CompanionTheory.SwUnf.BigCell

section Field

variable {K : Type} [Field K] {n : ℕ}

theorem cT_mul_sq (σ : K →+* K) (x y : Matrix (Fin n) (Fin n) K) : cT σ (x * y) = cT σ y * cT σ x := by
  unfold cT
  rw [Matrix.map_mul, Matrix.transpose_mul]

theorem cT_one_sq (σ : K →+* K) : cT σ (1 : Matrix (Fin n) (Fin n) K) = 1 := by
  unfold cT
  rw [Matrix.map_one _ (map_zero σ) (map_one σ), Matrix.transpose_one]

theorem cT_blk4 (σ : K →+* K) (a b c d : Matrix (Fin n) (Fin n) K) :
    cT σ (blk4 a b c d) = blk4 (cT σ a) (cT σ c) (cT σ b) (cT σ d) := by
  ext i j
  simp only [cT, blk4, Matrix.transpose_apply, Matrix.map_apply, Matrix.submatrix_apply]
  rcases finSumFinEquiv.symm i with i | i <;> rcases finSumFinEquiv.symm j with j | j <;> rfl

theorem block_identity_eq_one {R : Type} [CommRing R] : blk4 (1 : Matrix (Fin n) (Fin n) R) 0 0 1 = 1 := by
  unfold blk4
  rw [Matrix.fromBlocks_one, Matrix.submatrix_one_equiv]

theorem lowerLeft_block {R : Type} (a b c d : Matrix (Fin n) (Fin n) R) : lowerC (blk4 a b c d) = c := by
  ext i j
  simp [lowerC, blk4]

theorem exists_blockMatrixTwoByTwoFin_eq {R : Type} (M : Matrix (Fin (n + n)) (Fin (n + n)) R) :
    ∃ a b, M = blk4 a b (lowerC M) (GlobalTheory.CompanionTheory.RatPtsUnn.blkD M) := by
  refine ⟨(M.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₁₁,
    (M.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₁₂, ?_⟩
  have h : Matrix.fromBlocks (M.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₁₁
      (M.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₁₂ (lowerC M) (GlobalTheory.CompanionTheory.RatPtsUnn.blkD M) =
      M.submatrix finSumFinEquiv finSumFinEquiv :=
    Matrix.fromBlocks_toBlocks _
  unfold blk4
  rw [h]
  ext i j
  simp

theorem isSiegelParabolic_iff (M : Matrix (Fin (n + n)) (Fin (n + n)) K) : IsSiegelP M ↔ lowerC M = 0 := by
  constructor
  · intro h
    ext i j
    exact h i j
  · intro h i j
    exact congrFun (congrFun h i) j

theorem cellKer_eq_bot_iff' {E : Type} [Field E] (C : Matrix (Fin n) (Fin n) E) :
    LinearMap.ker C.mulVecLin = ⊥ ↔ IsUnit C.det := by
  rw [LinearMap.ker_eq_bot, ← Matrix.isUnit_iff_isUnit_det, ← Matrix.mulVec_injective_iff_isUnit]
  rfl

abbrev cellM (b : Matrix (Fin n) (Fin n) K) : Matrix (Fin (n + n)) (Fin (n + n)) K := blk4 0 1 (-1) (-b)

theorem cellM_mul (b : Matrix (Fin n) (Fin n) K) : cellM b * blk4 (-b) (-1) 1 0 = 1 := by
  rw [cellM, submatrix_fromBlocks_mul]
  simp [block_identity_eq_one]

theorem mul_cellM (b : Matrix (Fin n) (Fin n) K) : blk4 (-b) (-1) 1 0 * cellM b = 1 := by
  rw [cellM, submatrix_fromBlocks_mul]
  simp [block_identity_eq_one]

theorem cellM_det (b : Matrix (Fin n) (Fin n) K) : IsUnit (cellM b).det :=
  Matrix.isUnit_det_of_left_inverse (mul_cellM b)

theorem cellM_inv (b : Matrix (Fin n) (Fin n) K) : (cellM b)⁻¹ = blk4 (-b) (-1) 1 0 :=
  Matrix.inv_eq_right_inv (cellM_mul b)

theorem lower_rel (σ : K →+* K) {A B C Dd : Matrix (Fin n) (Fin n) K}
    (h : IsUnitary σ (blk4 0 1 (-1) 0) (blk4 A B C Dd)) : Dd * cT σ C = C * cT σ Dd := by
  have hJJ : (blk4 0 1 (-1) 0 : Matrix (Fin (n + n)) (Fin (n + n)) K) * blk4 0 (-1) 1 0 = 1 := by
    rw [submatrix_fromBlocks_mul]
    simp [block_identity_eq_one]
  have hJJ' : (blk4 0 (-1) 1 0 : Matrix (Fin (n + n)) (Fin (n + n)) K) * blk4 0 1 (-1) 0 = 1 := by
    rw [submatrix_fromBlocks_mul]
    simp [block_identity_eq_one]
  have h0 : cT σ (blk4 A B C Dd) * blk4 0 1 (-1) 0 * blk4 A B C Dd = blk4 0 1 (-1) 0 := h
  have h1 : (blk4 0 (-1) 1 0 * cT σ (blk4 A B C Dd) * blk4 0 1 (-1) 0) * blk4 A B C Dd = 1 := by
    rw [mul_assoc (blk4 0 (-1) 1 0), mul_assoc (blk4 0 (-1) 1 0), h0, hJJ']
  have h2 := mul_eq_one_comm.1 h1
  have h3 : blk4 A B C Dd * blk4 0 (-1) 1 0 * cT σ (blk4 A B C Dd) = blk4 0 (-1) 1 0 := by
    calc _ = blk4 A B C Dd * (blk4 0 (-1) 1 0 * cT σ (blk4 A B C Dd) * blk4 0 1 (-1) 0) * blk4 0 (-1) 1 0 := by
          simp only [mul_assoc, hJJ, mul_one]
      _ = _ := by rw [h2, one_mul]
  rw [cT_blk4, submatrix_fromBlocks_mul, submatrix_fromBlocks_mul] at h3
  obtain ⟨-, -, -, h4⟩ := blockMatrixTwoByTwoFin_injective h3
  simp only [mul_zero, mul_neg, mul_one, zero_add, add_zero] at h4
  exact sub_eq_zero.1 (by simpa [sub_eq_add_neg, add_comm] using h4)

theorem herm_of_rel (σ : K →+* K) {C Dd : Matrix (Fin n) (Fin n) K} (hC : IsUnit C.det)
    (h : Dd * cT σ C = C * cT σ Dd) : cT σ (C⁻¹ * Dd) = C⁻¹ * Dd := by
  have a1 : C⁻¹ * C = 1 := Matrix.nonsing_inv_mul _ hC
  have b1 : cT σ C * cT σ C⁻¹ = 1 := by rw [← cT_mul_sq, a1, cT_one_sq]
  have b2 : C⁻¹ * Dd * cT σ C = cT σ Dd := by rw [mul_assoc, h, ← mul_assoc, a1, one_mul]
  rw [cT_mul_sq, ← b2, mul_assoc, b1, mul_one]

theorem lower_unit {x : Matrix (Fin (n + n)) (Fin (n + n)) K} (hx : IsUnit x.det) (b : Matrix (Fin n) (Fin n) K)
    (hS : IsSiegelP (x * (cellM b)⁻¹)) : IsUnit (lowerC x).det := by
  rw [cellM_inv] at hS
  set S := x * blk4 (-b) (-1) 1 0 with hSd
  have hSx : S * cellM b = x := by rw [hSd, mul_assoc, mul_cellM, mul_one]
  have hdet : IsUnit S.det := by
    rw [hSd, Matrix.det_mul]
    exact hx.mul (Matrix.isUnit_det_of_left_inverse (cellM_mul b))
  have hd : IsUnit (GlobalTheory.CompanionTheory.RatPtsUnn.blkD S).det := by
    rw [GlobalTheory.CompanionTheory.RatPtsUnn.det_eq_of_lowerLeft_zero S hS] at hdet
    exact isUnit_of_mul_isUnit_right hdet
  obtain ⟨a, c, hb⟩ := exists_blockMatrixTwoByTwoFin_eq S
  have h0 : lowerC S = 0 := (isSiegelParabolic_iff S).1 hS
  rw [h0] at hb
  have e : lowerC x = -GlobalTheory.CompanionTheory.RatPtsUnn.blkD S := by
    rw [← hSx, hb, cellM, submatrix_fromBlocks_mul, lowerLeft_block, ← hb]
    simp
  rw [e, ← Matrix.isUnit_iff_isUnit_det]
  exact ((Matrix.isUnit_iff_isUnit_det _).2 hd).neg

theorem of_lower_unit (σ : K →+* K) {x : Matrix (Fin (n + n)) (Fin (n + n)) K}
    (hu : IsUnitary σ (blk4 0 1 (-1) 0) x) (hC : IsUnit (lowerC x).det) :
    cT σ ((lowerC x)⁻¹ * GlobalTheory.CompanionTheory.RatPtsUnn.blkD x) = (lowerC x)⁻¹ * GlobalTheory.CompanionTheory.RatPtsUnn.blkD x ∧
      IsSiegelP (x * (cellM ((lowerC x)⁻¹ * GlobalTheory.CompanionTheory.RatPtsUnn.blkD x))⁻¹) := by
  obtain ⟨a, b, hb⟩ := exists_blockMatrixTwoByTwoFin_eq x
  have hu' : IsUnitary σ (blk4 0 1 (-1) 0) (blk4 a b (lowerC x) (GlobalTheory.CompanionTheory.RatPtsUnn.blkD x)) := by
    rw [← hb]
    exact hu
  refine ⟨herm_of_rel σ hC (lower_rel σ hu'), ?_⟩
  rw [cellM_inv, isSiegelParabolic_iff]
  have a2 : lowerC x * (lowerC x)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hC
  generalize hl : (lowerC x)⁻¹ * GlobalTheory.CompanionTheory.RatPtsUnn.blkD x = l
  have e : lowerC x * l = GlobalTheory.CompanionTheory.RatPtsUnn.blkD x := by
    rw [← hl, ← mul_assoc, a2, one_mul]
  conv_lhs => rw [hb]
  rw [submatrix_fromBlocks_mul, lowerLeft_block, mul_neg, e]
  simp

end Field

variable {D : D7} {n : ℕ}

theorem ratOf_spec (γ : GF D n) : IsUnit (ratOf γ).det ∧
    IsUnitary (D.sp.cm.sig : D.host.E →+* D.host.E) (blk4 0 1 (-1) 0) (ratOf γ) := by
  obtain ⟨g, hd, hu, hm⟩ := GlobalTheory.CompanionTheory.RatPtsUnn.clause1 γ.1 γ.2
  have e : ratOf γ = g := Matrix.map_injective incA_injective ((mat_ratOf γ).symm.trans hm)
  rw [e]
  exact ⟨hd, hu⟩

theorem mat_cell_rat {w u : G D n} (hw : mat w = blk4 0 1 (-1) 0) (b : Matrix (Fin n) (Fin n) D.host.E)
    (hu : mat u = blk4 1 (b.map (incA D)) 0 1) : mat (w * u) = (cellM b).map (incA D) := by
  rw [mat_cell hw hu, cellM, blk4_map_alt]
  have e0 : (0 : Matrix (Fin n) (Fin n) D.host.E).map (incA D) = 0 := map_zero (incA D).mapMatrix
  have e1 : (1 : Matrix (Fin n) (Fin n) D.host.E).map (incA D) = 1 := map_one (incA D).mapMatrix
  have e2 : (-1 : Matrix (Fin n) (Fin n) D.host.E).map (incA D) = -1 := by
    have := map_neg (incA D).mapMatrix (1 : Matrix (Fin n) (Fin n) D.host.E)
    rwa [map_one] at this
  have e3 : (-b).map (incA D) = -(b.map (incA D)) := map_neg (incA D).mapMatrix b
  rw [e0, e1, e2, e3]

theorem exists_hermQ (l : ratHerm D n) : ∃ b : HermQ D n, b.1.map (incA D) = l.1.1 := by
  have hm : l.1.1 ∈ ratMx D n n := l.2
  obtain ⟨b, hb⟩ := hm
  have hb' : b.map (incA D) = l.1.1 := hb
  have hadj : adj (b.map (incA D) : Mx D n n) = b.map (incA D) := by
    rw [hb']
    exact l.1.2
  refine ⟨⟨b, fun i j => incA_injective ?_⟩, hb'⟩
  exact congrFun (congrFun hadj i) j

theorem bigCell : ∀ {D : D7} {n : ℕ} {w : G D n}, mat w = blk4 0 1 (-1) 0 → ∀ {nb : hermA D n → G D n}, IsNMap nb → ∃ e : ratHerm D n → Cosets (P D n) (GF D n), Function.Injective e ∧ (∀ q, cosetCell q = ⊥ ↔ q ∈ Set.range e) ∧ ∀ f : G D n → ℂ, LeftInv (P D n ⊓ GF D n) f → ∀ (l : ratHerm D n) (y : G D n), term (P D n) (GF D n) f y (e l) = f (w * nb l.1 * y) := by
  intro D n w hw nb hnb
  choose β hβ using exists_hermQ (D := D) (n := n)
  have hu : ∀ l, mat (nb l.1) = blk4 1 ((β l).1.map (incA D)) 0 1 := fun l => by
    rw [hβ]
    exact hnb l.1
  let c : ratHerm D n → GF D n := fun l => ⟨w * nb l.1, cell_mem_GF hw (β l) (hu l)⟩
  have hc : ∀ l, mat (c l).1 = (cellM (β l).1).map (incA D) := fun l => mat_cell_rat hw _ (hu l)
  refine ⟨fun l => mk ((P D n).subgroupOf (GF D n)) (c l), ?_, ?_, ?_⟩
  · intro l l' h
    obtain ⟨δ, hδ⟩ := mk_eq_iff.1 h
    have hP : (w * nb l'.1) * (w * nb l.1)⁻¹ ∈ P D n := by
      have e : (w * nb l'.1) * (w * nb l.1)⁻¹ = δ.1.1 := by
        have := congrArg Subtype.val hδ
        change δ.1.1 * (w * nb l.1) = w * nb l'.1 at this
        rw [← this]
        exact mul_inv_cancel_right _ _
      rw [e]
      exact Subgroup.mem_subgroupOf.1 δ.2
    have hbb := cell_inj hw (hu l) (hu l') hP
    apply Subtype.ext
    apply Subtype.ext
    rw [← hβ l, ← hβ l', hbb]
  · intro q
    have hspec := ratOf_spec (Quotient.out q)
    have hker : cosetCell q = ⊥ ↔ IsUnit (lowerC (ratOf (Quotient.out q))).det :=
      cellKer_eq_bot_iff' _
    rw [hker]
    constructor
    · intro hC
      obtain ⟨hh, hS⟩ := of_lower_unit _ hspec.2 hC
      set lam := (lowerC (ratOf (Quotient.out q)))⁻¹ * GlobalTheory.CompanionTheory.RatPtsUnn.blkD (ratOf (Quotient.out q)) with hlam
      let b : HermQ D n := ⟨lam, fun i j => congrFun (congrFun hh i) j⟩
      let l : ratHerm D n := ⟨⟨lam.map (incA D), adj_map_herm b⟩, ⟨lam, rfl⟩⟩
      have hbl : (β l).1 = lam := Matrix.map_injective incA_injective (hβ l)
      refine ⟨l, ?_⟩
      have hmk := (GlobalTheory.CompanionTheory.EisCellsAsm.mk_eq_iff_siegel GlobalTheory.CompanionTheory.RatPtsUnn.ratPtsUnn (c l) (Quotient.out q)
        (cellM_det _) (hc l) (mat_ratOf _)).2 (by rw [hbl]; exact hS)
      exact hmk.trans (Quotient.out_eq q)
    · rintro ⟨l, rfl⟩
      have hmk : mk ((P D n).subgroupOf (GF D n)) (c l) =
          mk ((P D n).subgroupOf (GF D n)) (Quotient.out (mk ((P D n).subgroupOf (GF D n)) (c l))) :=
        (Quotient.out_eq _).symm
      exact lower_unit hspec.1 _ ((GlobalTheory.CompanionTheory.EisCellsAsm.mk_eq_iff_siegel GlobalTheory.CompanionTheory.RatPtsUnn.ratPtsUnn (c l) _
        (cellM_det _) (hc l) (mat_ratOf _)).1 hmk)
  · intro f hf l y
    exact term_mk hf y (c l)

end GlobalTheory.CompanionTheory.SwUnf.BigCell
