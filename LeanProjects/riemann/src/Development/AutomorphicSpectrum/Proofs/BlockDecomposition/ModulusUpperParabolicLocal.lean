import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KvFintype
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DoublingNormDetSplitPlaceLatticeIntersection

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
open IsDedekindDomain NumberField
open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
open GlobalTheory.CompanionTheory.Jp

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.Jp.UpTri

theorem transpose_block_matrix {A : Type} {n : ℕ} (a b c d : Matrix (Fin n) (Fin n) A) :
    (GlobalTheory.StdUnn.blk4 a b c d)ᵀ = GlobalTheory.StdUnn.blk4 aᵀ cᵀ bᵀ dᵀ := by
  ext i j
  simp only [GlobalTheory.StdUnn.blk4, Matrix.transpose_apply, Matrix.submatrix_apply]
  rcases finSumFinEquiv.symm i with i | i <;> rcases finSumFinEquiv.symm j with j | j <;> rfl

theorem blocks_of_unitary {K : Type} [CommRing K] {n : ℕ} (a : GL (Fin n) K) (b d a' b' c' d' : Matrix (Fin n) (Fin n) K)
    (h : (GlobalTheory.StdUnn.blk4 a' b' c' d')ᵀ * GlobalTheory.StdUnn.blk4 0 1 (-1) 0 * GlobalTheory.StdUnn.blk4 a.1 b 0 d =
      GlobalTheory.StdUnn.blk4 0 1 (-1) 0) : c' = 0 ∧ a'ᵀ * d = 1 := by
  rw [transpose_block_matrix, GlobalTheory.StdUnn.Model.submatrix_fromBlocks_mul, GlobalTheory.StdUnn.Model.submatrix_fromBlocks_mul] at h
  obtain ⟨h1, h2, -, -⟩ := GlobalTheory.StdUnn.Model.blockMatrixTwoByTwoFin_injective h
  have e1 : c'ᵀ * a.1 = 0 := by simpa using h1
  have e2 : c'ᵀ = 0 := by
    have := congrArg (· * (a⁻¹).1) e1
    simpa [Matrix.mul_assoc, -Matrix.coe_units_inv] using this
  have e3 : c' = 0 := by simpa using congrArg Matrix.transpose e2
  subst e3
  exact ⟨rfl, by simpa using h2⟩

section General

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
  {Q : Matrix (Fin (n + n)) (Fin (n + n)) E} {v : HeightOneSpectrum (𝓞 F)}

theorem upperParabolic_height_of_split (h : IsCMExt F E σ) (hQ : Q = GlobalTheory.StdUnn.blk4 0 1 (-1) 0) (τ : E →ₐ[F] Fv F v)
    (y : GLoc σ Q v) (a d : GL (Fin n) (Fv F v)) (b : Matrix (Fin n) (Fin n) (Fv F v))
    (hy : (splitHom σ Q τ y).1 = GlobalTheory.StdUnn.blk4 a.1 b 0 d.1) :
    ∃ hm : y ∈ GlobalTheory.LocIntw.upperParabolic (Fv F v) σ Q,
      absEv F E v (GlobalTheory.LocIntw.aUp (Fv F v) σ Q ⟨y, hm⟩) = ‖a.1.det‖₊ / ‖d.1.det‖₊ := by
  obtain ⟨A, B, C, D', e⟩ := GlobalTheory.LocIntw.exists_blockMatrixTwoByTwoFin_eq (GlobalTheory.LocIntw.matR (Fv F v) σ y)
  have key : ∀ ρ : E →ₐ[F] Fv F v, (splitHom σ Q ρ y).1 =
      GlobalTheory.StdUnn.blk4 (A.map (splitProj ρ)) (B.map (splitProj ρ)) (C.map (splitProj ρ)) (D'.map (splitProj ρ)) := by
    intro ρ
    rw [splitHom_val]
    change (GlobalTheory.LocIntw.matR (Fv F v) σ y).map (splitProj ρ : Fv F v ⊗[F] E →+* Fv F v) = _
    rw [e]
    exact GlobalTheory.LocIntw.blockMatrix_map _ _ _ _ _
  obtain ⟨ha, -, hc, -⟩ := GlobalTheory.StdUnn.Model.blockMatrixTwoByTwoFin_injective ((key τ).symm.trans hy)
  have hQτ : Q.map τ = GlobalTheory.StdUnn.blk4 0 1 (-1) 0 := by
    subst hQ
    have := GlobalTheory.LocIntw.blockMatrix_map (τ : E →+* Fv F v) (0 : Matrix (Fin n) (Fin n) E) 1 (-1) 0
    rw [Matrix.map_zero _ (map_zero _), Matrix.map_neg _ (map_neg _), Matrix.map_one _ (map_zero _) (map_one _)] at this
    exact this
  have u := splitHom_unitary τ y
  rw [key (τ.comp σ), hQτ, hy] at u
  obtain ⟨hc', hd'⟩ := blocks_of_unitary a b d.1 _ _ _ _ u
  have hC : C = 0 := splitMat_ext h τ
    (by rw [hc]; exact (Matrix.map_zero _ (map_zero _)).symm)
    (by rw [hc']; exact (Matrix.map_zero _ (map_zero _)).symm)
  have hm : y ∈ GlobalTheory.LocIntw.upperParabolic (Fv F v) σ Q := (GlobalTheory.LocIntw.mem_siegelParabolic_iff_lowerLeft_eq_zero hQ).2 fun i j => by
    rw [e, hC, GlobalTheory.StdUnn.blk4, Matrix.submatrix_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
    simp
  refine ⟨hm, ?_⟩
  have hA : GlobalTheory.StdUnn.blkA (GlobalTheory.LocIntw.matR (Fv F v) σ y) = A := by rw [e, GlobalTheory.LocIntw.upperLeft_blockMatrix]
  have d1 : splitProj τ A.det = a.1.det := by
    rw [← ha]
    exact RingHom.map_det (splitProj τ : Fv F v ⊗[F] E →+* Fv F v) A
  have d2 : splitProj (τ.comp σ) A.det * d.1.det = 1 := by
    have : splitProj (τ.comp σ) A.det = (A.map (splitProj (τ.comp σ))).det :=
      RingHom.map_det (splitProj (τ.comp σ) : Fv F v ⊗[F] E →+* Fv F v) A
    rw [this, ← Matrix.det_transpose, ← Matrix.det_mul, hd', Matrix.det_one]
  rw [absEv_apply, GlobalTheory.LocIntw.coe_aUp, hA, GlobalTheory.SplitInterDet.norm_eq_split h τ, nnnorm_mul, d1,
    eq_inv_of_mul_eq_one_left d2, nnnorm_inv, div_eq_mul_inv]

end General

theorem upperParabolic_height (D : D7) (n : ℕ) (v : Pl D) (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v)
    (y : GLoc D.sp.cm.sig (Jst D n) v) (a d : GL (Fin n) (Fv D.host.F v))
    (b : Matrix (Fin n) (Fin n) (Fv D.host.F v)) (H : thU D n v τ y = pM a d b) :
    ∃ hy : y ∈ GlobalTheory.LocIntw.upperParabolic (Fv D.host.F v) D.sp.cm.sig (Jst D n),
      absEv D.host.F D.host.E v (GlobalTheory.LocIntw.aUp (Fv D.host.F v) D.sp.cm.sig (Jst D n) ⟨y, hy⟩) =
        nvL D v (Matrix.GeneralLinearGroup.det a) / nvL D v (Matrix.GeneralLinearGroup.det d) := by
  have hy : (splitHom D.sp.cm.sig (Jst D n) τ y).1 = GlobalTheory.StdUnn.blk4 a.1 b 0 d.1 := by
    have e : ((splitHom D.sp.cm.sig (Jst D n) τ y).1).submatrix finSumFinEquiv finSumFinEquiv =
        Matrix.fromBlocks a.1 b 0 d.1 := congrArg Units.val H
    rw [GlobalTheory.StdUnn.blk4, ← e]
    ext i j
    simp
  exact upperParabolic_height_of_split (isCMExt_host D) (GlobalTheory.LocIntw.Jst_eq D n) τ y a d b hy

end GlobalTheory.CompanionTheory.Jp.UpTri

end
