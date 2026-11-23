import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KvFintype
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
open IsDedekindDomain NumberField
open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
open GlobalTheory.CompanionTheory.Jp
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.Jp

section Skew

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {m : ℕ} {J : Matrix (Fin m) (Fin m) E} {v : HeightOneSpectrum (𝓞 F)}

def skewGram (hd : J.det ≠ 0) (τ : E →ₐ[F] Fv F v) : GL (Fin m) (Fv F v) :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (J.map τ) (by
    rw [← AlgHom.mapMatrix_apply, ← AlgHom.map_det]; exact (map_ne_zero τ).2 hd)

theorem map_comp_conj_skew (hs : ∀ i j, σ (J j i) = -J i j) (τ : E →ₐ[F] Fv F v) :
    J.map (τ.comp σ) = -(J.map τ)ᵀ :=
  Matrix.ext fun i j => by
    simp only [Matrix.map_apply, AlgHom.comp_apply, Matrix.neg_apply, Matrix.transpose_apply]
    rw [hs j i, map_neg]

theorem splitPairMat_unitary_skew (h : IsCMExt F E σ) (hs : ∀ i j, σ (J j i) = -J i j) (τ : E →ₐ[F] Fv F v)
    {a b : Matrix (Fin m) (Fin m) (Fv F v)} (e : bᵀ * J.map τ * a = J.map τ) :
    Formalism.UG.cT (sigR _ σ) (splitPairMat h τ a b) * JR (Fv F v) J * splitPairMat h τ a b = JR (Fv F v) J := by
  refine splitMat_ext h τ ?_ ?_
  · rw [map_unitary, splitPairMat_map, splitPairMat_map_comp, JR_map_splitProj, e]
  · rw [map_unitary, comp_conj_conj h, splitPairMat_map, splitPairMat_map_comp, JR_map_splitProj,
      map_comp_conj_skew hs, Matrix.mul_neg, Matrix.neg_mul, neg_inj,
      ← Matrix.transpose_inj, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
      Matrix.transpose_transpose, ← Matrix.mul_assoc, e]

theorem splitHom_injective_skew (h : IsCMExt F E σ) (hd : J.det ≠ 0) (τ : E →ₐ[F] Fv F v) :
    Function.Injective (splitHom σ J τ) := fun g g' e => by
  have c : ∀ x : GLoc σ J v, splitHom σ J (τ.comp σ) x = dualConj (skewGram hd τ) (splitHom σ J τ x) :=
    fun x => eq_dualConj_iff.2 (splitHom_unitary τ x)
  exact matHom_injective _ σ J (Units.ext (splitMat_ext h τ (congrArg Units.val e) (by
    rw [← splitHom_val, ← splitHom_val, c, c, e])))

theorem splitHom_surjective_skew (h : IsCMExt F E σ) (hs : ∀ i j, σ (J j i) = -J i j) (hd : J.det ≠ 0)
    (τ : E →ₐ[F] Fv F v) : Function.Surjective (splitHom σ J τ) := fun x =>
  ⟨(⟨splitPairGL h τ x (dualConj (skewGram hd τ) x),
    splitPairMat_unitary_skew h hs τ ((eq_dualConj_iff (A := skewGram hd τ)).1 rfl)⟩ : HR (Fv F v) σ J),
    Units.ext (splitPairMat_map h τ _ _)⟩

end Skew

theorem blkGL_bijective {R : Type} [CommRing R] (n : ℕ) : Function.Bijective (blkGL (R := R) n) :=
  (Units.mapEquiv (Matrix.reindexAlgEquiv R R (finSumFinEquiv (m := n) (n := n)).symm).toMulEquiv).bijective

theorem Jst_mul_self (D : D7) (n : ℕ) : Jst D n * Jst D n = -1 := by
  have e : (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) D.host.E) *
      Matrix.fromBlocks 0 1 (-1) 0 = -1 := by
    rw [Matrix.fromBlocks_multiply, ← Matrix.fromBlocks_one, Matrix.fromBlocks_neg]
    simp
  have e2 := Matrix.submatrix_mul_equiv
    (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) D.host.E)
    (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) D.host.E)
    (finSumFinEquiv (m := n) (n := n)).symm (finSumFinEquiv (m := n) (n := n)).symm
    (finSumFinEquiv (m := n) (n := n)).symm
  rw [e] at e2
  refine e2.trans (Matrix.ext fun i j => ?_)
  simp [Matrix.one_apply]

theorem Jst_det_ne_zero (D : D7) (n : ℕ) : (Jst D n).det ≠ 0 := by
  have : IsUnit (Jst D n).det :=
    Matrix.isUnit_det_of_left_inverse (B := -Jst D n) (by rw [Matrix.neg_mul, Jst_mul_self, neg_neg])
  exact this.ne_zero

theorem Jst_skew (D : D7) (n : ℕ) (i j : Fin (n + n)) :
    D.sp.cm.sig (Jst D n j i) = -Jst D n i j := by
  have key : ∀ a b : Fin n ⊕ Fin n,
      D.sp.cm.sig ((Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) D.host.E) b a) =
        -(Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) D.host.E) a b := by
    rintro (a | a) (b | b) <;>
      simp only [Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
        Matrix.fromBlocks_apply₂₂, Matrix.zero_apply, Matrix.neg_apply, Matrix.one_apply, map_zero, neg_zero, map_neg]
    · by_cases hab : a = b
      · subst hab; simp
      · simp [hab, Ne.symm hab]
    · by_cases hab : a = b
      · subst hab; simp
      · simp [hab, Ne.symm hab]
  exact key _ _

theorem thU_bijective : ∀ (D : D7) (n : ℕ) (v : Pl D) (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v),
    Function.Bijective (thU D n v τ) := fun D n _ τ =>
  (blkGL_bijective n).comp
    ⟨splitHom_injective_skew (isCMExt_host D) (Jst_det_ne_zero D n) τ,
      splitHom_surjective_skew (isCMExt_host D) (Jst_skew D n) (Jst_det_ne_zero D n) τ⟩

end GlobalTheory.CompanionTheory.Jp

end
