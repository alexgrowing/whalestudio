import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaEqB
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsThetaSubSelf
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityReal
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HypothesesAbsDet
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.EmbeddingXiZeroNeZero
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FinPartIdemMulMemIff

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
noncomputable section

namespace GlobalTheory.SquareAgree.KapOnto

variable {D : D7}

theorem inv_mem (X : HSp D) {d : ℕ} (e : Fin X.rank ≃ Fin d) {J : Matrix (Fin d) (Fin d) D.host.E}
    (hJ : J = D.host.xi0 • reindex e e X.gramᵀ) (x : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.UB J) :
    Units.map (Matrix.reindexAlgEquiv (AE D) (AE D) e.symm).toMonoidHom x.1 ∈
      HR (AF D.host.F) D.sp.cm.sig X.gram := by
  have hx : (x.1.1 : Matrix (Fin d) (Fin d) (AE D))ᵀ * GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM J *
      (x.1.1 : Matrix (Fin d) (Fin d) (AE D)).map (cA D) = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM J := x.2
  show (((x.1.1 : Matrix (Fin d) (Fin d) (AE D)).submatrix e e).map (cA D))ᵀ * GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM X.gram *
    (x.1.1 : Matrix (Fin d) (Fin d) (AE D)).submatrix e e = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM X.gram
  generalize (x.1.1 : Matrix (Fin d) (Fin d) (AE D)) = Y at hx ⊢
  rw [hJ, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM_smul, Matrix.mul_smul, Matrix.smul_mul] at hx
  have hx' := congrArg (fun y => incA D (D.host.xi0)⁻¹ • y) hx
  simp only [smul_smul, ← map_mul, inv_mul_cancel₀ (GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D), map_one, one_smul] at hx'
  have e1 : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM (reindex e e X.gramᵀ) = reindex e e (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM X.gram)ᵀ := rfl
  rw [e1] at hx'
  have hs := congrArg (fun y => y.submatrix e e) hx'
  simp only [reindex_apply] at hs
  rw [← submatrix_mul_equiv _ _ _ e _, ← submatrix_mul_equiv _ _ _ e _] at hs
  simp only [submatrix_submatrix, Equiv.symm_comp_self, submatrix_id_id, ← transpose_submatrix,
    ← Matrix.submatrix_map] at hs
  have ht := congrArg transpose hs
  rw [transpose_mul, transpose_mul, transpose_transpose, transpose_transpose, ← Matrix.mul_assoc] at ht
  exact ht

set_option maxHeartbeats 1600000 in

theorem kapX_onto : ∀ (D : D7) (X : HSp D) {d : ℕ} (e : Fin X.rank ≃ Fin d) (Wd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E d)
    (hJ : Wd.J = D.host.xi0 • reindex e e X.gramᵀ) (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl D.host.F),
    ∀ h ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UAt D.sp.cm.sig Wd (GlobalTheory.AdelicU.evFin D.host.F v), ∃ h' ∈ GfC X, kapX X e hJ h' = h := by
  intro D X d e Wd hJ v h hh
  let h' : GA D X := ⟨Units.map (Matrix.reindexAlgEquiv (AE D) (AE D) e.symm).toMonoidHom h.1, inv_mem X e hJ h⟩
  refine ⟨h', ?_, ?_⟩
  · set a : AF D.host.F := 1 - GlobalTheory.EmbChart.atPlace v 1 with ha
    have h0 : GlobalTheory.AdelicU.evFin D.host.F v a = 0 := by
      rw [ha, map_sub, map_one, GlobalTheory.EmbChart.evFin_atPlace, sub_self]
    have h1 : fstA D.host.F a = 1 := by
      show (1 : Ainf D.host.F) - (0 : Ainf D.host.F) = 1
      exact sub_zero 1
    let f := Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E)
    have hf1 : f (a ⊗ₜ[D.host.F] (1 : D.host.E)) = 1 := by
      simp only [f, Algebra.TensorProduct.map_tmul, AlgHom.coe_id, id_eq, h1]
      rfl
    have hz : ∀ i j, f ((GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat h - 1) i j) = 0 := by
      intro i j
      have k := congrFun (congrFun (hh a h0) i) j
      rw [Matrix.smul_apply, Matrix.zero_apply, Algebra.smul_def, Algebra.TensorProduct.algebraMap_apply,
        Algebra.algebraMap_self, RingHom.id_apply] at k
      have k2 := congrArg f k
      rw [map_mul, map_zero, hf1, one_mul] at k2
      exact k2
    rw [GfC, MonoidHom.mem_ker]
    apply Units.ext
    ext i j
    show f (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat h (e i) (e j)) = (1 : Matrix (Fin X.rank) (Fin X.rank) _) i j
    have e2 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat h (e i) (e j) =
        (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat h - 1) (e i) (e j) + (1 : Matrix (Fin d) (Fin d) (AE D)) (e i) (e j) := by
      rw [Matrix.sub_apply, sub_add_cancel]
    rw [e2, map_add, hz, zero_add]
    by_cases hij : i = j
    · subst hij
      rw [Matrix.one_apply_eq (α := AF D.host.F ⊗[D.host.F] D.host.E), map_one,
        Matrix.one_apply_eq (α := Ainf D.host.F ⊗[D.host.F] D.host.E)]
    · rw [Matrix.one_apply_ne (α := AF D.host.F ⊗[D.host.F] D.host.E) (e.injective.ne hij), map_zero,
        Matrix.one_apply_ne (α := Ainf D.host.F ⊗[D.host.F] D.host.E) hij]
  · apply Subtype.ext
    apply Units.ext
    ext i j
    show (h.1.1 : Matrix (Fin d) (Fin d) (AE D)) (e (e.symm i)) (e (e.symm j)) = h.1.1 i j
    simp only [Equiv.apply_symm_apply]

end GlobalTheory.SquareAgree.KapOnto
