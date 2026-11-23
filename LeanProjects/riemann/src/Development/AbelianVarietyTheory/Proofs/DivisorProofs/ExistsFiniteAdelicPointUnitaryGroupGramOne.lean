import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFinPt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DefiniteUnitaryClassSetFinite
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicUnitaryEqRealMulFiniteSplit
import Formalism.SharpRestriction.GlobalSchurBounds.Joints
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
open scoped TensorProduct
namespace GlobalTheory.BotFormula

theorem toFinE_sgA (D : D7) (y : Formalism.MainNotions.StandardLatticesGL3.AE D) :
    toFinE D (Formalism.MainNotions.StandardLatticesGL3.sgA D y) = GlobalTheory.CuspRep.conjFin (D.host.conj : D.host.E ≃+* D.host.E) (toFinE D y) := by
  induction y using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add a b ha hb => simp only [map_add, ha, hb]
  | tmul x a =>
    change GlobalTheory.LFun.toFinAd ℚ D.host.E (a ⊗ₜ[ℚ] D.host.conj x) =
      GlobalTheory.CuspRep.conjFin _ (GlobalTheory.LFun.toFinAd ℚ D.host.E (a ⊗ₜ[ℚ] x))
    rw [GlobalTheory.LFun.toFinAd_tmul, GlobalTheory.LFun.toFinAd_tmul, map_mul,
      GlobalTheory.DefU.ClassFin.conjFin_adMap _ (fun q => D.host.conj.commutes q), GlobalTheory.CuspRep.conjFin_algebraMap]
    rfl

def toAfE (D : D7) : Formalism.MainNotions.StandardLatticesGL3.AE D ≃+* TensorProduct D.host.F (Af D.host.F) D.host.E :=
  (toFinE D).trans (GlobalTheory.LFun.finAdEquiv D.host.F D.host.E).symm

theorem toAfE_sgA (D : D7) (y : Formalism.MainNotions.StandardLatticesGL3.AE D) :
    toAfE D (Formalism.MainNotions.StandardLatticesGL3.sgA D y) = sigR (Af D.host.F) D.sp.cm.sig (toAfE D y) := by
  apply (GlobalTheory.LFun.finAdEquiv D.host.F D.host.E).injective
  rw [GlobalTheory.DefU.ClassFin.finAdEquiv_sigR D.sp.cm.sig (D.host.conj : D.host.E ≃+* D.host.E)
    (fun x => Formalism.MainNotions.GlobalTheoryTheory.jnt_sig_eq_conj D x)]
  simp only [toAfE, RingEquiv.trans_apply, RingEquiv.apply_symm_apply]
  exact toFinE_sgA D y

theorem exists_isFinPt_of_gram_one : ∀ {D : D7} (WW : HSp D), WW.gram = 1 → ∀ {n : ℕ} (h : GA D n), WW.rank = n →
    ∃ g : GA D WW, GlobalTheory.BotFormula.IsFinPt WW g h := by
  intro D WW hG n h hr
  subst hr
  let x' : GL (Fin WW.rank) (TensorProduct D.host.F (Af D.host.F) D.host.E) := Formalism.UG.bc (toAfE D).toRingHom h.1
  have hh : Formalism.UG.cT (Formalism.MainNotions.StandardLatticesGL3.sgA D) (h.1 : Matrix (Fin WW.rank) (Fin WW.rank) (Formalism.MainNotions.StandardLatticesGL3.AE D)) * h.1 = 1 := by
    have h2 := h.2
    change Formalism.UG.cT _ (h.1 : Matrix (Fin WW.rank) (Fin WW.rank) (Formalism.MainNotions.StandardLatticesGL3.AE D)) * _ * _ = _ at h2
    rw [Matrix.map_one _ (map_zero _) (map_one _), mul_one] at h2
    exact h2
  have hx' : x' ∈ HR (Af D.host.F) D.sp.cm.sig WW.gram := by
    show Formalism.UG.cT (sigR (Af D.host.F) D.sp.cm.sig) (x' : Matrix (Fin WW.rank) (Fin WW.rank) _) *
      JR (Af D.host.F) WW.gram * (x' : Matrix (Fin WW.rank) (Fin WW.rank) _) = JR (Af D.host.F) WW.gram
    rw [hG, JR, Matrix.map_one _ (map_zero _) (map_one _), mul_one]
    exact GlobalTheory.DefU.ClassFin.unitary_map (toAfE D).toRingHom (Formalism.MainNotions.StandardLatticesGL3.sgA D) _ (toAfE_sgA D) _ hh
  obtain ⟨k, k1, k2⟩ := GlobalTheory.UnitarySplit.ga_glue WW 1 x' (one_mem _) hx'
  refine ⟨k, k1, rfl, fun i j => ?_⟩
  rw [k2]
  exact (GlobalTheory.LFun.finAdEquiv D.host.F D.host.E).apply_symm_apply _

end GlobalTheory.BotFormula
