import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasTypeVec
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.LabesseWaldspurger
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ConstantTermVanishing
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.AdjointRadical
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspidalNoRadicalFixed
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.StandardMaximalParabolic
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CentralizerTensorForms
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AbsAUnit
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Chamber GlobalTheory.TruncKer GlobalTheory.Cusp
open GlobalTheory.LeviShift

noncomputable section

open scoped TensorProduct NNReal

namespace GlobalTheory.LeviShift

variable {D : D7} {V : HSp D} (Φ : WittFrame V)

theorem bas_stdVec (j i : Fin (wittIndex V)) : bas Φ (stdVec j) i = Φ.e i := by
  unfold bas; rw [if_neg]; unfold stdVec; split_ifs <;> decide

theorem dbas_stdVec (j i : Fin (wittIndex V)) : dbas Φ (stdVec j) i = Φ.f i := by
  unfold dbas; rw [if_neg]; unfold stdVec; split_ifs <;> decide

theorem detMat_stdVec_apply (j : Fin (wittIndex V)) (p : PA Φ.flag0) (a b : Supp (stdVec j)) :
    detMat Φ D.sp.cm (AF D.host.F) (stdVec j) p a b =
      Φ.coef D.sp.cm (AF D.host.F) a.1
        (GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.act D.sp.cm V (p : GA D V) (GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.coordR V (AF D.host.F) (Φ.e b.1))) := by
  simp only [detMat, Matrix.of_apply, bas_stdVec, dbas_stdVec]; rfl

theorem detMat_stdVec_blockTriangular (j : Fin (wittIndex V)) (p : PA Φ.flag0) :
    (detMat Φ D.sp.cm (AF D.host.F) (stdVec j) p).BlockTriangular id := by
  intro a b hba
  rw [detMat_stdVec_apply]
  apply Φ.coef_eq_zero
  have he : GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.coordR V (AF D.host.F) (Φ.e b.1) ∈
      GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.extSub (F := D.host.F) V (AF D.host.F) (Φ.flag0.X b.1.succ) :=
    coordR_mem V _ (Submodule.subset_span ⟨b.1, Nat.lt_succ_self _, rfl⟩)
  have h1 := mem_parab_iff_maps.1 (IsoFlag.mem_par.1 p.2 b.1.succ) _ he
  have hle : b.1.succ ≤ a.1.castSucc := by
    have : b.1.val < a.1.val := hba
    rw [Fin.le_iff_val_le_val, Fin.val_succ, Fin.coe_castSucc]; omega
  exact Submodule.span_mono (Set.image_mono (Φ.flag0.strictMono.monotone hle)) h1

theorem prod_absChi_eq_absA_detU (j : Fin (wittIndex V)) (p : PA Φ.flag0) :
    ∏ i ∈ Finset.Iic j, absChi Φ i p = absA D.host.F D.host.E (detU Φ D.sp.cm (AF D.host.F) (stdVec j) p) := by
  have hdet : detU Φ D.sp.cm (AF D.host.F) (stdVec j) p =
      ((∏ a : Supp (stdVec j), (Φ.chi D.sp.cm (AF D.host.F) a.1).toHomUnits p :
        (AF D.host.F ⊗[D.host.F] D.host.E)ˣ) : AF D.host.F ⊗[D.host.F] D.host.E) := by
    rw [detU, Matrix.det_of_upperTriangular (detMat_stdVec_blockTriangular Φ j p), Units.coe_prod]
    refine Finset.prod_congr rfl fun a _ => ?_
    rw [detMat_stdVec_apply]; rfl
  rw [hdet, absA_unit, map_prod]
  rw [Finset.prod_subtype (Finset.Iic j) (p := fun i => stdVec j i ≠ 0)
    (fun i => by simp [stdVec])]
  rfl

end GlobalTheory.LeviShift

theorem GlobalTheory.LeviShift.prod_absChi_Iic : ∀ (D : D7) (V : HSp D) (Φ : WittFrame V) (j : Fin (wittIndex V)) (p : PA Φ.flag0),
    ∏ i ∈ Finset.Iic j, absChi Φ i p = absA D.host.F D.host.E (detU Φ D.sp.cm (AF D.host.F) (stdVec j) p) :=
  fun _ _ Φ j p => GlobalTheory.LeviShift.prod_absChi_eq_absA_detU Φ j p

end
