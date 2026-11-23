import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.KernelNormConstantSpec
import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
import Formalism.LocalToGlobal.ProjectiveLattices.CuspidalL2Subspace
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrPt
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ApplyAddInfRat
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.StdCharFinitePartRationalEqExpTraceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockJetGaussianEntireOriginGridFrames
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.CmBaseFieldIntegersAndCurveIdealFacts
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FrameLat

theorem frame_finRat_mem_latO : ∀ {D : D7} (S T : HSp D) (B : GL (Fin S.rank) D.host.E) (B' : GL (Fin T.rank) D.host.E), Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) B.1 * S.gram * B.1 = 1 → ∀ M : Matrix (Fin T.rank) (Fin S.rank) D.host.E, (∀ i j, M i j ∈ D.host.AA) → GlobalTheory.VacUnique.finRat S T (-(B'.1 * M * (B⁻¹ : GL (Fin S.rank) D.host.E).1)) ∈ latO S T (colLat B : Set (Fin S.rank → D.host.E)) (colLat B' : Set (Fin T.rank → D.host.E)) fun _ => True := by
  intro D S T B B' hB M hM
  have hinv : ((B⁻¹ : GL (Fin S.rank) D.host.E).1) = Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) B.1 * S.gram := by
    have h1 : ((B⁻¹ : GL (Fin S.rank) D.host.E).1) * B.1 = 1 := by
      have := congrArg Units.val (inv_mul_cancel B); simpa using this
    have h2 : B.1 * ((B⁻¹ : GL (Fin S.rank) D.host.E).1) = 1 := by
      have := congrArg Units.val (mul_inv_cancel B); simpa using this
    calc ((B⁻¹ : GL (Fin S.rank) D.host.E).1)
        = (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) B.1 * S.gram * B.1) * ((B⁻¹ : GL (Fin S.rank) D.host.E).1) := by rw [hB, one_mul]
      _ = _ := by rw [Matrix.mul_assoc _ B.1, h2, Matrix.mul_one]
  have key : -(B'.1 * M * (B⁻¹ : GL (Fin S.rank) D.host.E).1) = ∑ l, ∑ k,
      GlobalTheory.LatVac.genMap S T (-M l k) (fun m => B.1 m k) (fun i => B'.1 i l) := by
    rw [hinv]
    ext i j
    simp only [GlobalTheory.LatVac.genMap, Matrix.neg_apply, Matrix.sum_apply, Matrix.of_apply, Matrix.mul_apply]
    have hc : ∀ k m, Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) B.1 k m = star (B.1 m k) := fun _ _ => rfl
    simp only [hc, Finset.sum_mul, ← Finset.sum_neg_distrib]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => ?_
    rw [neg_mul, neg_mul, mul_assoc, mul_assoc, mul_left_comm]
  have hmem : -(B'.1 * M * (B⁻¹ : GL (Fin S.rank) D.host.E).1) ∈ GlobalTheory.LatVac.latRat S T (colLat B : Set (Fin S.rank → D.host.E)) (colLat B' : Set (Fin T.rank → D.host.E)) := by
    rw [key]
    refine AddSubgroup.sum_mem _ fun l _ => AddSubgroup.sum_mem _ fun k _ => AddSubgroup.subset_closure ?_
    refine ⟨-M l k, Submodule.neg_mem (D.host.AA : Submodule (𝓞 D.host.E) D.host.E) (hM l k), _, ?_, _, ?_, rfl⟩
    · exact Submodule.subset_span ⟨k, rfl⟩
    · exact Submodule.subset_span ⟨l, rfl⟩
  exact GlobalTheory.LatVac.finTens_mem_latO (GlobalTheory.LatVac.one_mem_intAf _) hmem

end GlobalTheory.FrameLat
