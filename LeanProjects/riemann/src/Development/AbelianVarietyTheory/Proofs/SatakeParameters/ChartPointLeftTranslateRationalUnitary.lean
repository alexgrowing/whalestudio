import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.UnderTie
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.TwistEmptyOfChartsEx
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.RedPEqZeroOfDiv
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.LocalProductMeasures.MqRowSGUnif
import Formalism.SharpRestriction.GlobalSchurBounds.Joints
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.OrthonormalCoordsConjUnitaryStandardFormStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsUnitaryAutColumnFieldOfStandardUnitaryMatrStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TransportedLatticeOfLinearAutImageEqMatrixImageStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelPrimeFunctionalsMoveRationalLatticeAutStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelFrameLiftUnitaryAutNearAdelicMatrixDepthOneStatement

noncomputable section

open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.UG Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct

namespace GlobalTheory.TwRat

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in

theorem ratPt : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => ∀ (i : ℕ) (hi : i ≤ D.R.m) (β : (St i hi).Ch) (x x' : UA D i hi) p, ∀ γ ∈ Formalism.UG.UJ (Formalism.L2.Forms.sigD D : D.host.E →+* D.host.E) (Formalism.L2.Forms.gramN D i hi), x'.1 = ratA D.host.F γ * x.1 → IsPtAd A a i hi β x p → ∃ p', IsPtAd A a i hi β x' p') := by
  intro D _ _ _ _ _ _ _ _ t u μ St A dtU a hP _ i hi β x x' p γ hγ hx hp
  obtain ⟨g, hg⟩ := GlobalTheory.T.exists_unitaryAut_columnField_of_standard_unitary_matrix t.seam t.seam_ok (A.crd i hi * γ * (A.crd i hi)⁻¹) (GlobalTheory.T.orthonormalCoords_conj_unitary_standard_form D _ _ _ (hP.crd_orth i hi) hγ)
  have hmv : ∀ y : GL (Fin (D.R.N i)) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F),
      ratA D.host.F (A.crd i hi) * (ratA D.host.F γ * y) = ratA D.host.F (seamGL t.seam g.1) * (ratA D.host.F (A.crd i hi) * y) := by
    intro y
    rw [hg, ← mul_assoc, ← mul_assoc, ← map_mul, ← map_mul, inv_mul_cancel_right]
  let a' : UF t.X.E (D.R.N i) × GLG t.X.E (D.R.N i) t.Pr.vGs × GLQ t.X.E (D.R.N i) (QE t.sel (t.tup μ : Chr t.X.F t.X.E t.X.K)) := (g, 1, 1)
  refine ⟨a' • p, ?_, ?_, ?_⟩
  · have e1 : (a' • p).deco.1.N = Formalism.HermitianLatticesTheory.gmap g.1 p.deco.1.N := rfl
    rw [e1, GlobalTheory.T.transportedLattice_of_linearAutImage_eq_matrixImage, hg, hp.lat, hx, latCo_rat _ _ _ hγ]
  · intro P
    have hb := hp.frame P
    rw [hx, hmv, mul_assoc (ratA D.host.F (seamGL t.seam g.1))]
    by_cases hPg : P.1 ∈ t.Pr.vGs
    · have hD : (t.cst μ).D P = 1 := (t.idx_ok μ).depthG P hPg
      have e0 : frsF t.sel (t.tup μ) p P = p.deco.1.liftFr ⟨P.1, hPg⟩ := dif_pos hPg
      have e1 : frsF (R := D.R) t.sel (t.tup μ) (a' • p) P = ((g, (1 : GLG t.X.E (D.R.N i) t.Pr.vGs)) • p.deco).1.liftFr ⟨P.1, hPg⟩ := dif_pos hPg
      rw [hD, e0] at hb
      rw [hD, e1]
      exact GlobalTheory.T.levelFrameLift_unitaryAut_near_adelicMatrix_depth_one t.seam p.deco ⟨P.1, hPg⟩ g (mq_rowSG_unif (t.tup μ) hP.fields.ok t.pr_ok hP.sel P) _ hb
    · have e1 : frsF (R := D.R) t.sel (t.tup μ) (a' • p) P = g.1 * frsF t.sel (t.tup μ) p P := by
        unfold frsF
        rw [dif_neg hPg, dif_neg hPg]
        show g.1 * p.fr _ * (((1 : GLQ t.X.E (D.R.N i) (QE t.sel (t.tup μ : Chr t.X.F t.X.E t.X.K))) _)⁻¹).1 = _
        simp
      rw [e1, map_mul, nearAt_rat_mul]
      exact hb
  · intro P v h hv
    rw [hx, hmv]
    exact GlobalTheory.T.levelPrimeFunctionals_move_rational_lattice_aut t.seam _ P v h _ _ _ g.1 1 (hp.fnl P v h hv)

end GlobalTheory.TwRat
