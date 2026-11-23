import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsTateZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsProjOverOfIsProjOverBase
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsHeckeQuotientTriple
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPointPicardClassEqTranslateOfTrivialLambda
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelAmpleRigidTranslateLineBundleRationalPoint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KernelTrivialRigidTranslateLineBundle
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPolarisationDescentMulOddVeryDense
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsPointPrimitiveBundleEqTranslatePpav
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsRigidTranslatePrincipalPolarisationOrderTw
open CategoryTheory AlgebraicGeometry Set Matrix ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.ArInt GlobalTheory.TorsionForm GlobalTheory.ThetaRR
open GlobalTheory.LB (toMod)
open GlobalTheory.LieVB (omega)
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe (Fl Pt stdLat symMat tauU siegel symPart ChernIsFlat IsMetric InducesPolarisation cov)
open ReciprocityTheory.L2DbarEstimates (V)
open Filter Topology
open scoped ContDiff
open MonoidalCategory CartesianMonoidalCategory Limits
open GlobalTheory.CechPic (Pic cls lam)
open MonObj
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AmpleKerFibre

theorem relAmple_kTriv_of_lam_eq : ∀ (K : Type) [Field K] [IsAlgClosed K] (B : Over (Sp K)) [GrpObj B], IsAbelianScheme B → ∀ (L₀ : LB B.left) (h₀ : L₀.IsLB), Out.RelAmple B L₀ → Out.KTriv B L₀ → ∀ (N : LB B.left) (hN : N.IsLB), lam (cls N hN) (fst B B) (snd B B) = lam (cls L₀ h₀) (fst B B) (snd B B) → Out.RelAmple B N ∧ Out.KTriv B N := by
  intro K _ _ B _ hB L₀ h₀ hA hK N hN hlam
  have := hB.comm
  obtain ⟨O, hO, eO⟩ := CechPic.cls_surj (cls N hN - cls L₀ h₀)
  have lamO : lam (cls O hO) (fst B B) (snd B B) = 0 := by
    rw [eO, GlobalTheory.PrimitiveOverField.lam_sub, hlam, sub_self]
  obtain ⟨x, hx⟩ := GlobalTheory.PointTranslate.exists_point_cls_eq_lam K B hB L₀ h₀ hK O hO lamO
  have hR : (GlobalTheory.RigidTranslate.rigTransl L₀ x).IsLB := LB.isLB_linComb h₀ _ _
  have hcls : cls _ hR = cls N hN := by
    rw [CechPic.cls_linComb h₀, Fin.sum_univ_two]
    have e1 : cls N hN = cls O hO + cls L₀ h₀ := by rw [eO]; abel
    rw [e1, hx, GlobalTheory.PrimitiveOverField.lam_const, Over.id_left, CechPic.pull_id]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, one_smul, neg_smul]
    rw [GlobalTheory.PrimitiveOverField.pull_const, GlobalTheory.PolTranslate.transl, _root_.mul_comm (𝟙 B)]
    abel
  have hiso := (CechPic.cls_eq_iff hR hN).1 hcls
  refine ⟨?_, GlobalTheory.MulDescent.kTriv_of_lbIso hR hN hiso
    (GlobalTheory.RigidTranslate.kTriv_rigTransl_any _ B L₀ h₀ x hK)⟩
  have hAR := GlobalTheory.RigidTranslate.relAmple_rigTransl_point K B hB L₀ h₀ x hA
  obtain ⟨w, hw⟩ : LBIso N ((GlobalTheory.RigidTranslate.rigTransl L₀ x).pull (𝟙 B.left)) :=
    hiso.symm.chartPull (Geo.Tor.chartPullId N) (Geo.Tor.chartPullPull _ (𝟙 _) (𝟙 _) rfl)
  exact relAmple_pull (A' := B) (IsPullback.id_horiz B.hom) hR hN ((isGen_iff w).1 hw) ⊤
    (isAffineOpen_top _) (fun _ => trivial) hAR

end GlobalTheory.AmpleKerFibre
