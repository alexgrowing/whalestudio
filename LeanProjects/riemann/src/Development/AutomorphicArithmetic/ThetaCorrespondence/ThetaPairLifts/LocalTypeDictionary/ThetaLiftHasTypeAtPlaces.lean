import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HorizontalThetaLevelFifth
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ThetaLiftApproxOfApproxData
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.HasTypeAtCuspOfCuspValueType
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HorizontalThetaLevelFifthStatement

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
noncomputable section
namespace GlobalTheory.ThetaLiftTypeTh
theorem thetaLift_hasTypeAt : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ t i j, i ≤ D.R.m → j < D.R.m → ∀ Φ, IsThetaFunO R.ψ (G.V i j).V (G.V i (j + 1)).V Φ → ∀ φ, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType R.θ (G.V i (j + 1)) φ → (∀ h, IntegrableOn (fun g => thetaKO (G.th t i j).ω h g Φ * φ g) (G.meas t i (j + 1)).fd (G.meas t i (j + 1)).ν) → ∀ τ, GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.HasTypeAt R.θ (G.V i j).V τ ((G.V i j).S τ) (fun h => ∫ g in (G.meas t i (j + 1)).fd, thetaKO (G.th t i j).ω h g Φ * φ g ∂(G.meas t i (j + 1)).ν) := by
  intro hL hP D hSz G₀ _ _ Pl0 T A Ks _ _ _ R G hR hG t i j hi hj Φ hΦ φ hφ hint τ
  have hV : (G.V i j).V.SigOK := sigOK_vert G hG hi (by omega)
  intro C hC δ hδ
  obtain ⟨n, f, p, F, v, hf, hF, happ⟩ := _root_.GlobalTheory.T.approximation_by_theta_lifts hL hP D hSz G₀ Pl0 T A Ks R G hR hG t i j hi hj Φ hΦ φ hφ hint C hC (δ / 2) (by linarith)
  have hCA := hL D hSz G₀ Pl0 T A Ks R G hR hG
  choose F' hF' hE using fun l => hCA.th t i j hi hj (f l) (hf l) (F l) (hF l)
  have hψ0 : GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.HasTypeAt R.θ (G.V i j).V τ ((G.V i j).S τ)
      (∑ l, F' l ((G.th t i j).It (p l) (v l))) :=
    (GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.typeSub R.θ _ τ _).sum_mem fun l _ => _root_.GlobalTheory.T.cusp_value_has_prescribed_type hP R.θ hR.inf _ hV _ (hF' l) _ τ
  obtain ⟨ψ, hψ, hψC⟩ := hψ0 C hC (δ / 2) (by linarith)
  refine ⟨ψ, hψ, fun x hx => ?_⟩
  have h1 := happ x hx
  have h2 := hψC x hx
  have e : (∑ l, ∫ g in (G.meas t i (j + 1)).fd, thetaKO (G.th t i j).ω x g (GlobalTheory.Grid.fock R.ψ R.θ false (G.V i j) (G.V i (j + 1)) (f l) (p l)) * F l (v l) g ∂(G.meas t i (j + 1)).ν) = (∑ l, F' l ((G.th t i j).It (p l) (v l))) x := by
    rw [Finset.sum_apply]
    exact Finset.sum_congr rfl fun l _ => (hE l (p l) (v l) x).2
  rw [e] at h1
  calc _ = ‖((∫ g in (G.meas t i (j + 1)).fd, thetaKO (G.th t i j).ω x g Φ * φ g ∂(G.meas t i (j + 1)).ν) - (∑ l, F' l ((G.th t i j).It (p l) (v l))) x) + ((∑ l, F' l ((G.th t i j).It (p l) (v l))) x - ψ x)‖ := by congr 1; ring
    _ ≤ _ := norm_add_le _ _
    _ < δ / 2 + δ / 2 := add_lt_add h1 h2
    _ = δ := by ring
end GlobalTheory.ThetaLiftTypeTh
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaLift_hasTypeAt_places : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ t i j, i ≤ D.R.m → j < D.R.m → ∀ Φ, IsThetaFunO R.ψ (G.V i j).V (G.V i (j + 1)).V Φ → ∀ φ, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType R.θ (G.V i (j + 1)) φ → (∀ h, IntegrableOn (fun g => thetaKO (G.th t i j).ω h g Φ * φ g) (G.meas t i (j + 1)).fd (G.meas t i (j + 1)).ν) → ∀ τ, GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.HasTypeAt R.θ (G.V i j).V τ ((G.V i j).S τ) (fun h => ∫ g in (G.meas t i (j + 1)).fd, thetaKO (G.th t i j).ω h g Φ * φ g ∂(G.meas t i (j + 1)).ν) := by
  first | exact @_root_.GlobalTheory.ThetaLiftTypeTh.thetaLift_hasTypeAt | exact _root_.GlobalTheory.ThetaLiftTypeTh.thetaLift_hasTypeAt | (intros; apply _root_.GlobalTheory.ThetaLiftTypeTh.thetaLift_hasTypeAt <;> assumption)
end
