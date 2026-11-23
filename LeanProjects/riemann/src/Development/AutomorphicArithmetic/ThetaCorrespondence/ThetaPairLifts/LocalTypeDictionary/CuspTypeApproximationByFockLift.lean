import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NegativeThetaLevelSixth
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.CuspFormsApproximatedByThetaLifts
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ThetaLiftsDenseInCuspForms
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NegativeThetaLevelSixthStatement

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
noncomputable section
namespace GlobalTheory.CuspTypeApproxX
theorem cuspType_lift_approx_fockSpace : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ t i j, i < D.R.m → j ≤ D.R.m → ∀ Φ, IsThetaFunO R.ψ (GlobalTheory.Grid.neg (G.V (i + 1) j).V) (G.V i j).V Φ → ∀ φ, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType R.θ (G.V i j) φ → (∀ h, IntegrableOn (fun g => thetaKO (G.X i j).ω h g Φ * φ g) (G.meas t i j).fd (G.meas t i j).ν) → ∀ C : Set (GA D (G.V (i + 1) j).V), IsCompact C → ∀ δ : ℝ, 0 < δ → ∃ (n : ℕ) (f : Fin n → (WO (G.V (i + 1) j).V (G.V i j).V → ℂ)) (p : Fin n → GlobalTheory.Grid.Pol (G.V (i + 1) j) (G.V i j)) (F : Fin n → (G.V i j).Maps) (v : Fin n → SmT (G.V i j).M), (∀ l, GlobalTheory.Grid.IsFinVec R.ψ R.θ true (G.V (i + 1) j) (G.V i j) (f l)) ∧ (∀ l, F l ∈ (G.V i j).Cusp R.θ) ∧ ∀ h ∈ C, ‖(∫ g in (G.meas t i j).fd, thetaKO (G.X i j).ω h g Φ * φ g ∂(G.meas t i j).ν) - ∑ l, ∫ g in (G.meas t i j).fd, thetaKO (G.X i j).ω h g (GlobalTheory.Grid.fock R.ψ R.θ true (G.V (i + 1) j) (G.V i j) (f l) (p l)) * F l (v l) g ∂(G.meas t i j).ν‖ < δ := by
  intro hL hP D hS G₀ _ _ Pl0 T A Ks _ _ _ R G hRB hG t i j hi hj Φ hΦ φ hφ hint C hC δ hδ
  obtain ⟨m, F, v, hF, hFi, hA⟩ := _root_.GlobalTheory.T.cusp_forms_approximated_by_theta_lifts hL hP D hS G₀ Pl0 T A Ks R G hRB hG t i j hi hj Φ hΦ φ hφ hint C hC (δ / 2) (by positivity)
  have hB := fun k : Fin m => _root_.GlobalTheory.T.theta_lifts_dense_in_cusp_forms hL hP D hS G₀ Pl0 T A Ks R G hRB hG t i j hi hj Φ hΦ (F k) (hF k) (v k) (hFi k) C hC
    (δ / (2 * (m + 1))) (by positivity)
  choose n f p hf hBk using hB
  refine ⟨∑ k, n k, fun l => f (finSigmaFinEquiv.symm l).1 (finSigmaFinEquiv.symm l).2,
    fun l => p (finSigmaFinEquiv.symm l).1 (finSigmaFinEquiv.symm l).2, fun l => F (finSigmaFinEquiv.symm l).1,
    fun l => v (finSigmaFinEquiv.symm l).1, fun l => hf _ _, fun l => hF _, fun h hh => ?_⟩
  exact norm_sub_sum_sigma_lt (J := fun k q => ∫ g in (G.meas t i j).fd, thetaKO (G.X i j).ω h g
      (GlobalTheory.Grid.fock R.ψ R.θ true (G.V (i + 1) j) (G.V i j) (f k q) (p k q)) * F k (v k) g ∂(G.meas t i j).ν) _ _ _ hδ
    (hA h hh) fun k => hBk k h hh
end GlobalTheory.CuspTypeApproxX
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cusp_type_approximation_by_fock_lift : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ t i j, i < D.R.m → j ≤ D.R.m → ∀ Φ, IsThetaFunO R.ψ (GlobalTheory.Grid.neg (G.V (i + 1) j).V) (G.V i j).V Φ → ∀ φ, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType R.θ (G.V i j) φ → (∀ h, IntegrableOn (fun g => thetaKO (G.X i j).ω h g Φ * φ g) (G.meas t i j).fd (G.meas t i j).ν) → ∀ C : Set (GA D (G.V (i + 1) j).V), IsCompact C → ∀ δ : ℝ, 0 < δ → ∃ (n : ℕ) (f : Fin n → (WO (G.V (i + 1) j).V (G.V i j).V → ℂ)) (p : Fin n → GlobalTheory.Grid.Pol (G.V (i + 1) j) (G.V i j)) (F : Fin n → (G.V i j).Maps) (v : Fin n → SmT (G.V i j).M), (∀ l, GlobalTheory.Grid.IsFinVec R.ψ R.θ true (G.V (i + 1) j) (G.V i j) (f l)) ∧ (∀ l, F l ∈ (G.V i j).Cusp R.θ) ∧ ∀ h ∈ C, ‖(∫ g in (G.meas t i j).fd, thetaKO (G.X i j).ω h g Φ * φ g ∂(G.meas t i j).ν) - ∑ l, ∫ g in (G.meas t i j).fd, thetaKO (G.X i j).ω h g (GlobalTheory.Grid.fock R.ψ R.θ true (G.V (i + 1) j) (G.V i j) (f l) (p l)) * F l (v l) g ∂(G.meas t i j).ν‖ < δ := by
  first | exact @_root_.GlobalTheory.CuspTypeApproxX.cuspType_lift_approx_fockSpace | exact _root_.GlobalTheory.CuspTypeApproxX.cuspType_lift_approx_fockSpace | (intros; apply _root_.GlobalTheory.CuspTypeApproxX.cuspType_lift_approx_fockSpace <;> assumption)
end
