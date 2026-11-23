import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CompactSetSumApproximation
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistDownwardApproxCusp
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistDescentApproximation
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CompactSetSumApproximationStatement

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
noncomputable section
namespace GlobalTheory.DnTypeApprox
theorem downType_lift_approx_span : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ i, i < D.R.m → ∀ Φ, IsThetaFunO R.ψ (GlobalTheory.Grid.neg (G.P (i + 1)).V) (G.P i).V Φ → ∀ φ, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType R.θ (G.P (i + 1)) φ → (∀ h, IntegrableOn (fun g => thetaKO (G.dn i).ω g h Φ * φ g) (G.mP (i + 1)).fd (G.mP (i + 1)).ν) → ∀ C : Set (GA D (G.P i).V), IsCompact C → ∀ δ : ℝ, 0 < δ → ∃ χ ∈ Submodule.span ℂ {f : GA D (G.P i).V → ℂ | ∃ F ∈ (G.P i).Cusp R.θ, ∃ w, f = F w}, ∀ x ∈ C, ‖(∫ g in (G.mP (i + 1)).fd, thetaKO (G.dn i).ω g x Φ * φ g ∂(G.mP (i + 1)).ν) - χ x‖ < δ := by
  intro hL hP D hS G₀ _ _ Pl0 T A Ks _ _ _ R G hRB hG i hi Φ hΦ φ hφ hint C hC δ hδ
  obtain ⟨m, F, v, hF, hFi, hA⟩ := _root_.GlobalTheory.T.twist_downward_approx_cusp hL hP D hS G₀ Pl0 T A Ks R G hRB hG i hi Φ hΦ φ hφ hint C hC (δ / 2) (by positivity)
  have hB := fun k : Fin m => _root_.GlobalTheory.T.twist_descent_approximation hL hP D hS G₀ Pl0 T A Ks R G hRB hG i hi Φ hΦ (F k) (hF k) (v k) (hFi k) C hC
    (δ / (2 * (m + 1))) (by positivity)
  choose n f p hf hBk using hB
  have hCA := (hL D hS G₀ Pl0 T A Ks R G hRB hG).dn i hi
  have hE := fun k (q : Fin (n k)) => hCA (f k q) (hf k q) (F k) (hF k)
  choose F' hF' hI using hE
  refine ⟨∑ k, ∑ q, (F' k q ((G.dn i).It (p k q) (v k)) : GA D (G.P i).V → ℂ), ?_, fun x hx => ?_⟩
  · refine Submodule.sum_mem _ fun k _ => Submodule.sum_mem _ fun q _ => Submodule.subset_span ⟨F' k q, hF' k q, _, rfl⟩
  · have e : (∑ k, ∑ q, (F' k q ((G.dn i).It (p k q) (v k)) : GA D (G.P i).V → ℂ)) x = ∑ k, ∑ q, ∫ g in (G.mP (i + 1)).fd,
        thetaKO (G.dn i).ω g x (GlobalTheory.Grid.fock R.ψ R.θ true (G.P (i + 1)) (G.P i) (f k q) (p k q)) * F k (v k) g ∂(G.mP (i + 1)).ν := by
      simp only [Finset.sum_apply]
      refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun q _ => ?_
      exact ((hI k q (p k q) (v k) x).2).symm
    rw [e]
    exact norm_sub_sum_sum_lt _ _ _ _ hδ (hA x hx) fun k => hBk k x hx
end GlobalTheory.DnTypeApprox
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twist_downType_lift_approx_span : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ i, i < D.R.m → ∀ Φ, IsThetaFunO R.ψ (GlobalTheory.Grid.neg (G.P (i + 1)).V) (G.P i).V Φ → ∀ φ, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType R.θ (G.P (i + 1)) φ → (∀ h, IntegrableOn (fun g => thetaKO (G.dn i).ω g h Φ * φ g) (G.mP (i + 1)).fd (G.mP (i + 1)).ν) → ∀ C : Set (GA D (G.P i).V), IsCompact C → ∀ δ : ℝ, 0 < δ → ∃ χ ∈ Submodule.span ℂ {f : GA D (G.P i).V → ℂ | ∃ F ∈ (G.P i).Cusp R.θ, ∃ w, f = F w}, ∀ x ∈ C, ‖(∫ g in (G.mP (i + 1)).fd, thetaKO (G.dn i).ω g x Φ * φ g ∂(G.mP (i + 1)).ν) - χ x‖ < δ := by
  first | exact @_root_.GlobalTheory.DnTypeApprox.downType_lift_approx_span | exact _root_.GlobalTheory.DnTypeApprox.downType_lift_approx_span | (intros; apply _root_.GlobalTheory.DnTypeApprox.downType_lift_approx_span <;> assumption)
end
