import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaLiftVerticalCuspidalGridStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaLiftVerticalCuspidalTypeStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RangeSndRel
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsAllTiedNotStable
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.DiscreteSeriesHermitianUniqueOfClassification
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.FinitePartTypes
import Development.AbelianVarietyTheory.Proofs.HeightProofs.AutomorphicFormUniformLimitDiscreteSeriesSeriesStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.CuspTypeApproxX

theorem norm_sub_sum_sigma_lt {E : Type*} [SeminormedAddCommGroup E] {m : ℕ} (I : E) (L : Fin m → E) (n : Fin m → ℕ)
    (J : ∀ k, Fin (n k) → E) {δ : ℝ} (hδ : 0 < δ) (h1 : ‖I - ∑ k, L k‖ < δ / 2)
    (h2 : ∀ k, ‖L k - ∑ j, J k j‖ < δ / (2 * (m + 1))) :
    ‖I - ∑ l : Fin (∑ k, n k), J (finSigmaFinEquiv.symm l).1 (finSigmaFinEquiv.symm l).2‖ < δ := by
  have hs : ∑ l : Fin (∑ k, n k), J (finSigmaFinEquiv.symm l).1 (finSigmaFinEquiv.symm l).2 = ∑ k, ∑ j, J k j := by
    rw [Equiv.sum_comp finSigmaFinEquiv.symm (fun x => J x.1 x.2), Fintype.sum_sigma]
  have hd : I - ∑ k, ∑ j, J k j = (I - ∑ k, L k) + ∑ k, (L k - ∑ j, J k j) := by
    rw [Finset.sum_sub_distrib]; abel
  rw [hs, hd]
  have h3 : ‖∑ k, (L k - ∑ j, J k j)‖ ≤ m * (δ / (2 * (m + 1))) := by
    refine (norm_sum_le _ _).trans ?_
    calc ∑ k, ‖L k - ∑ j, J k j‖ ≤ ∑ _k : Fin m, δ / (2 * (m + 1)) := Finset.sum_le_sum fun k _ => (h2 k).le
      _ = m * (δ / (2 * (m + 1))) := by simp
  have h4 : (m : ℝ) * (δ / (2 * (m + 1))) ≤ δ / 2 := by
    have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  calc ‖(I - ∑ k, L k) + ∑ k, (L k - ∑ j, J k j)‖ ≤ ‖I - ∑ k, L k‖ + ‖∑ k, (L k - ∑ j, J k j)‖ := norm_add_le _ _
    _ < δ / 2 + δ / 2 := by linarith
    _ = δ := by ring

theorem lift_approx_fock : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → GlobalTheory.FunPr.Hypotheses₂ → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ t i j, i < D.R.m → j ≤ D.R.m → ∀ Φ, IsThetaFunO R.ψ (GlobalTheory.Grid.neg (G.V (i + 1) j).V) (G.V i j).V Φ → ∀ φ, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType R.θ (G.V i j) φ → (∀ h, IntegrableOn (fun g => thetaKO (G.X i j).ω h g Φ * φ g) (G.meas t i j).fd (G.meas t i j).ν) → ∀ C : Set (GA D (G.V (i + 1) j).V), IsCompact C → ∀ δ : ℝ, 0 < δ → ∃ (n : ℕ) (f : Fin n → (WO (G.V (i + 1) j).V (G.V i j).V → ℂ)) (p : Fin n → GlobalTheory.Grid.Pol (G.V (i + 1) j) (G.V i j)) (F : Fin n → (G.V i j).Maps) (v : Fin n → SmT (G.V i j).M), (∀ l, GlobalTheory.Grid.IsFinVec R.ψ R.θ true (G.V (i + 1) j) (G.V i j) (f l)) ∧ (∀ l, F l ∈ (G.V i j).Cusp R.θ) ∧ ∀ h ∈ C, ‖(∫ g in (G.meas t i j).fd, thetaKO (G.X i j).ω h g Φ * φ g ∂(G.meas t i j).ν) - ∑ l, ∫ g in (G.meas t i j).fd, thetaKO (G.X i j).ω h g (GlobalTheory.Grid.fock R.ψ R.θ true (G.V (i + 1) j) (G.V i j) (f l) (p l)) * F l (v l) g ∂(G.meas t i j).ν‖ < δ := by
  intro hL hP D hS G₀ _ _ Pl0 T A Ks _ _ _ R G hRB hG t i j hi hj Φ hΦ φ hφ hint C hC δ hδ
  obtain ⟨m, F, v, hF, hFi, hA⟩ := GlobalTheory.T.theta_lift_vertical_cuspidal_grid hL hP D hS G₀ Pl0 T A Ks R G hRB hG t i j hi hj Φ hΦ φ hφ hint C hC (δ / 2) (by positivity)
  have hB := fun k : Fin m => GlobalTheory.T.theta_lift_vertical_cuspidal_type hL hP D hS G₀ Pl0 T A Ks R G hRB hG t i j hi hj Φ hΦ (F k) (hF k) (v k) (hFi k) C hC
    (δ / (2 * (m + 1))) (by positivity)
  choose n f p hf hBk using hB
  refine ⟨∑ k, n k, fun l => f (finSigmaFinEquiv.symm l).1 (finSigmaFinEquiv.symm l).2,
    fun l => p (finSigmaFinEquiv.symm l).1 (finSigmaFinEquiv.symm l).2, fun l => F (finSigmaFinEquiv.symm l).1,
    fun l => v (finSigmaFinEquiv.symm l).1, fun l => hf _ _, fun l => hF _, fun h hh => ?_⟩
  exact norm_sub_sum_sigma_lt (J := fun k q => ∫ g in (G.meas t i j).fd, thetaKO (G.X i j).ω h g
      (GlobalTheory.Grid.fock R.ψ R.θ true (G.V (i + 1) j) (G.V i j) (f k q) (p k q)) * F k (v k) g ∂(G.meas t i j).ν) _ _ _ hδ
    (hA h hh) fun k => hBk k h hh

end GlobalTheory.CuspTypeApproxX
