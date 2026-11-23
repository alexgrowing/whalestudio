import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaLiftDiagonalSmoothVectorsStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaLiftDiagonalRapidDecayStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RangeSndRel
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.HeightProofs.TypeAtOfDiscreteSeries
import Development.AbelianVarietyTheory.Proofs.HeightProofs.AutomorphicFormUniformLimitDiscreteSeriesSeriesStatement
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.DiscreteSeriesHermitianUniqueOfClassification
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.DnTypeApprox

theorem norm_sub_sum_sum_lt {E : Type*} [SeminormedAddCommGroup E] {m : ℕ} (I : E) (L : Fin m → E) (n : Fin m → ℕ)
    (J : ∀ k, Fin (n k) → E) {δ : ℝ} (hδ : 0 < δ) (h1 : ‖I - ∑ k, L k‖ < δ / 2)
    (h2 : ∀ k, ‖L k - ∑ q, J k q‖ < δ / (2 * (m + 1))) :
    ‖I - ∑ k, ∑ q, J k q‖ < δ := by
  have hd : I - ∑ k, ∑ q, J k q = (I - ∑ k, L k) + ∑ k, (L k - ∑ q, J k q) := by
    rw [Finset.sum_sub_distrib]; abel
  rw [hd]
  have h3 : ‖∑ k, (L k - ∑ q, J k q)‖ ≤ m * (δ / (2 * (m + 1))) := by
    refine (norm_sum_le _ _).trans ?_
    calc ∑ k, ‖L k - ∑ q, J k q‖ ≤ ∑ _k : Fin m, δ / (2 * (m + 1)) := Finset.sum_le_sum fun k _ => (h2 k).le
      _ = m * (δ / (2 * (m + 1))) := by simp
  have h4 : (m : ℝ) * (δ / (2 * (m + 1))) ≤ δ / 2 := by
    have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  calc ‖(I - ∑ k, L k) + ∑ k, (L k - ∑ q, J k q)‖ ≤ ‖I - ∑ k, L k‖ + ‖∑ k, (L k - ∑ q, J k q)‖ := norm_add_le _ _
    _ < δ / 2 + δ / 2 := by linarith
    _ = δ := by ring

theorem lift_approx_span : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → GlobalTheory.FunPr.Hypotheses₂ → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ i, i < D.R.m → ∀ Φ, IsThetaFunO R.ψ (GlobalTheory.Grid.neg (G.P (i + 1)).V) (G.P i).V Φ → ∀ φ, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType R.θ (G.P (i + 1)) φ → (∀ h, IntegrableOn (fun g => thetaKO (G.dn i).ω g h Φ * φ g) (G.mP (i + 1)).fd (G.mP (i + 1)).ν) → ∀ C : Set (GA D (G.P i).V), IsCompact C → ∀ δ : ℝ, 0 < δ → ∃ χ ∈ Submodule.span ℂ {f : GA D (G.P i).V → ℂ | ∃ F ∈ (G.P i).Cusp R.θ, ∃ w, f = F w}, ∀ x ∈ C, ‖(∫ g in (G.mP (i + 1)).fd, thetaKO (G.dn i).ω g x Φ * φ g ∂(G.mP (i + 1)).ν) - χ x‖ < δ := by
  intro hL hP D hS G₀ _ _ Pl0 T A Ks _ _ _ R G hRB hG i hi Φ hΦ φ hφ hint C hC δ hδ
  obtain ⟨m, F, v, hF, hFi, hA⟩ := GlobalTheory.T.theta_lift_diagonal_smooth_vectors hL hP D hS G₀ Pl0 T A Ks R G hRB hG i hi Φ hΦ φ hφ hint C hC (δ / 2) (by positivity)
  have hB := fun k : Fin m => GlobalTheory.T.theta_lift_diagonal_rapid_decay hL hP D hS G₀ Pl0 T A Ks R G hRB hG i hi Φ hΦ (F k) (hF k) (v k) (hFi k) C hC
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
