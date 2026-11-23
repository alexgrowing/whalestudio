import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaLiftDiagonalSmoothVectors
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistCuspFormApproxWeighted
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaLiftDiagonalSmoothVectorsStatement

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
noncomputable section
namespace GlobalTheory.DownApprox
open GlobalTheory.Size
variable {D : D7}
theorem downward_approx_cusp : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ i, i < D.R.m → ∀ Φ, IsThetaFunO R.ψ (GlobalTheory.Grid.neg (G.P (i + 1)).V) (G.P i).V Φ → ∀ φ, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType R.θ (G.P (i + 1)) φ → (∀ h, IntegrableOn (fun g => thetaKO (G.dn i).ω g h Φ * φ g) (G.mP (i + 1)).fd (G.mP (i + 1)).ν) → ∀ C : Set (GA D (G.P i).V), IsCompact C → ∀ ε : ℝ, 0 < ε → ∃ (n : ℕ) (F : Fin n → (G.P (i + 1)).Maps) (v : Fin n → SmT (G.P (i + 1)).M), (∀ l, F l ∈ (G.P (i + 1)).Cusp R.θ) ∧ (∀ l h, IntegrableOn (fun g => thetaKO (G.dn i).ω g h Φ * F l (v l) g) (G.mP (i + 1)).fd (G.mP (i + 1)).ν) ∧ ∀ h ∈ C, ‖(∫ g in (G.mP (i + 1)).fd, thetaKO (G.dn i).ω g h Φ * φ g ∂(G.mP (i + 1)).ν) - ∑ l, ∫ g in (G.mP (i + 1)).fd, thetaKO (G.dn i).ω g h Φ * F l (v l) g ∂(G.mP (i + 1)).ν‖ < ε := by
  intro _ hP D _ G₀ _ _ Pl0 T A Ks _ _ _ R G hB hG i hi Φ hΦ φ hφ hint C hC ε hε
  obtain ⟨hν, h𝓕⟩ := GlobalTheory.DownConv.MeasDat.haar_fd (hG.meas.P (i + 1) hi)
  obtain ⟨C1, A1, hC1, hK⟩ := thetaKO_le_quotHeight hB.inf true ((hG.arrows.dn i hi).weil) hΦ hC
  have hfin : (G.mP (i + 1)).ν (G.mP (i + 1)).fd < ⊤ :=
    GlobalTheory.CuspDecay.measure_lt_top GlobalTheory.Mem.VolFin.finVol _ _ _ hν h𝓕
  set X := C1 * ((G.mP (i + 1)).ν (G.mP (i + 1)).fd).toReal with hX
  have hX0 : 0 ≤ X := mul_nonneg hC1 ENNReal.toReal_nonneg
  set δ := ε / (2 * (X + 1)) with hδ
  have hδ0 : 0 < δ := div_pos hε (by positivity)
  obtain ⟨n, F, v, hF, happ⟩ := _root_.GlobalTheory.T.twist_cusp_form_approx_weighted D R.θ hB.inf hP (G.P (i + 1)) φ hφ A1 δ hδ0
  have hI : ∀ l h, IntegrableOn (fun g => thetaKO (G.dn i).ω g h Φ * F l (v l) g) (G.mP (i + 1)).fd
      (G.mP (i + 1)).ν := fun l h => by
    obtain ⟨ha, hc, -⟩ := GlobalTheory.ChainOnto.MultRapid.multT_apply_rapidDec hP.cuspRapidDecay D _ _ _ R.θ hB.inf _ _
      (F l) (hF l) (v l)
    exact GlobalTheory.DownConv.integrableOn_thetaKO_mul_cusp hP.cuspRapidDecay hB.inf true ((hG.arrows.dn i hi).weil) hΦ
      hν h𝓕 ha hc h
  refine ⟨n, F, v, hF, hI, fun h hh => ?_⟩
  rw [← integral_finset_sum Finset.univ fun l _ => hI l h,
    ← integral_sub (hint h) (integrable_finset_sum _ fun l _ => hI l h)]
  have : IsFiniteMeasure ((G.mP (i + 1)).ν.restrict (G.mP (i + 1)).fd) := isFiniteMeasure_restrict.2 hfin.ne
  have hpt : ∀ g, ‖thetaKO (G.dn i).ω g h Φ * φ g - ∑ l, thetaKO (G.dn i).ω g h Φ * F l (v l) g‖ ≤ C1 * δ :=
    fun g => by
      rw [← Finset.mul_sum, ← mul_sub, norm_mul]
      have h1 := hK h hh g
      have h2 := happ g
      calc _ ≤ C1 * GlobalTheory.Grow.quotHeight _ g ^ A1 * ‖φ g - ∑ l, F l (v l) g‖ :=
            mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
        _ = C1 * (‖φ g - ∑ l, F l (v l) g‖ * GlobalTheory.Grow.quotHeight _ g ^ A1) := by ring
        _ ≤ C1 * δ := mul_le_mul_of_nonneg_left h2 hC1
  refine (norm_integral_le_of_norm_le_const (Filter.Eventually.of_forall hpt)).trans_lt ?_
  have hv : C1 * δ * ((G.mP (i + 1)).ν (G.mP (i + 1)).fd).toReal = X * δ := by rw [hX]; ring
  have hlt : X * δ < ε := by
    rw [hδ, ← mul_div_assoc, div_lt_iff₀ (by positivity)]
    nlinarith
  simpa [Measure.real, Measure.restrict_apply_univ, hv] using hlt
end GlobalTheory.DownApprox
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twist_downward_approx_cusp : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ i, i < D.R.m → ∀ Φ, IsThetaFunO R.ψ (GlobalTheory.Grid.neg (G.P (i + 1)).V) (G.P i).V Φ → ∀ φ, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType R.θ (G.P (i + 1)) φ → (∀ h, IntegrableOn (fun g => thetaKO (G.dn i).ω g h Φ * φ g) (G.mP (i + 1)).fd (G.mP (i + 1)).ν) → ∀ C : Set (GA D (G.P i).V), IsCompact C → ∀ ε : ℝ, 0 < ε → ∃ (n : ℕ) (F : Fin n → (G.P (i + 1)).Maps) (v : Fin n → SmT (G.P (i + 1)).M), (∀ l, F l ∈ (G.P (i + 1)).Cusp R.θ) ∧ (∀ l h, IntegrableOn (fun g => thetaKO (G.dn i).ω g h Φ * F l (v l) g) (G.mP (i + 1)).fd (G.mP (i + 1)).ν) ∧ ∀ h ∈ C, ‖(∫ g in (G.mP (i + 1)).fd, thetaKO (G.dn i).ω g h Φ * φ g ∂(G.mP (i + 1)).ν) - ∑ l, ∫ g in (G.mP (i + 1)).fd, thetaKO (G.dn i).ω g h Φ * F l (v l) g ∂(G.mP (i + 1)).ν‖ < ε := by
  first | exact @_root_.GlobalTheory.DownApprox.downward_approx_cusp | exact _root_.GlobalTheory.DownApprox.downward_approx_cusp | (intros; apply _root_.GlobalTheory.DownApprox.downward_approx_cusp <;> assumption)
end
