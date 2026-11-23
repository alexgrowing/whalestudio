import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RangeSndRel
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.HeightProofs.TypeAtOfDiscreteSeries
import Development.AbelianVarietyTheory.Proofs.HeightProofs.AutomorphicFormUniformLimitDiscreteSeriesSeriesStatement
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.DiscreteSeriesHermitianUniqueOfClassification
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CuspFormUniformHeightApproxStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegrableOnThetaKOMulCusp
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaKernelMulConjCuspFormIntegrableOn
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MultTApplyRapidDec
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaGrowthOfThetaSquareIntegrable
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
noncomputable section

namespace GlobalTheory.DownApprox

open GlobalTheory.Size

variable {D : D7}

theorem thetaKO_le_unif {V W : HSp D} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {χS χT : (AE D)ˣ →* Circle}
    {ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)} {f : WO V W → ℂ}
    (hθ : IsInfFam θ) (hω : IsWeilDatumO ψ V W χS χT ω) (hf : IsThetaFunO ψ V W f)
    {K : Set (GA D W)} (hK : IsCompact K) :
    ∃ (C : ℝ) (A : ℕ), 0 ≤ C ∧ ∀ h ∈ K, ∀ g, ‖thetaKO ω g h f‖ ≤ C * GlobalTheory.Grow.height V g ^ A := by
  obtain ⟨A, d, H⟩ := GlobalTheory.KernelSeminorm.thetaGrowth D V.rank W.rank
  obtain ⟨U, hU, hl⟩ := isTheta_iff_level.1 hf
  obtain ⟨μ, 𝓕, hμ⟩ := exists_isCovolOne V W
  obtain ⟨C, hC0, hC⟩ := (H V W rfl rfl).real ψ hθ hU
  obtain ⟨B, hB⟩ := GlobalTheory.Grow.exists_height_le_of_isCompact W hK
  have hs : 0 ≤ C * (sobO ψ θ μ 𝓕 d f).toReal := mul_nonneg hC0 ENNReal.toReal_nonneg
  refine ⟨C * (sobO ψ θ μ 𝓕 d f).toReal * max B 1 ^ A, A, mul_nonneg hs (pow_nonneg (by positivity) _),
    fun h hh g => ?_⟩
  have h1 := (hC χS χT ω hω μ 𝓕 hμ f hl).2 g h
  have hW : GlobalTheory.Grow.height W h ≤ max B 1 := (hB h hh).trans (le_max_left _ _)
  have hW0 : 0 ≤ GlobalTheory.Grow.height W h := (GlobalTheory.Grow.height_pos W h).le
  have hV0 : 0 ≤ GlobalTheory.Grow.height V g := (GlobalTheory.Grow.height_pos V g).le
  calc ‖thetaKO ω g h f‖ = ‖ω (g, h) f 0‖ := rfl
    _ ≤ C * (sobO ψ θ μ 𝓕 d f).toReal * (GlobalTheory.Grow.height V g * GlobalTheory.Grow.height W h) ^ A := h1
    _ ≤ C * (sobO ψ θ μ 𝓕 d f).toReal * (GlobalTheory.Grow.height V g * max B 1) ^ A :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (mul_nonneg hV0 hW0)
          (mul_le_mul_of_nonneg_left hW hV0) _) hs
    _ = C * (sobO ψ θ μ 𝓕 d f).toReal * max B 1 ^ A * GlobalTheory.Grow.height V g ^ A := by ring

theorem thetaKO_le_quotHeight {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D}
    (hθ : IsInfFam θ) (ε : Bool) {S T : HSp D} {χS χT : (AE D)ˣ →* Circle} {ω : GlobalTheory.Grid.WRep S T}
    (hω : IsWeilDatumO ψ (GlobalTheory.Grid.sgn ε S) T χS χT (ω.toSgn ε)) {Φ : WO S T → ℂ}
    (hΦ : IsThetaFunO ψ (GlobalTheory.Grid.sgn ε S) T Φ) {K : Set (GA D T)} (hK : IsCompact K) :
    ∃ (C : ℝ) (A : ℕ), 0 ≤ C ∧ ∀ h ∈ K, ∀ g, ‖thetaKO ω g h Φ‖ ≤ C * GlobalTheory.Grow.quotHeight S g ^ A := by
  have e : ∀ g h, thetaKO ω g h Φ = thetaKO (ω.toSgn ε) ((GlobalTheory.Grid.ofSgn ε S).symm g) h Φ := fun g h => by
    show ω (g, h) Φ 0 = ω (GlobalTheory.Grid.ofSgn ε S ((GlobalTheory.Grid.ofSgn ε S).symm g), h) Φ 0
    rw [MulEquiv.apply_symm_apply]
  have hinv : ∀ h, ∀ γ ∈ GQ S, ∀ g, thetaKO ω (γ * g) h Φ = thetaKO ω g h Φ := fun h γ hγ g => by
    rw [e, e, map_mul]
    refine GlobalTheory.ChainOnto.ThetaFirstVar.thetaKO_left_fst hω hΦ h _ ?_ _
    rw [GlobalTheory.SgnIdent.mem_GQ_sgn, MulEquiv.apply_symm_apply]
    exact hγ
  obtain ⟨C, A, hC0, hC⟩ := thetaKO_le_unif hθ hω hΦ hK
  have hC' : ∀ h ∈ K, ∀ g, ‖thetaKO ω g h Φ‖ ≤ C * GlobalTheory.Grow.height S g ^ A := fun h hh g => by
    simp only [e]
    exact hC h hh _
  exact ⟨C * 2 ^ A, A, by positivity, fun h hh g => GlobalTheory.Grow.norm_le_quotHeight_pow (hinv h) (hC' h hh) g⟩

theorem approx_cusp : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → GlobalTheory.FunPr.Hypotheses₂ → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ i, i < D.R.m → ∀ Φ, IsThetaFunO R.ψ (GlobalTheory.Grid.neg (G.P (i + 1)).V) (G.P i).V Φ → ∀ φ, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType R.θ (G.P (i + 1)) φ → (∀ h, IntegrableOn (fun g => thetaKO (G.dn i).ω g h Φ * φ g) (G.mP (i + 1)).fd (G.mP (i + 1)).ν) → ∀ C : Set (GA D (G.P i).V), IsCompact C → ∀ ε : ℝ, 0 < ε → ∃ (n : ℕ) (F : Fin n → (G.P (i + 1)).Maps) (v : Fin n → SmT (G.P (i + 1)).M), (∀ l, F l ∈ (G.P (i + 1)).Cusp R.θ) ∧ (∀ l h, IntegrableOn (fun g => thetaKO (G.dn i).ω g h Φ * F l (v l) g) (G.mP (i + 1)).fd (G.mP (i + 1)).ν) ∧ ∀ h ∈ C, ‖(∫ g in (G.mP (i + 1)).fd, thetaKO (G.dn i).ω g h Φ * φ g ∂(G.mP (i + 1)).ν) - ∑ l, ∫ g in (G.mP (i + 1)).fd, thetaKO (G.dn i).ω g h Φ * F l (v l) g ∂(G.mP (i + 1)).ν‖ < ε := by
  intro _ hP D _ G₀ _ _ Pl0 T A Ks _ _ _ R G hB hG i hi Φ hΦ φ hφ hint C hC ε hε
  obtain ⟨hν, h𝓕⟩ := GlobalTheory.DownConv.MeasDat.haar_fd (hG.meas.P (i + 1) hi)
  obtain ⟨C1, A1, hC1, hK⟩ := thetaKO_le_quotHeight hB.inf true ((hG.arrows.dn i hi).weil) hΦ hC
  have hfin : (G.mP (i + 1)).ν (G.mP (i + 1)).fd < ⊤ :=
    GlobalTheory.CuspDecay.measure_lt_top GlobalTheory.Mem.VolFin.finVol _ _ _ hν h𝓕
  set X := C1 * ((G.mP (i + 1)).ν (G.mP (i + 1)).fd).toReal with hX
  have hX0 : 0 ≤ X := mul_nonneg hC1 ENNReal.toReal_nonneg
  set δ := ε / (2 * (X + 1)) with hδ
  have hδ0 : 0 < δ := div_pos hε (by positivity)
  obtain ⟨n, F, v, hF, happ⟩ := GlobalTheory.T.cusp_form_uniform_height_approx D R.θ hB.inf hP (G.P (i + 1)) φ hφ A1 δ hδ0
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
