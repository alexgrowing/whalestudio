import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MatrixOfBesselTwoSidedAction
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ExistsIsFolnerUWset
import Formalism.FormalDegreeBessel.FinalG
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselSubgroupsClosedUnitaryWCompactStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnimodularBesselSubgroupsUWNStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.WeilFormulaBesselUnitaryIntegrableStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselSubgroupRepTwistedIsUnitaryRepStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselFormCoeffProductFubiniIntegrableStatement

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

namespace GlobalTheory.SgInf.AbsConv

variable {k r : ℕ}

theorem measurable_lmul : Measurable (fun p : Mt k r × Mt k r => lmulM (Matrix.of p.2 : Mat k r) p.1) := by
  apply Continuous.measurable
  refine continuous_pi fun i => continuous_pi fun j => ?_
  simp only [lmulM, Matrix.mul_apply, Matrix.of_apply]
  fun_prop

theorem lintegral_lt_top {μG μS ν : Measure (Mt k r)} [SFinite μG] [SFinite μS] [SFinite ν]
    {S : Set (Mat k r)} (hq : IsQuotMeas μG μS ν)
    (hmap : μG = (ν.prod μS).map (fun p : Mt k r × Mt k r => lmulM (Matrix.of p.2 : Mat k r) p.1))
    (hS : ∀ᵐ s ∂μS, (Matrix.of s : Mat k r) ∈ S)
    (hR : ∀ s ∈ S, μS.map (rmulM s) = μS)
    {φ : Mt k r → ENNReal} (hφ : Measurable φ)
    (hfin : ∫⁻ g, ∫⁻ t, φ g * φ (lmulM (Matrix.of t : Mat k r) g) ∂μS ∂μG < ⊤)
    {Wn : Mt k r → ENNReal} (hWG : AEMeasurable Wn μG) (hWν : AEMeasurable Wn ν)
    (hinv : ∀ᵐ x ∂ν, ∀ s ∈ S, Wn (lmulM s x) = Wn x)
    (hl2 : ∫⁻ x, Wn x ^ 2 ∂ν < ⊤) :
    ∫⁻ g, φ g * Wn g ∂μG < ⊤ := by
  have hmeas2 : Measurable (fun p : Mt k r × Mt k r => φ (lmulM (Matrix.of p.2 : Mat k r) p.1)) :=
    hφ.comp GlobalTheory.SgInf.AbsConv.measurable_lmul
  have hsec : ∀ x : Mt k r, Measurable (fun t : Mt k r => φ (lmulM (Matrix.of t : Mat k r) x)) :=
    fun x => hmeas2.comp measurable_prodMk_left
  obtain ⟨Φ, hΦdef⟩ : ∃ Φ : Mt k r → ENNReal,
      Φ = fun x => ∫⁻ t, φ (lmulM (Matrix.of t : Mat k r) x) ∂μS := ⟨_, rfl⟩
  have hΦx : ∀ x, Φ x = ∫⁻ t, φ (lmulM (Matrix.of t : Mat k r) x) ∂μS := fun x => by rw [hΦdef]
  have hΦm : Measurable Φ := by rw [hΦdef]; exact hmeas2.lintegral_prod_right'

  have hΦinv : ∀ s ∈ S, ∀ x, Φ (lmulM s x) = Φ x := by
    intro s hs x
    have hrm : Measurable (rmulM s : Mt k r → Mt k r) := (continuous_rmulM s).measurable
    rw [hΦx, hΦx]
    conv_rhs => rw [← hR s hs]
    rw [lintegral_map (hsec x) hrm]
    refine lintegral_congr fun t => ?_
    congr 1
    change (Matrix.of t * (s * Matrix.of x) : Mat k r) = Matrix.of t * s * Matrix.of x
    rw [Matrix.mul_assoc]

  have hΦ2 : ∫⁻ x, Φ x * Φ x ∂ν < ⊤ := by
    have hF : Measurable (fun g : Mt k r => φ g * Φ g) := hφ.mul hΦm
    have e1 : ∫⁻ g, ∫⁻ t, φ g * φ (lmulM (Matrix.of t : Mat k r) g) ∂μS ∂μG
        = ∫⁻ g, φ g * Φ g ∂μG := by
      refine lintegral_congr fun g => ?_
      rw [lintegral_const_mul _ (hsec g), hΦx]
    have e2 : ∫⁻ g, φ g * Φ g ∂μG = ∫⁻ x, ∫⁻ s, φ (lmulM (Matrix.of s : Mat k r) x) *
        Φ (lmulM (Matrix.of s : Mat k r) x) ∂μS ∂ν := hq _ hF
    have e3 : ∀ x, ∫⁻ s, φ (lmulM (Matrix.of s : Mat k r) x) * Φ (lmulM (Matrix.of s : Mat k r) x) ∂μS
        = Φ x * Φ x := by
      intro x
      rw [lintegral_congr_ae (g := fun s => φ (lmulM (Matrix.of s : Mat k r) x) * Φ x) ?_]
      · rw [lintegral_mul_const _ (hsec x), ← hΦx]
      · filter_upwards [hS] with s hs
        rw [hΦinv _ hs x]
    calc ∫⁻ x, Φ x * Φ x ∂ν
        = ∫⁻ x, ∫⁻ s, φ (lmulM (Matrix.of s : Mat k r) x) * Φ (lmulM (Matrix.of s : Mat k r) x) ∂μS ∂ν :=
          lintegral_congr fun x => (e3 x).symm
      _ = ∫⁻ g, φ g * Φ g ∂μG := e2.symm
      _ = _ := e1.symm
      _ < ⊤ := hfin

  have hWmm : Measurable (hWν.mk Wn) := hWν.measurable_mk
  have h1 : ∀ᵐ x ∂ν, (∀ s ∈ S, Wn (lmulM s x) = Wn x) ∧ Wn x = hWν.mk Wn x :=
    hinv.and hWν.ae_eq_mk
  have h1' : ∀ᵐ p ∂(ν.prod μS), (∀ s ∈ S, Wn (lmulM s p.1) = Wn p.1) ∧ Wn p.1 = hWν.mk Wn p.1 :=
    Measure.quasiMeasurePreserving_fst.ae h1
  have h2 : ∀ᵐ p ∂(ν.prod μS), (Matrix.of p.2 : Mat k r) ∈ S :=
    Measure.quasiMeasurePreserving_snd.ae hS
  have hA : AEMeasurable (fun g => φ g * Wn g)
      ((ν.prod μS).map (fun p : Mt k r × Mt k r => lmulM (Matrix.of p.2 : Mat k r) p.1)) := by
    rw [← hmap]; exact hφ.aemeasurable.mul hWG
  have hmain : ∫⁻ g, φ g * Wn g ∂μG = ∫⁻ x, Φ x * hWν.mk Wn x ∂ν := by
    rw [hmap, lintegral_map' hA GlobalTheory.SgInf.AbsConv.measurable_lmul.aemeasurable]
    rw [lintegral_congr_ae (g := fun p : Mt k r × Mt k r =>
      φ (lmulM (Matrix.of p.2 : Mat k r) p.1) * hWν.mk Wn p.1) ?_]
    · rw [lintegral_prod (fun p : Mt k r × Mt k r => φ (lmulM (Matrix.of p.2 : Mat k r) p.1) * hWν.mk Wn p.1)
        (hmeas2.mul (hWmm.comp measurable_fst)).aemeasurable]
      refine lintegral_congr fun x => ?_
      dsimp only
      rw [lintegral_mul_const _ (hsec x), ← hΦx]
    · filter_upwards [h1', h2] with p hp1 hp2
      simp only [hp1.1 _ hp2, hp1.2]

  have hpt : ∀ x, Φ x * hWν.mk Wn x ≤ hWν.mk Wn x ^ 2 + Φ x * Φ x := by
    intro x
    rcases le_total (Φ x) (hWν.mk Wn x) with h | h
    · calc Φ x * hWν.mk Wn x ≤ hWν.mk Wn x * hWν.mk Wn x := by gcongr
        _ = hWν.mk Wn x ^ 2 := (sq _).symm
        _ ≤ _ := le_self_add
    · calc Φ x * hWν.mk Wn x ≤ Φ x * Φ x := by gcongr
        _ ≤ _ := le_add_self
  have hW2 : ∫⁻ x, hWν.mk Wn x ^ 2 ∂ν = ∫⁻ x, Wn x ^ 2 ∂ν :=
    lintegral_congr_ae (hWν.ae_eq_mk.symm.fun_comp (· ^ 2))
  rw [hmain]
  calc ∫⁻ x, Φ x * hWν.mk Wn x ∂ν ≤ ∫⁻ x, hWν.mk Wn x ^ 2 + Φ x * Φ x ∂ν := lintegral_mono hpt
    _ = ∫⁻ x, hWν.mk Wn x ^ 2 ∂ν + ∫⁻ x, Φ x * Φ x ∂ν := lintegral_add_left (hWmm.pow_const 2) _
    _ < ⊤ := by rw [hW2]; exact ENNReal.add_lt_top.2 ⟨hl2, hΦ2⟩

theorem enorm_star' (a : ℂ) : ‖star a‖ₑ = ‖a‖ₑ := by
  rw [enorm_eq_nnnorm, enorm_eq_nnnorm, nnnorm_star]

theorem coef_inv_mul {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {σ : Mat k r → (H →L[ℂ] H)} (hσ : IsURepOn (GG k r) σ) (w : H) {y g : Mat k r}
    (hy : y ∈ GG k r) (hyi : y⁻¹ ∈ GG k r) (hg : g ∈ GG k r) :
    coef σ w w (y⁻¹ * g) = coef σ w (σ y w) g := by
  obtain ⟨⟨h1, hmul⟩, hiso, -⟩ := hσ
  have hyy : y * y⁻¹ = 1 := Matrix.mul_nonsing_inv y (isUnit_det_of_mem_GG hy)
  have key : ∀ v : H, σ y (σ y⁻¹ v) = v := by
    intro v
    have := congrArg (fun T : H →L[ℂ] H => T v) (hmul y hy y⁻¹ hyi)
    simp only [hyy, h1, ContinuousLinearMap.comp_apply, ContinuousLinearMap.one_apply] at this
    exact this.symm
  have hinner : ∀ u v : H, ⟪σ y u, σ y v⟫_ℂ = ⟪u, v⟫_ℂ := by
    intro u v
    let L : H →ₗᵢ[ℂ] H := { toLinearMap := (σ y).toLinearMap, norm_map' := hiso y hy }
    exact L.inner_map_map u v
  simp only [coef]
  rw [hmul y⁻¹ hyi g hg, ContinuousLinearMap.comp_apply, ← hinner w (σ y⁻¹ (σ g w)), key]

theorem norm_equiv {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    {z : Fin (2 * r + k + 1) → ℂ} {c : Fin r → ℂ} {π : Mat k r → (Wp →L[ℂ] Wp)}
    (hπ : IsURepOn (UWset k r z) π) {W : Mat k r → Wp} (hW : IsSPsiEquiv z (psiGen k r z c) π W)
    {s x : Mat k r} (hs : s ∈ Sset k r z) (hx : x ∈ GG k r) : ‖W (s * x)‖ₑ = ‖W x‖ₑ := by
  obtain ⟨h, hh, m, hm, rfl⟩ := hs
  have hx' : x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) := hx
  rw [hW h hh m hm x hx']
  obtain ⟨-, hiso, -⟩ := hπ
  have hψ : ‖psiGen k r z c m‖ = 1 := by simp [psiGen, Complex.norm_exp]
  have hn : ‖psiGen k r z c m • π h (W x)‖ = ‖W x‖ := by rw [norm_smul, hψ, one_mul, hiso h hh]
  simp only [enorm_eq_nnnorm]
  congr 1
  exact NNReal.eq hn

theorem integrable_coef_smul : ∀ (k r : ℕ) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] [CompleteSpace Wp] (σ : Mat k r → (H →L[ℂ] H)) (w : H) (a : ℝ) (μG : Measure (Mt k r)) (d : ℝ) (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (π : Mat k r → (Wp →L[ℂ] Wp)) (μS : Measure (Mt k r)), Std σ w a μG d → Side z π μS → ∀ ν : Measure (Mt k r), IsQuotMeas μG μS ν → ∀ W : Mat k r → Wp, AEStronglyMeasurable (fun x : Mt k r => W (Matrix.of x)) μG → AEStronglyMeasurable (fun x : Mt k r => W (Matrix.of x)) ν → IsSPsiEquiv z (psiGen k r z c) π W → l2SG ν W < ⊤ → ∀ y ∈ GG k r, Integrable (fun g : Mt k r => star (coef σ w w (y⁻¹ * Matrix.of g)) • W (Matrix.of g)) μG := by
  classical
  intro k r H _ _ _ Wp _ _ _ _ σ w a μG d z c π μS hStd hSide ν hq W hWG hWν hW hl2 y hy
  have hint := GlobalTheory.T.besselForm_coeff_product_fubini_integrable k r σ w a μG d z c π μS hStd hSide
  obtain ⟨-, hσ, -, -, hHG, -, -, -, -⟩ := hStd
  obtain ⟨hz, hT, hπ, hHS, -⟩ := hSide
  have hcl := GlobalTheory.T.bessel_subgroups_closed_unitaryW_compact k r z hz hT
  have hUS : IsUnimod (Sset k r z) μS := (GlobalTheory.T.unimodular_besselSubgroups_UW_N k r z hz hT μS).1 hHS
  obtain ⟨hνσ, hνG, hmap, -, -⟩ := GlobalTheory.T.weil_formula_besselUnitary_integrable k r (Sset k r z) μG μS ν hcl.2.2.2.1 hHG hHS hUS hq
  have : SigmaFinite μG := hHG.1
  have : SigmaFinite μS := hHS.1
  have : SigmaFinite ν := hνσ
  have hyi : y⁻¹ ∈ GG k r := hcl.1.2.2.2.2 y hy
  have hone : (1 : Mat k r) ∈ GG k r := hcl.1.2.2.1
  have hwD : w ∈ DD σ w := by
    have := mem_DD σ w hone
    rwa [hσ.1.1, ContinuousLinearMap.one_apply] at this
  have hyD : σ y w ∈ DD σ w := mem_DD σ w hy
  have hint2 := hint w hwD w hwD (σ y w) hyD (σ y w) hyD

  have hof : Continuous (fun x : Mt k r => (Matrix.of x : Mat k r)) := continuous_id
  set GGset : Set (Mt k r) := {x | (Matrix.of x : Mat k r) ∈ GG k r} with hGGdef
  have hGGmeas : MeasurableSet GGset := (hcl.1.2.1.preimage hof).measurableSet
  have hGae : ∀ᵐ x ∂μG, x ∈ GGset := ae_iff.2 hHG.2.2.1
  have hc0 : ContinuousOn (fun g : Mt k r => σ (Matrix.of g) w) GGset :=
    (hσ.2.2 w).comp hof.continuousOn (fun x hx => hx)
  have hcc : ContinuousOn (fun g : Mt k r => coef σ w (σ y w) (Matrix.of g)) GGset := by
    simp only [coef]
    exact continuousOn_const.inner hc0

  obtain ⟨φ, hφdef⟩ : ∃ φ : Mt k r → ENNReal,
      φ = GGset.piecewise (fun g => ‖coef σ w (σ y w) (Matrix.of g)‖ₑ) 0 := ⟨_, rfl⟩
  have hφm : Measurable φ := by
    rw [hφdef]
    exact ContinuousOn.measurable_piecewise (continuous_enorm.comp_continuousOn hcc)
      continuousOn_const hGGmeas
  have hφle : ∀ g, φ g ≤ ‖coef σ w (σ y w) (Matrix.of g)‖ₑ := by
    intro g
    rw [hφdef]
    by_cases hg : g ∈ GGset
    · simp [Set.piecewise, hg]
    · simp [Set.piecewise, hg]
  have hfin : ∫⁻ g, ∫⁻ t, φ g * φ (lmulM (Matrix.of t : Mat k r) g) ∂μS ∂μG < ⊤ := by
    have hfi := hint2.hasFiniteIntegral
    unfold HasFiniteIntegral at hfi
    refine lt_of_le_of_lt ?_ hfi
    refine le_trans (lintegral_mono fun g => lintegral_mono fun t => ?_) (lintegral_prod _ hint2.aestronglyMeasurable.enorm).symm.le
    dsimp only
    rw [enorm_mul, GlobalTheory.SgInf.AbsConv.enorm_star']
    exact mul_le_mul' (hφle g) (hφle _)
  have hinv : ∀ᵐ x ∂ν, ∀ s ∈ Sset k r z,
      ‖W (Matrix.of (lmulM s x))‖ₑ = ‖W (Matrix.of x)‖ₑ := by
    have : ∀ᵐ x ∂ν, x ∈ GGset := ae_iff.2 hνG
    filter_upwards [this] with x hx s hs
    exact GlobalTheory.SgInf.AbsConv.norm_equiv hπ hW hs hx
  have hl2' : ∫⁻ x, ‖W (Matrix.of x)‖ₑ ^ 2 ∂ν < ⊤ := by
    simpa only [l2SG, enorm_eq_nnnorm] using hl2
  have hbound := GlobalTheory.SgInf.AbsConv.lintegral_lt_top (S := Sset k r z) hq hmap (ae_iff.2 hHS.2.2.1)
    hUS.1 hφm hfin hWG.enorm hWν.enorm hinv hl2'

  have hcm : AEStronglyMeasurable (fun g : Mt k r => star (coef σ w (σ y w) (Matrix.of g))) μG := by
    rw [← Measure.restrict_eq_self_of_ae_mem hGae]
    exact hcc.star.aestronglyMeasurable hGGmeas
  have hsm : AEStronglyMeasurable
      (fun g : Mt k r => star (coef σ w (σ y w) (Matrix.of g)) • W (Matrix.of g)) μG := hcm.smul hWG
  have hae : (fun g : Mt k r => star (coef σ w w (y⁻¹ * Matrix.of g)) • W (Matrix.of g))
      =ᵐ[μG] (fun g : Mt k r => star (coef σ w (σ y w) (Matrix.of g)) • W (Matrix.of g)) := by
    filter_upwards [hGae] with g hg
    rw [GlobalTheory.SgInf.AbsConv.coef_inv_mul (g := Matrix.of g) hσ w hy hyi hg]
  refine Integrable.congr ⟨hsm, ?_⟩ hae.symm
  show ∫⁻ g, ‖star (coef σ w (σ y w) (Matrix.of g)) • W (Matrix.of g)‖ₑ ∂μG < ⊤
  refine lt_of_eq_of_lt (lintegral_congr_ae ?_) hbound
  filter_upwards [hGae] with g hg
  rw [enorm_smul, GlobalTheory.SgInf.AbsConv.enorm_star', hφdef, Set.piecewise_eq_of_mem _ _ _ hg]

end GlobalTheory.SgInf.AbsConv
