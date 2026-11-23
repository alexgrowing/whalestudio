import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.OnePlaceKF
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Formalism.SharpRestriction.CuspSpanNormBounds.LeadMinorK
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.DegVand
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsNormalFormStabilizerMeasure
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MomAllP
import Formalism.LocalRingCardinality.DataTies
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MassBoundLowTypesSum

open BranchingSupport GlobalTheory.CellAmp GlobalTheory.Amp GlobalTheory.TypeAsm Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

noncomputable section

namespace GlobalTheory.LowTypeMass

section prelim

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

variable {k r : ℕ}

open scoped Classical in

theorem lintegral_rmul_of_measurable {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp]
    {z : Fin (2 * r + k + 1) → ℂ} {π : Mx k r → (Wp →L[ℂ] Wp)} {u : ℕ → ℝ}
    {μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)} (hS : SideG k r z π u μW μN μG νq) (F : Mx k r → ℝ≥0∞)
    (hF : Measurable ({x : Formalism.QuantumDeterminants.Mt k r | Matrix.of x ∈ GG k r}.piecewise
      (fun x : Formalism.QuantumDeterminants.Mt k r => F (Matrix.of x)) (fun _ => 0)))
    (hinv : ∀ s ∈ Formalism.QuantumDeterminants.Sset k r z, ∀ x ∈ GG k r, F (s * x) = F x)
    {g : Mx k r} (hg : g ∈ GG k r) :
    ∫⁻ x, F (Matrix.of x * g) ∂νq = ∫⁻ x, F (Matrix.of x) ∂νq := by
  classical
  obtain ⟨hz, hT, -, -, hW, hN, hG, hq⟩ := hS
  obtain ⟨hGG, hGH⟩ := GlobalTheory.unitaryGroup_matGroup_unimodular k r
  obtain ⟨hGH1, hGH2⟩ := hGH μG hG
  obtain ⟨hSG, hsub, hS1, hS2⟩ := GlobalTheory.muSof_isHaar k r z μW μN hz hT hW hN
  have hset : PI.QuotientSetting (GG k r) (Formalism.QuantumDeterminants.Sset k r z) μG (muSof μW μN) νq :=
    ⟨hGG, hSG, hsub, hGH1, hS1, hGH2, hS2, hq⟩
  obtain ⟨h0, h1⟩ := Formalism.FourierDecayAlt.P.DDSmoothness.muSof_facts hW hN
  have hae := Formalism.FourierDecayAlt.P.DDSmoothness.ae_UH_of_quot hG.2.2.1 h0 h1 hq
  set A : Set (Formalism.QuantumDeterminants.Mt k r) := {x | Matrix.of x ∈ GG k r} with hA
  have hval : ∀ x : Formalism.QuantumDeterminants.Mt k r, Matrix.of x ∈ GG k r →
      A.piecewise (fun x : Formalism.QuantumDeterminants.Mt k r => F (Matrix.of x)) (fun _ => 0) x = F (Matrix.of x) :=
    fun x hx => Set.piecewise_eq_of_mem _ _ _ hx
  have key := GlobalTheory.QuotRightInv.quotInv _ _ _ _ _ _ hset _ hF (fun s hs x hx => by
    rw [hval x hx]
    exact (hval (fun i j => (s * Matrix.of x) i j) (hGG.2.2.1 s (hsub hs) _ hx)).trans (hinv s hs _ hx)) g hg
  refine Eq.trans (lintegral_congr_ae (hae.mono fun x hx => ?_))
    (key.trans (lintegral_congr_ae (hae.mono fun x hx => hval x hx)))
  exact (hval (fun i j => (Matrix.of x * g) i j) (hGG.2.2.1 _ hx g hg)).symm

theorem norm_sq_sqrt_scaled {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] {t d : ℝ} (ht : 0 ≤ t)
    (hd : 0 ≤ d) (v : Wp) : ‖((Real.sqrt t * Real.sqrt d : ℝ) : ℂ) • v‖ ^ 2 = t * (d * ‖v‖ ^ 2) := by
  rw [norm_smul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs, mul_pow, Real.sq_sqrt ht, Real.sq_sqrt hd]
  ring

open scoped Classical in

theorem measurable_piecewise_mass {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    (z : Fin (2 * r + k + 1) → ℂ) (hz : Formalism.QuantumDeterminants.inWb k r z) (hT : 0 < Formalism.QuantumDeterminants.Tz k r z)
    (φ : (Fin (r + 1) → ℝ) → ℝ) (hφm : Measurable φ) (d : ℝ) (B : Mx k r → Wp) (hB : ContinuousOn B (GG k r)) :
    Measurable ({x : Formalism.QuantumDeterminants.Mt k r | Matrix.of x ∈ GG k r}.piecewise
      (fun x : Formalism.QuantumDeterminants.Mt k r => ENNReal.ofReal (φ (fun a => lenA k r z (Matrix.of x) a)) *
        ENNReal.ofReal (d * ‖B (Matrix.of x)‖ ^ 2)) (fun _ => 0)) := by
  classical
  set A : Set (Formalism.QuantumDeterminants.Mt k r) := {x | Matrix.of x ∈ GG k r} with hA
  have hAm : MeasurableSet A := by
    have := (Formalism.FourierDecayAlt.P.DDSmoothness.uh_measurableSet (k := k) (r := r)).compl
    convert this using 1
    ext x
    simp [hA]
  have hL : ContinuousOn (fun x : Formalism.QuantumDeterminants.Mt k r => fun a => lenA k r z (Matrix.of x) a) A :=
    continuousOn_pi.2 fun a => GlobalTheory.LengthCont.lenA_continuousOn k r z hz hT a
  have hLm : Measurable (A.piecewise (fun x : Formalism.QuantumDeterminants.Mt k r => fun a => lenA k r z (Matrix.of x) a)
      (fun _ => (0 : Fin (r + 1) → ℝ))) :=
    hL.measurable_piecewise continuousOn_const hAm
  have hBc : ContinuousOn (fun x : Formalism.QuantumDeterminants.Mt k r => d * ‖B (Matrix.of x)‖ ^ 2) A :=
    continuousOn_const.mul (hB.norm.pow 2)
  have hBm : Measurable (A.piecewise (fun x : Formalism.QuantumDeterminants.Mt k r => d * ‖B (Matrix.of x)‖ ^ 2) (fun _ => (0 : ℝ))) :=
    hBc.measurable_piecewise continuousOn_const hAm
  have heq : A.piecewise (fun x : Formalism.QuantumDeterminants.Mt k r => ENNReal.ofReal (φ (fun a => lenA k r z (Matrix.of x) a)) *
        ENNReal.ofReal (d * ‖B (Matrix.of x)‖ ^ 2)) (fun _ => 0) =
      A.indicator (fun x => ENNReal.ofReal (φ (A.piecewise
        (fun x : Formalism.QuantumDeterminants.Mt k r => fun a => lenA k r z (Matrix.of x) a) (fun _ => (0 : Fin (r + 1) → ℝ)) x)) *
        ENNReal.ofReal (A.piecewise (fun x : Formalism.QuantumDeterminants.Mt k r => d * ‖B (Matrix.of x)‖ ^ 2) (fun _ => (0 : ℝ)) x)) := by
    funext x
    by_cases hx : x ∈ A
    · simp [Set.piecewise, Set.indicator, hx]
    · simp [Set.piecewise, Set.indicator, hx]
  rw [heq]
  exact ((ENNReal.measurable_ofReal.comp (hφm.comp hLm)).mul (ENNReal.measurable_ofReal.comp hBm)).indicator hAm

theorem mass_low_types_bound (hH : Hyps) (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (lam : Fin (2 * r + k + 1) → ℝ) (u : ℕ → ℝ) (b bv ga h : ℝ) (q0 : ℕ)
    (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r))
    (R : (Fin (2 * r + k + 1) → ℤ) → Rep k r) (lb : ∀ ν, (R ν).H → Wp) (dg : (Fin (2 * r + k + 1) → ℤ) → ℝ)
    (hS : Setup lam u b bv ga h q0 z π μW μN μG νq R lb dg) (ν : Fin (2 * r + k + 1) → ℤ) (hν0 : n1 ν ≤ q0)
    (φ : (Fin (r + 1) → ℝ) → ℝ) (Bd : ℝ≥0∞) (hφm : Measurable φ) (hφ0 : ∀ y, 0 ≤ φ y)
    (hbd : ∀ (Q : Mx k r) (E : ∀ ν', Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Module.End ℂ (R ν').smSub),
      PI.UpqRep.IsCayleyU k r (PI.BesselPeriodGGP.eps48 k r) Q →
      (∀ ν', n1 ν' ≤ q0 → (R ν').IsE Q (E ν') ∧ Formalism.REAL.GlRel (E ν')) →
      ∀ w : (R ν).smSub, Lev (PI.BesselPeriodGGP.eps48 k r) (E ν) (fun a => lam a + (ν a : ℝ)) 0 w → ‖w‖ = 1 →
      ∫⁻ x, ENNReal.ofReal (φ (fun a => lenA k r z (Matrix.of x) a) *
        (dg ν * ‖lb ν ((R ν).σ (Matrix.of x) w)‖ ^ 2)) ∂νq ≤ Bd)
    (w : (R ν).H)
    (hw : PI.UpqRep.IsLowUnitH k r (PI.BesselPeriodGGP.eps48 k r) (fun a => lam a + (ν a : ℝ)) (R ν).σ w) :
    ∫⁻ x, ENNReal.ofReal (φ (fun a => lenA k r z (Matrix.of x) a) *
      (dg ν * ‖lb ν ((R ν).σ (Matrix.of x) w)‖ ^ 2)) ∂νq ≤ Bd := by
  classical
  have hK : PI.KFinSmooth := hH.1.2.2.1
  have hNum := hS.1
  have hFam := hS.2.1
  have hSide := hS.2.2.1
  have hSF := hS.2.2.2
  have hk : 1 ≤ k := hNum.1
  obtain ⟨Q, hQ, hw1, hwL⟩ := hw
  have hQu : IsUnit Q := hQ.1.1
  have hE : ∀ ν', ∃ E : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Module.End ℂ (R ν').smSub,
      n1 ν' ≤ q0 → (R ν').IsE Q E ∧ Formalism.REAL.GlRel E := by
    intro ν'
    by_cases h' : n1 ν' ≤ q0
    · obtain ⟨E, hE⟩ := GlobalTheory.smooth_gl_module hK k r _ _ (R ν') (hFam ν' h') Q hQu
      exact ⟨E, fun _ => hE⟩
    · exact ⟨fun _ _ => 0, fun h'' => absurd h'' h'⟩
  choose E hE using hE
  have hbd' := hbd Q E hQ hE
  have hDS := hFam ν hν0
  have hD := (GlobalTheory.CayleyChoice.cayley_exists_and_any k r).2 _ _ _ hDS Q hQ
  obtain ⟨hG, -, hlen, hmeas⟩ := GlobalTheory.quotMeas_ae_mem_and_measurable hK k r _ _ (R ν) Wp z π u μW μN μG νq hDS hSide
  obtain ⟨hBeL, hdg, -⟩ := hSF ν hν0
  obtain ⟨hmul, -, -, hsm, -⟩ := GlobalTheory.rep_basic_of_isDS hK k r _ _ (R ν) hDS
  have hT : 0 < Formalism.QuantumDeterminants.Tz k r z := hSide.2.1
  have hsmS : ∀ S : Submodule ℂ (R ν).H, FiniteDimensional ℂ S →
      PI.UpqRep.IsKStableOn (PI.BesselPeriodGGP.eps48 k r) (fun g => (R ν).σ (Q⁻¹ * g * Q)) S → S ≤ (R ν).smSub :=
    fun S h1 h2 v hv => ((GlobalTheory.CompactStable.kStable_smooth_and_stable hK k r _ _ (R ν) hDS Q hQ S h1 h2).1 v hv).2
  have hlenv : AEMeasurable (fun x : Formalism.QuantumDeterminants.Mt k r => fun a => lenA k r z (Matrix.of x) a) νq :=
    aemeasurable_pi_iff.2 hlen
  rcases eq_or_ne Bd ⊤ with rfl | hBd
  · exact le_top
  have hCB : ENNReal.ofReal Bd.toReal = Bd := ENNReal.ofReal_toReal hBd
  rw [← hCB]
  rw [← hCB] at hbd'
  have key := GlobalTheory.MomOne.lintegral_le_of_highest (m := νq) hD.2.2.1 _ (R ν).smSub hsmS
    (fun v x => ((Real.sqrt (φ (fun a => lenA k r z (Matrix.of x) a)) * Real.sqrt (dg ν) : ℝ) : ℂ) •
      lb ν ((R ν).σ (Matrix.of x) v))
    ?_ ?_ ?_ ?_ Bd.toReal ENNReal.toReal_nonneg ?_ w hwL hw1
  · simpa only [norm_sq_sqrt_scaled (hφ0 _) hdg.le] using key
  · intro v hv v' hv'
    filter_upwards [hG] with x hx
    simp only [Pi.add_apply]
    rw [map_add, hBeL.1.1 _ (hsm _ hx v hv) _ (hsm _ hx v' hv'), smul_add]
  · intro c v hv
    filter_upwards [hG] with x hx
    simp only [Pi.smul_apply]
    rw [map_smul, hBeL.1.2.1 c _ (hsm _ hx v hv), smul_comm]
  · intro v hv
    refine (Complex.continuous_ofReal.comp_aestronglyMeasurable ?_).smul (hmeas (lb ν) hBeL.1 v hv)
    exact (((hφm.comp_aemeasurable hlenv).sqrt).mul_const _).aestronglyMeasurable
  · intro g hg v hv
    obtain ⟨hgG, hgU⟩ := GlobalTheory.MomOne.conj_back hQ hg
    simp only [norm_sq_sqrt_scaled (hφ0 _) hdg.le]
    have hBc := (GlobalTheory.cwCont_continuousOn_hasDerivAt hK k r _ _ (R ν) hDS Wp (lb ν) hBeL.1.1 hBeL.1.2.1
      hBeL.1.2.2.2 v hv).1
    have hF := measurable_piecewise_mass z hSide.1 hT φ hφm (dg ν) (fun x => lb ν ((R ν).σ x v)) hBc
    have := lintegral_rmul_of_measurable hSide
      (fun x => ENNReal.ofReal (φ (fun a => lenA k r z x a)) * ENNReal.ofReal (dg ν * ‖lb ν ((R ν).σ x v)‖ ^ 2))
      hF ?_ hgG
    · have e1 : ∀ x : Formalism.QuantumDeterminants.Mt k r, ENNReal.ofReal (φ (fun a => lenA k r z (Matrix.of x) a) *
          (dg ν * ‖lb ν ((R ν).σ (Matrix.of x) v)‖ ^ 2)) =
          ENNReal.ofReal (φ (fun a => lenA k r z (Matrix.of x) a)) *
            ENNReal.ofReal (dg ν * ‖lb ν ((R ν).σ (Matrix.of x) v)‖ ^ 2) :=
        fun x => ENNReal.ofReal_mul (hφ0 _)
      simp only [e1]
      rw [← this]
      refine lintegral_congr_ae ?_
      filter_upwards [hG] with x hx
      simp only [GlobalTheory.MomOne.lenA_mul_unitary z _ hgU, hmul _ hx _ hgG]
      rw [ENNReal.ofReal_mul (hφ0 _)]
    · intro s hs x hx
      have e := (GlobalTheory.TensLen.lengths k r z hSide.1 hT _ hx).2.2.2 s hs
      obtain ⟨h', hh, m, hmN, rfl⟩ := hs
      obtain ⟨u₀, hπ⟩ := hSide.2.2.1
      have hsG : h' * m ∈ GG k r := Formalism.FourierDecayAlt.P.DDSmoothness.uh_mul hh.1 hmN.1
      beta_reduce
      simp only [e]
      rw [hmul _ hsG _ hx, hBeL.1.2.2.1 h' hh m hmN _ (hsm _ hx v hv), norm_smul,
        Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.psi_norm, one_mul, Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.piW_unitary hT hπ h' hh]
  · intro S hfd hst hcd v hv hv1 hwt
    simp only [norm_sq_sqrt_scaled (hφ0 _) hdg.le]
    have hvs : v ∈ (R ν).sm := hsmS S hfd hst hv
    have hLev := GlobalTheory.MomOne.lev_zero_of_wt hH hk hDS hQ (hE ν hν0).1 S hfd hst hcd ⟨v, hvs⟩ hv hwt
    have hv1' : ‖(⟨v, hvs⟩ : (R ν).smSub)‖ = 1 := hv1
    exact hbd' ⟨v, hvs⟩ hLev hv1'

end prelim

section main

open BranchingSupport GlobalTheory.CellAmp GlobalTheory.Amp GlobalTheory.TypeAsm Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

theorem mass_low : Hyps → GlobalTheory.Dec.LowKMultOne → ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (lam : Fin (2 * r + k + 1) → ℝ) (u : ℕ → ℝ) (b bv ga h : ℝ) (q0 : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (π : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (Wp →L[ℂ] Wp)) (μW μN μG νq : Measure (Mt k r)) (R : (Fin (2 * r + k + 1) → ℤ) → Rep k r) (lb : ∀ ν, (R ν).H → Wp) (dg : (Fin (2 * r + k + 1) → ℤ) → ℝ), Setup lam u b bv ga h q0 z π μW μN μG νq R lb dg → ∀ ν, n1 ν ≤ q0 → ∀ (φ : (Fin (r + 1) → ℝ) → ℝ) (Bd : ℝ≥0∞), Measurable φ → (∀ y, 0 ≤ φ y) → (∀ (Q : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (E : ∀ ν', Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Module.End ℂ (R ν').smSub), PI.UpqRep.IsCayleyU k r (PI.BesselPeriodGGP.eps48 k r) Q → (∀ ν', n1 ν' ≤ q0 → (R ν').IsE Q (E ν') ∧ Formalism.REAL.GlRel (E ν')) → ∀ w : (R ν).smSub, Lev (PI.BesselPeriodGGP.eps48 k r) (E ν) (fun a => lam a + (ν a : ℝ)) 0 w → ‖w‖ = 1 → ∫⁻ x, ENNReal.ofReal (φ (fun a => lenA k r z (Matrix.of x) a) * (dg ν * ‖lb ν ((R ν).σ (Matrix.of x) w)‖ ^ 2)) ∂νq ≤ Bd) → ∀ w : (R ν).H, PI.UpqRep.IsLowUnitH k r (PI.BesselPeriodGGP.eps48 k r) (fun a => lam a + (ν a : ℝ)) (R ν).σ w → ∫⁻ x, ENNReal.ofReal (φ (fun a => lenA k r z (Matrix.of x) a) * (dg ν * ‖lb ν ((R ν).σ (Matrix.of x) w)‖ ^ 2)) ∂νq ≤ Bd :=
  fun hH _ k r Wp _ _ _ _ lam u b bv ga h q0 z π μW μN μG νq R lb dg hS ν hν0 φ Bd hφm hφ0 hbd w hw =>
    mass_low_types_bound hH k r Wp lam u b bv ga h q0 z π μW μN μG νq R lb dg hS ν hν0 φ Bd hφm hφ0 hbd w hw

end main

end GlobalTheory.LowTypeMass
