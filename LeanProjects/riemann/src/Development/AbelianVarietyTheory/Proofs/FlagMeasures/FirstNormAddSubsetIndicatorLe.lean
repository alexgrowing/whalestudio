import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.OnePlaceKF
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Formalism.SharpRestriction.CuspSpanNormBounds.LeadMinorK
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.DegVand
import Formalism.LocalRingCardinality.DataTies
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.TensorMomentEstimate
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.FamilySetupBesselGrowth
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.AbsCoordLeOfLOneNormLe
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.NumericalFamilyShapeGaps
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.HaarEqSmul
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.TensorDecompositionInjectiveParameters
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.PieriTensorDecomposition
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsFRepExteriorPowerStandardRep
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.DiscreteSeriesUnitarySmoothBasic
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.LenEqOfUnitriangular
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HaarLieIsHaarOnUnipotentRadicalStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.QuotientMeasureAeMemAndMeasurableBesselModel
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselPeriodPositivityStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TorusNormaliserBessel
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BlockProjectionBesselStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AmplitudesRelevantCellMonomialRepStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselMapPairingBoundStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsUnitaryTorusScaleBesselCharacter
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TorusCommutesWithUnipotentStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MomentPieriNumericsOfSizeHypsStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FormalDegreeProportional
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DegreeNearParameterBoundStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AmplitudeSizeConsequencesOfWordIndependentHyps
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MassBoundLowTypesAltBis
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.PairingEqLeadingMinor
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FlagWedgeFixedAndLengthEqProdDistancesStatement

open BranchingSupport GlobalTheory.CellAmp GlobalTheory.Amp Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.CellMinorLine

open GlobalTheory.BesselMove

variable {k r q0 : ℕ}

theorem urep_of_isDS {R : Rep k r} {ε mu} (h : R.IsDS ε mu) : IsURepOn (GG k r) R.σ :=
  ⟨⟨(Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.sigma_facts h.2).1, fun _ ha _ hb => Formalism.FourierDecayAlt.P.TranslationBesselVanishing.sigma_mul h.2 ha hb⟩,
    (Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.sigma_facts h.2).2, fun v => Formalism.FourierDecayAlt.P.S3dx4.sigma_contOn h.2 v⟩

theorem cmp_wedge_eigen {n l : ℕ} (g : Matrix (Fin n) (Fin n) ℂ) (f : Fin l → Fin n → ℂ) (s : Fin l → ℂ)
    (h : ∀ a, g *ᵥ f a = s a • f a) : cmp l g *ᵥ wedge f = (∏ a, s a) • wedge f := by
  rw [GlobalTheory.TensLen.cmp_mulVec_wedge]
  funext I
  simp only [h, wedge, Pi.smul_apply, smul_eq_mul]
  exact Matrix.det_mul_row s (Matrix.of fun a b : Fin l => f b (I.1.orderEmbOfFin I.2 a))

theorem kappa_move {ι κ Wp : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [AddCommGroup Wp]
    [Module ℂ Wp] {ρ : MM k r → Matrix ι ι ℂ} {R : Rep k r} {RI : κ → Rep k r}
    {io : ∀ I, ι → (RI I).H → R.H} {pr : ∀ I, ι → R.H → (RI I).H} (hT : TensRaw ρ R RI io pr)
    (hR : IsURepOn (GG k r) R.σ) {g : MM k r} (hg : g ∈ GG k r) {om : ι → ℂ} {S : ℂ} (hS : ρ g *ᵥ om = S • om)
    {l : R.H → Wp} (hl : ∀ (a : ℂ), ∀ v ∈ R.sm, l (a • v) = a • l v) (I : κ) {lI : (RI I).H → Wp} {κ₀ : ℂ}
    (hκ : ∀ v ∈ R.sm, lI (∑ c, pr I c (tm R om v c)) = κ₀ • l v) :
    ∀ v ∈ R.sm, lI ((RI I).σ g (∑ c, pr I c (tm R om v c))) = (S * κ₀) • l (R.σ g v) := by
  intro v hv
  have hgv := sig_sm hR hg hv
  rw [← hT.pr_eq I g hg (tm R om v) (fun c => Formalism.FourierDecayAlt.P.DDSmoothness.smooth_smul _ hv)]
  have e : act ρ R g (tm R om v) = tm R om (S • R.σ g v) := by
    funext i
    have := congrFun hS i
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at this
    simp only [act, tm, map_smul, smul_smul, ← Finset.sum_smul, this, mul_comm]
  rw [e, hκ _ (Formalism.FourierDecayAlt.P.DDSmoothness.smooth_smul _ hgv), hl _ _ hgv, smul_smul, mul_comm]

theorem mass_move {Wp : Type} [NormedAddCommGroup Wp] {R : Rep k r} (hR : IsURepOn (GG k r) R.σ) {t : MM k r}
    (ht : t ∈ GG k r) {ν : Measure (Mt k r)} {l : R.H → Wp} {d : ℝ} (hd : 0 < d) {w : R.H}
    (hae : ∀ᵐ x ∂(ν.map fun x => fun i j => (t⁻¹ * Matrix.of x) i j), Matrix.of x ∈ GG k r)
    (h : ∫⁻ x, ENNReal.ofReal (1 * (d * ‖l (R.σ (Matrix.of x) w)‖ ^ 2))
      ∂(ν.map fun x => fun i j => (t⁻¹ * Matrix.of x) i j) = ENNReal.ofReal (‖w‖ ^ 2)) :
    l2SG ν (fun g => l (R.σ t⁻¹ (R.σ g w))) = ENNReal.ofReal (‖w‖ ^ 2 / d) := by
  change ∀ᵐ x ∂(ν.map (leftE ht)), _ at hae
  change ∫⁻ x, _ ∂(ν.map (leftE ht)) = _ at h
  rw [lintegral_map_equiv] at h
  have hae' : ∀ᵐ x ∂ν, Matrix.of x ∈ GG k r := by
    filter_upwards [ae_of_ae_map (leftE ht).measurable.aemeasurable hae] with x hx
    have := mul_mem' ht (h := t⁻¹ * Matrix.of x) hx
    rwa [mic ht] at this
  have h2 : ENNReal.ofReal d * l2SG ν (fun g => l (R.σ t⁻¹ (R.σ g w))) = ENNReal.ofReal (‖w‖ ^ 2) := by
    rw [← h, l2SG, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_congr_ae (hae'.mono fun x hx => ?_)
    show _ = ENNReal.ofReal (1 * (d * ‖l (R.σ (t⁻¹ * Matrix.of x) w)‖ ^ 2))
    rw [one_mul, sig_mul hR (inv_mem ht) hx, ENNReal.ofReal_mul hd.le, ENNReal.ofReal_pow (norm_nonneg _),
      ofReal_norm_eq_enorm]
    rfl
  have h0 : ENNReal.ofReal d ≠ 0 := (ENNReal.ofReal_pos.2 hd).ne'
  rw [ENNReal.ofReal_div_of_pos hd, ← h2, mul_comm (ENNReal.ofReal d), ENNReal.mul_div_cancel_right h0 ENNReal.ofReal_ne_top]

theorem kappa_zero {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] {R : Rep k r}
    {RI : Sub (2 * r + k + 1) 0 → Rep k r} {io pr ep} (hT : TensH (cmp 0) (cmp 0 (Hpk k r)) R RI io pr ep)
    (f : Fin 0 → Fin (2 * r + k + 1) → ℂ) {l : R.H → Wp} (I : Sub (2 * r + k + 1) 0) {lI : (RI I).H → Wp} {κ₀ : ℂ}
    (hκ : ∀ v ∈ R.sm, lI (∑ c, pr I c (tm R (wedge f) v c)) = κ₀ • l v)
    (hd : ∀ y ∈ (RI I).sm, l (ev (cmp 0 (Hpk k r)) R (wedge f) (fun c => io I c y)) = ((ep I : ℂ) * star κ₀) • lI y)
    (hnz : NzOn (RI I) lI) : ‖κ₀‖ ^ 2 ≤ 1 := by
  obtain ⟨y, hy, hy0⟩ := hnz
  haveI : Unique (Sub (2 * r + k + 1) 0) :=
    ⟨⟨I⟩, fun J => Subtype.ext ((Finset.card_eq_zero.1 J.2).trans (Finset.card_eq_zero.1 I.2).symm)⟩
  have hw : ∀ c, wedge f c = 1 := fun c => Matrix.det_fin_zero
  have hc : ∀ c d, cmp 0 (Hpk k r) c d = 1 := fun c d => Matrix.det_fin_zero
  have h1 := hκ _ ((hT.raw.io_sm I default).mem y hy)
  have h2 := hd y hy
  have h3 := hT.raw.pr_io I y hy
  simp only [tm, ev, hw, hc, Fintype.sum_unique, one_smul, star_one, mul_one] at h1 h2 h3
  rw [h3, h2, smul_smul] at h1
  have h4 := congrArg norm h1
  have he : ‖(ep I : ℂ)‖ = 1 := by rcases hT.ep_sq I with h | h <;> simp [h]
  rw [norm_smul, norm_mul, norm_mul, he, norm_star, one_mul] at h4
  have h5 : 0 < ‖lI y‖ := norm_pos_iff.2 hy0
  nlinarith

theorem exists_fam (hH : Hyps) {lam : Fin (2 * r + k + 1) → ℝ} (hlam : ∀ ν : Fin (2 * r + k + 1) → ℤ, n1 ν ≤ q0 →
      IsHCParam fun a => lam a + (ν a : ℝ))
    (hP : ∃ P, PI.UpqRep.IsCayleyU k r (PI.BesselPeriodGGP.eps48 k r) P) {ι : Type}
    (p : ι → Fin (2 * r + k + 1) → ℤ) (hp : Function.Injective p) (X : ι → Rep k r)
    (hX : ∀ i, (X i).IsDS (PI.BesselPeriodGGP.eps48 k r) fun a => lam a + (p i a : ℝ)) (R₀ : Rep k r) :
    ∃ R, IsFam lam q0 R ∧ ∀ i, R (p i) = X i := by
  have h1 : ∀ ν : Fin (2 * r + k + 1) → ℤ, ∃ R : Rep k r, (∀ i, p i = ν → R = X i) ∧
      (n1 ν ≤ q0 → R.IsDS (PI.BesselPeriodGGP.eps48 k r) fun a => lam a + (ν a : ℝ)) := by
    intro ν
    by_cases h : ∃ i, p i = ν
    · obtain ⟨i, rfl⟩ := h
      exact ⟨X i, fun j hj => by rw [hp hj], fun _ => hX i⟩
    · by_cases hq : n1 ν ≤ q0
      · obtain ⟨R, hR⟩ := hH.2.2.2.1 k r _ _ (hlam ν hq) hP
        exact ⟨R, fun i hi => absurd ⟨i, hi⟩ h, fun _ => hR⟩
      · exact ⟨R₀, fun i hi => absurd ⟨i, hi⟩ h, fun h' => absurd h' hq⟩
  choose R h2 h3 using h1
  exact ⟨R, h3, fun i => h2 _ i rfl⟩

theorem amp_eq (hH : Hyps) (D : D7) {τ w w' θ} {W : LocW D.R.k D.R.rS} [CompleteSpace W.Wp] [CompleteSpace W.Wq]
    {lam : Fin (2 * D.R.rS + D.R.k + 1) → ℝ} {A : LocS W} {h : ℝ} {R : Rep D.R.k D.R.rS} (hR : R = ⟨A.H, A.σ⟩)
    {l : R.H → W.Wp} {l' : R.H → W.Wq} (hθ : 0 < θ) (hka : 0 < D.host.ka / gg D) (hT : 0 < Tr D w)
    (hT' : 0 < Tr D w') (hW : GoodW D τ w w' θ W) (hA : GoodS D lam A) (hg : GapAtLeast (epsSH D.R) lam h)
    (hok : Formalism.FourierDecayAlt.ThreeDimData.GapOK D.R.k D.R.rS h)
    (b1 : PI.BesselMapUniq.IsBesselMapSm (k := D.R.k) (r := D.R.rS) W.z (psiS D W.z) R.σ W.π l)
    (b2 : PI.BesselMapUniq.IsBesselMapSm (k := D.R.k) (r := D.R.rS) W.z' (psiS D W.z') R.σ W.π' l')
    (e1 : ∀ x ∈ R.sm, ∀ v ∈ R.TK, Formalism.FourierDecayAlt.ThreeDimData.be W.z
      ((2 * D.host.ka / ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)) : ℝ) : ℂ) W.π R.σ W.μW W.μN x v =
        (innerSL ℂ (l v)).smulRight (l x))
    (e2 : ∀ x ∈ R.sm, ∀ v ∈ R.TK, Formalism.FourierDecayAlt.ThreeDimData.be W.z'
      ((2 * D.host.ka / ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)) : ℝ) : ℂ) W.π' R.σ W.μW' W.μN x v =
        (innerSL ℂ (l' v)).smulRight (l' x)) :
    (∃ v, R.KFin v ∧ l v ≠ 0) ∧ (∃ v, R.KFin v ∧ l' v ≠ 0) ∧ ∃ (w0 : R.H) (η : ℂ),
      PI.UpqRep.IsLowUnitH D.R.k D.R.rS (epsSH D.R) lam R.σ w0 ∧
      ‖η‖ = PI.BesselPeriodGGP.fdegH W.μG R.σ w0 *
        Real.sqrt ((Module.finrank ℂ W.Wp : ℝ) * (Module.finrank ℂ W.Wq : ℝ)) ∧
      ∀ (ν : Measure (Mt D.R.k D.R.rS)) (γ : MatKR D.R.k D.R.rS), γ ∈ UH (Hpk D.R.k D.R.rS) →
        ν {x | Matrix.of x ∉ UH (Hpk D.R.k D.R.rS)} = 0 → A.J ν γ = η • amp R l l' w0 ν γ := by
  subst hR
  exact GlobalTheory.T.bessel_period_positivity hH D τ w w' θ W lam A h l l' hθ hka hT hT' hW hA hg hok b1 b2 e1 e2

theorem deg_eq {D : D7} {W : LocW D.R.k D.R.rS} {A : LocS W} {R : Rep D.R.k D.R.rS} (hR : R = ⟨A.H, A.σ⟩) {c d : ℝ}
    (h : ∀ v : A.H, v ≠ 0 → A.deg = c * PI.BesselPeriodGGP.fdegH W.μG A.σ v ∧ 0 < A.deg)
    (hd : ∀ v : R.H, v ≠ 0 → PI.BesselPeriodGGP.fdegH W.μG R.σ v = d) {v : R.H} (hv : v ≠ 0) : A.deg = c * d := by
  subst hR
  rw [← hd v hv]
  exact (h v hv).1

theorem ne_zero_of_low {R : Rep k r} {ε mu} {v : R.H} (h : PI.UpqRep.IsLowUnitH k r ε mu R.σ v) : v ≠ 0 := by
  obtain ⟨P, -, h1, -⟩ := h
  intro h0
  simp [h0] at h1

theorem rpow_ratio {K c d e : ℝ} (hK : 0 < K) (hc : 0 < c) (hd : 0 < d) (he : 0 < e) :
    (ENNReal.ofReal (K / (c * d))).toReal ^ (-(1 / 2 : ℝ)) =
      Real.sqrt (d / e) * (ENNReal.ofReal (K / (c * e))).toReal ^ (-(1 / 2 : ℝ)) := by
  rw [ENNReal.toReal_ofReal (by positivity), ENNReal.toReal_ofReal (by positivity), Real.rpow_neg (by positivity),
    Real.rpow_neg (by positivity), ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow, ← Real.sqrt_inv, ← Real.sqrt_inv,
    ← Real.sqrt_mul (by positivity)]
  congr 1
  field_simp

set_option maxHeartbeats 1000000 in

theorem line_of_tens (hH : Hyps) (hKF : AmpKF) (hCC : CellConv) (D : D7) {τ w w' θ} {W : LocW D.R.k D.R.rS}
    [CompleteSpace W.Wp] [CompleteSpace W.Wq] (hcd : cdScaleTie D)
    (hθ : 0 < θ) (hka : 0 < D.host.ka / gg D) (hT : 0 < Tr D w) (hT' : 0 < Tr D w') (hW : GoodW D τ w w' θ W)
    {lam : Fin (2 * D.R.rS + D.R.k + 1) → ℝ} {A₀ : LocS W} (hA₀ : GoodS D lam A₀) {l : ℕ} (hl : l ≤ D.R.rS + 1)
    {lamI : Sub (2 * D.R.rS + D.R.k + 1) l → Fin (2 * D.R.rS + D.R.k + 1) → ℝ}
    {AI : Sub (2 * D.R.rS + D.R.k + 1) l → LocS W} {gd : Sub (2 * D.R.rS + D.R.k + 1) l → Prop}
    (hAI : ∀ I, gd I → GoodS D (lamI I) (AI I)) {h : ℝ} {R : Rep D.R.k D.R.rS} (hR : R = ⟨A₀.H, A₀.σ⟩)
    {RI : Sub (2 * D.R.rS + D.R.k + 1) l → Rep D.R.k D.R.rS} (hRI : ∀ I, gd I → RI I = ⟨(AI I).H, (AI I).σ⟩)
    (hDS : R.IsDS (epsSH D.R) lam) (hg : GapAtLeast (epsSH D.R) lam h)
    (hDI : ∀ I, (RI I).IsDS (epsSH D.R) (lamI I) ∧ GapAtLeast (epsSH D.R) (lamI I) h)
    (hok : Formalism.FourierDecayAlt.ThreeDimData.GapOK D.R.k D.R.rS h) (hgc : GapCell D.R.k D.R.rS h) {io pr ep}
    (hTH : TensH (cmp l) (cmp l (Hpk D.R.k D.R.rS)) R RI io pr ep)
    {B : R.H → W.Wp} {B' : R.H → W.Wq} {BI : ∀ I, (RI I).H → W.Wp} {BI' : ∀ I, (RI I).H → W.Wq}
    (b1 : PI.BesselMapUniq.IsBesselMapSm (k := D.R.k) (r := D.R.rS) W.z (psiS D W.z) R.σ W.π B)
    (b2 : PI.BesselMapUniq.IsBesselMapSm (k := D.R.k) (r := D.R.rS) W.z' (psiS D W.z') R.σ W.π' B')
    (e1 : ∀ x ∈ R.sm, ∀ v ∈ R.TK, Formalism.FourierDecayAlt.ThreeDimData.be W.z
      ((2 * D.host.ka / ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)) : ℝ) : ℂ) W.π R.σ W.μW W.μN x v =
        (innerSL ℂ (B v)).smulRight (B x))
    (e2 : ∀ x ∈ R.sm, ∀ v ∈ R.TK, Formalism.FourierDecayAlt.ThreeDimData.be W.z'
      ((2 * D.host.ka / ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)) : ℝ) : ℂ) W.π' R.σ W.μW' W.μN x v =
        (innerSL ℂ (B' v)).smulRight (B' x))
    (bI1 : ∀ I, PI.BesselMapUniq.IsBesselMapSm (k := D.R.k) (r := D.R.rS) W.z (psiS D W.z) (RI I).σ W.π (BI I))
    (bI2 : ∀ I, PI.BesselMapUniq.IsBesselMapSm (k := D.R.k) (r := D.R.rS) W.z' (psiS D W.z') (RI I).σ W.π' (BI' I))
    (eI1 : ∀ I, ∀ x ∈ (RI I).sm, ∀ v ∈ (RI I).TK, Formalism.FourierDecayAlt.ThreeDimData.be W.z
      ((2 * D.host.ka / ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)) : ℝ) : ℂ) W.π (RI I).σ W.μW W.μN x v =
        (innerSL ℂ (BI I v)).smulRight (BI I x))
    (eI2 : ∀ I, ∀ x ∈ (RI I).sm, ∀ v ∈ (RI I).TK, Formalism.FourierDecayAlt.ThreeDimData.be W.z'
      ((2 * D.host.ka / ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)) : ℝ) : ℂ) W.π' (RI I).σ W.μW' W.μN x v =
        (innerSL ℂ (BI' I v)).smulRight (BI' I x))
    {κ₀ κ₁ : Sub (2 * D.R.rS + D.R.k + 1) l → ℂ}
    (hκ : ∀ I, ∀ v ∈ R.sm,
      BI I (∑ c, pr I c (tm R (wedge fun a : Fin l => fvec D.R.k D.R.rS W.z (Fin.castLE hl a)) v c)) = κ₀ I • B v ∧
      BI' I (∑ c, pr I c (tm R (wedge fun a : Fin l => fvec D.R.k D.R.rS W.z' (Fin.castLE hl a)) v c)) = κ₁ I • B' v)
    (hz : ∀ I, ¬ gd I → κ₀ I = 0 ∨ κ₁ I = 0) {d : ℝ} {dI : Sub (2 * D.R.rS + D.R.k + 1) l → ℝ} (hd0 : 0 < d)
    (hdI0 : ∀ I, 0 < dI I) (hd : ∀ v : R.H, v ≠ 0 → PI.BesselPeriodGGP.fdegH W.μG R.σ v = d)
    (hdI : ∀ I, ∀ v : (RI I).H, v ≠ 0 → PI.BesselPeriodGGP.fdegH W.μG (RI I).σ v = dI I) :
    ∃ a : Sub (2 * D.R.rS + D.R.k + 1) l → ℂ, (∀ I, ¬ gd I → a I = 0) ∧
      (∀ I, ‖a I‖ ≤ Real.sqrt (d / dI I) * (‖κ₀ I‖ * ‖κ₁ I‖)) ∧
      ∀ μsec (K : ℝ), 0 < K → MMv D w w' A₀ μsec = ENNReal.ofReal (K / A₀.deg) →
        (∀ I, gd I → MMv D w w' (AI I) μsec = ENNReal.ofReal (K / (AI I).deg)) →
        ∀ γ p, RelPt D W.z W.z' γ p → ∀ θ' : ℝ, 0 < θ' → ∀ νR, RMeas D W γ θ' νR →
          DminN W.z W.z' γ l • jhUnit D w w' A₀ μsec νR γ = ∑ I, a I • jhUnit D w w' (AI I) μsec νR γ := by
  classical
  obtain ⟨n1, n2, w0, η, hw0, hη, hJ⟩ := amp_eq hH D hR hθ hka hT hT' hW hA₀ hg hok b1 b2 e1 e2
  have hN : 0 < Real.sqrt ((Module.finrank ℂ W.Wp : ℝ) * (Module.finrank ℂ W.Wq : ℝ)) := by
    obtain ⟨v, -, hv⟩ := n1
    obtain ⟨v', -, hv'⟩ := n2
    haveI := nontrivial_of_ne _ _ hv
    haveI := nontrivial_of_ne _ _ hv'
    have a1 : 0 < Module.finrank ℂ W.Wp := Module.finrank_pos
    have a2 : 0 < Module.finrank ℂ W.Wq := Module.finrank_pos
    positivity
  have hI : ∀ I, ∃ (wI : (RI I).H) (ηI : ℂ), PI.UpqRep.IsLowUnitH D.R.k D.R.rS (epsSH D.R) (lamI I) (RI I).σ wI ∧
      (gd I → ‖ηI‖ = dI I * Real.sqrt ((Module.finrank ℂ W.Wp : ℝ) * (Module.finrank ℂ W.Wq : ℝ)) ∧
      ∀ (ν : Measure (Mt D.R.k D.R.rS)) (γ : MatKR D.R.k D.R.rS), γ ∈ UH (Hpk D.R.k D.R.rS) →
        ν {x | Matrix.of x ∉ UH (Hpk D.R.k D.R.rS)} = 0 →
          (AI I).J ν γ = ηI • amp (RI I) (BI I) (BI' I) wI ν γ) := by
    intro I
    by_cases hI : gd I
    · obtain ⟨-, -, wI, ηI, h1, h2, h3⟩ :=
        amp_eq hH D (hRI I hI) hθ hka hT hT' hW (hAI I hI) (hDI I).2 hok (bI1 I) (bI2 I) (eI1 I) (eI2 I)
      exact ⟨wI, ηI, h1, fun _ => ⟨by rw [h2, hdI I _ (ne_zero_of_low h1)], h3⟩⟩
    · obtain ⟨wI, -, h1⟩ := GlobalTheory.exists_isLowUnitH_of_isDSHpk (hDI I).1.2
      exact ⟨wI, 0, h1, fun h' => absurd h' hI⟩
  choose wI ηI hwI hηI using hI
  rw [hd _ (ne_zero_of_low hw0)] at hη
  obtain ⟨c, hc, hdeg⟩ := GlobalTheory.DegreeTie.deg_eq_mul_fdegH hH D τ w w' θ W hcd hW
  have hη0 : ∀ I, gd I → ηI I ≠ 0 := fun I hI => by
    rw [← norm_pos_iff, (hηI I hI).1]
    exact mul_pos (hdI0 I) hN
  refine ⟨fun I => if gd I then (Real.sqrt (d / dI I) : ℂ) * (η / d * ((ep I : ℂ) * κ₁ I * star (κ₀ I) * dI I) / ηI I)
    else 0, fun I hI => if_neg hI, fun I => ?_, ?_⟩
  · by_cases hI : gd I
    · have he : ‖(ep I : ℂ)‖ = 1 := by rcases hTH.ep_sq I with h | h <;> simp [h]
      have := hdI0 I
      simp only [if_pos hI, norm_mul, norm_div, he, norm_star, hη, (hηI I hI).1, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hd0, abs_of_pos this, abs_of_nonneg (Real.sqrt_nonneg _)]
      refine le_of_eq ?_
      field_simp
    · simp only [if_neg hI, norm_zero]
      positivity
  intro μsec K hK hM hMI γ p hγ θ' hθ' νR hν
  obtain ⟨g₀, μR, ν₀, ν, s, hcell, hν₀, hD, hs⟩ :=
    GlobalTheory.T.amplitudes_relevant_cell_monomial_rep D τ w w' θ W hW lam A₀ hA₀ hT hT' hθ hka γ p hγ θ' hθ' νR hν
  have hμ : W.μN = (toBessel D τ w w' θ W lam A₀ hW hA₀ hT hT').μN := hW.2.2.2.2.2.2.2.2.2.2.2.1
  rw [hμ] at e1 e2 eI1 eI2
  have hc0 : ((2 * D.host.ka / ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)) : ℝ) : ℂ) ≠ 0 := by
    rw [Complex.ofReal_ne_zero, mul_div_assoc]
    exact (mul_pos two_pos hka).ne'
  have key := GlobalTheory.T.block_projection_bessel hH hKF hCC D.R.k D.R.rS _ _ (cmp l) (cmp l (Hpk D.R.k D.R.rS)) l
    (toBessel D τ w w' θ W lam A₀ hW hA₀ hT hT') R RI io pr ep lam lamI h W.μG _ _ B B' BI BI' w0 wI κ₀ κ₁
    hDS hg hDI hok hgc hc0 ENNReal.ofReal_ne_top hW.2.2.2.2.2.2.1 (GlobalTheory.WedgeFRep.isFRep_cmp _ _ l) hTH
    (GlobalTheory.T.flagWedge_fixed_and_length_eq_prod_distances _ _ l hl W.z hW.2.2.1).1 (GlobalTheory.T.flagWedge_fixed_and_length_eq_prod_distances _ _ l hl W.z' hW.2.2.2.1).1 e1 e2
    (fun I => ⟨eI1 I, eI2 I⟩) n1 n2 hw0 hwI hκ g₀ μR ν₀ ν hcell
  rw [GlobalTheory.PrincipalMinorExterior.pairing_eq_leading_minor, hd _ (ne_zero_of_low hw0)] at key
  have hDm : DminN W.z W.z' g₀ l =
      ((Zhat D.R.k D.R.rS W.z W.z' g₀).submatrix (Fin.castLE hl) (Fin.castLE hl)).det := by
    rw [DminN, dif_pos (by omega)]; rfl
  have hdc : (d : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hd0.ne'
  rw [hD, jhUnit, hs _ _ hA₀, hJ _ _ hcell.1 hν₀, hM, deg_eq hR (hdeg _ _ hA₀) hd (ne_zero_of_low hw0)]
  set M : ℂ := (((ENNReal.ofReal (K / (c * d))).toReal ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) with hMd
  have e : DminN W.z W.z' g₀ l • M • s • η • amp R B B' w0 ν₀ g₀ =
      (M * s * η / d) • (DminN W.z W.z' g₀ l * (d : ℂ)) • amp R B B' w0 ν₀ g₀ := by
    simp only [smul_smul]
    congr 1
    field_simp
  have key' : (DminN W.z W.z' g₀ l * (d : ℂ)) • amp R B B' w0 ν₀ g₀ =
      ∑ I, ((ep I : ℂ) * κ₁ I * star (κ₀ I) * (PI.BesselPeriodGGP.fdegH W.μG (RI I).σ (wI I) : ℂ)) •
        amp (RI I) (BI I) (BI' I) (wI I) ν₀ g₀ := by
    rw [hDm]; exact key
  rw [e, key', Finset.smul_sum]
  refine Finset.sum_congr rfl fun I _ => ?_
  rw [hdI I _ (ne_zero_of_low (hwI I))]
  beta_reduce
  by_cases hI : gd I
  · rw [if_pos hI, jhUnit, hs _ _ (hAI I hI), (hηI I hI).2 _ _ hcell.1 hν₀, hMI I hI,
      deg_eq (hRI I hI) (hdeg _ _ (hAI I hI)) (hdI I) (ne_zero_of_low (hwI I)), hMd,
      rpow_ratio hK hc hd0 (hdI0 I)]
    simp only [smul_smul]
    congr 1
    have := hη0 I hI
    push_cast
    field_simp
  · rw [if_neg hI]
    rcases hz I hI with h0 | h0 <;> simp only [h0, mul_zero, zero_mul, star_zero, zero_smul, smul_zero]

section side

variable {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp]
  {z : Fin (2 * r + k + 1) → ℂ} {π : MM k r → (Wp →L[ℂ] Wp)} {μW μN μG νq : Measure (Mt k r)} {t : MM k r}

theorem moved (hH : Hyps) {u : ℕ → ℝ} {c : ℂ} (ht : t ∈ GG k r) (hN : ∀ n, n ∈ Nset k r ↔ t * n * t⁻¹ ∈ Nset k r)
    (hc : ∀ h ∈ UWset k r z, t * h = h * t)
    (hψ : ∀ n ∈ Nset k r, psi k r z cStd n = psi k r z c (t * n * t⁻¹)) (hS : SideG k r z π u μW μN μG νq)
    {R : Rep k r} {ε mu} (hR : R.IsDS ε mu) {l₁ : R.H → Wp}
    (hl : IsBeL R z π μW (μN.map fun x => fun i j => (t⁻¹ * Matrix.of x * t) i j) l₁) :
    PI.BesselMapUniq.IsBesselMapSm (k := k) (r := r) z (psi k r z c) R.σ π (fun v => l₁ (R.σ t⁻¹ v)) ∧
    ∀ x ∈ R.sm, ∀ v ∈ R.TK, Formalism.FourierDecayAlt.ThreeDimData.be z c π R.σ μW μN x v =
      (innerSL ℂ (l₁ (R.σ t⁻¹ v))).smulRight (l₁ (R.σ t⁻¹ x)) := by
  have hU := urep_of_isDS hR
  obtain ⟨h1, h2⟩ := (bessel_move hH k r Wp z π u c μW μN μG νq t ht hN hc hψ hS).2 R hU
  refine ⟨(h1 _).2 ?_, h2 l₁ hl⟩
  have e : (fun v => l₁ (R.σ t⁻¹ (R.σ t v))) = l₁ := by
    funext v
    rw [← sig_mul hU (inv_mem ht) ht, inv_mul' ht, sig_one hU]
  rw [e]
  exact hl.1

theorem firstNorm_add_subsetIndicator_le {n l : ℕ} {ν : Fin n → ℤ} {q : ℕ} (h : n1 ν + l ≤ q) (I : Sub n l) : n1 (ν + eZ I.1) ≤ q := by
  have := GlobalTheory.TensExists.l1_add_le ν (eZ I.1)
  rw [GlobalTheory.TensExists.n1_eZ_eq_card, I.2] at this
  omega

omit [FiniteDimensional ℂ Wp] in
theorem dg_eq {lam u b bv ga h R l dg} (hS : Setup (k := k) (r := r) lam u b bv ga h q0 z π μW μN μG νq R l dg) {c : ℝ}
    (hc : ∀ mu (R : Rep k r), R.IsDS (PI.BesselPeriodGGP.eps48 k r) mu → ∀ w, w ≠ 0 →
      PI.BesselPeriodGGP.fdegH μG R.σ w = c * fdegHC mu) {ν} (hν : n1 ν ≤ q0) :
    dg ν = c * fdegHC fun a => lam a + (ν a : ℝ) := by
  obtain ⟨w, -, hw⟩ := GlobalTheory.exists_isLowUnitH_of_isDSHpk (hS.2.1 ν hν).2
  rw [← (hS.2.2.2 ν hν).2.2 w (ne_zero_of_low hw), hc _ _ (hS.2.1 ν hν) w (ne_zero_of_low hw)]

theorem side_kappa (hH : Hyps) (ht : t ∈ GG k r) {lam u u' b bv ga h F F' l₁ m₁ dg dg'} {μN' : Measure (Mt k r)}
    (hS : Setup (k := k) (r := r) lam u b bv ga h q0 z π μW μN' μG
      (νq.map fun x => fun i j => (t⁻¹ * Matrix.of x) i j) F l₁ dg)
    (hS' : Setup (k := k) (r := r) lam u' b bv ga h q0 z π μW μN' μG
      (νq.map fun x => fun i j => (t⁻¹ * Matrix.of x) i j) F' m₁ dg')
    {l : ℕ} (hl : l ≤ r + 1) (hFF : l = 0 ∨ (F' = F ∧ HEq m₁ l₁ ∧ dg' = dg)) {ν} (hν : n1 ν + (r + 1) * (r + 2) ≤ q0)
    {io pr ep} (hT : TensH (cmp l) (cmp l (Hpk k r)) (F ν) (fun I : Sub (2 * r + k + 1) l => F' (ν + eZ I.1)) io pr ep)
    {S : ℂ} (hω : cmp l t⁻¹ *ᵥ (wedge fun a : Fin l => fvec k r z (Fin.castLE hl a)) =
      S • wedge fun a : Fin l => fvec k r z (Fin.castLE hl a))
    (hnz : ∃ v, (F ν).KFin v ∧ l₁ ν ((F ν).σ t⁻¹ v) ≠ 0) (I : Sub (2 * r + k + 1) l) :
    ∃ κ₀ : ℂ, (∀ v ∈ (F ν).sm, m₁ (ν + eZ I.1) ((F' (ν + eZ I.1)).σ t⁻¹
        (∑ c, pr I c (tm (F ν) (wedge fun a : Fin l => fvec k r z (Fin.castLE hl a)) v c))) =
          κ₀ • l₁ ν ((F ν).σ t⁻¹ v)) ∧
      ‖κ₀‖ ^ 2 * dg ν / dg' (ν + eZ I.1) ≤ ‖S‖ ^ 2 * Hsq r (Tz k r z) b ^ l ∧
      (κ₀ ≠ 0 → ∀ v ∈ (F' (ν + eZ I.1)).sm,
        l2SG νq (fun g => m₁ (ν + eZ I.1) ((F' (ν + eZ I.1)).σ t⁻¹ ((F' (ν + eZ I.1)).σ g v))) =
          ENNReal.ofReal (‖v‖ ^ 2 / dg' (ν + eZ I.1))) := by
  have hν0 : n1 ν ≤ q0 := by omega
  have hνl : n1 ν + l ≤ q0 := by nlinarith
  have hR := hS.2.1 ν hν0
  have hRI := fun J : Sub (2 * r + k + 1) l => hS'.2.1 _ (firstNorm_add_subsetIndicator_le hνl J)
  have hU := urep_of_isDS hR
  have hb := GlobalTheory.rep_basic_of_isDS hH.1.2.2.1 k r _ _ _ hR
  have hnz' : NzOn (F ν) (l₁ ν) := by
    obtain ⟨v, hv, hv0⟩ := hnz
    exact ⟨_, sig_sm hU (inv_mem ht) (hb.2.2.2.2.1 v (hb.2.2.2.2.2.2.1 v hv)), hv0⟩
  obtain ⟨⟨κ₁, hκ⟩, hdual⟩ := GlobalTheory.KappaDual.kappa_dual hH k r _ _ _ _ l _ _ io pr ep _ _ _ Wp z π u μW μN' μG _ _ (l₁ ν)
    hR hRI (GlobalTheory.WedgeFRep.isFRep_cmp k r l) hT hS.2.2.1 (GlobalTheory.T.flagWedge_fixed_and_length_eq_prod_distances k r l hl z hS.2.2.1.1).1
    (hS.2.2.2 ν hν0).1 hnz' I (m₁ _) (hS'.2.2.2 _ (firstNorm_add_subsetIndicator_le hνl I)).1
  have hnI : κ₁ ≠ 0 → NzOn (F' (ν + eZ I.1)) (m₁ (ν + eZ I.1)) := by
    intro h0
    obtain ⟨v, hv, hv0⟩ := hnz'
    refine ⟨_, ?_, by rw [hκ v hv]; exact smul_ne_zero h0 hv0⟩
    exact Submodule.sum_mem (F' (ν + eZ I.1)).smSub fun c _ =>
      (hT.raw.pr_sm I c).mem _ (Formalism.FourierDecayAlt.P.DDSmoothness.smooth_smul _ hv)
  have hH1 : 0 ≤ Hsq r (Tz k r z) b ^ l := by
    have := (GlobalTheory.NumFam.num_fam k r _ _ _ _ _ _ _ hS.1).1
    have hb0 : 0 ≤ b := by linarith [this.1, this.2.1]
    unfold Hsq
    positivity
  refine ⟨S * κ₁, kappa_move hT.raw hU (inv_mem ht) hω (hS.2.2.2 ν hν0).1.1.2.1 I hκ, ?_, fun h0 v hv => ?_⟩
  · rw [norm_mul, mul_pow, mul_assoc, mul_div_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    by_cases h0 : κ₁ = 0
    · simpa [h0] using hH1
    rcases hFF with rfl | ⟨rfl, h2, rfl⟩
    · obtain ⟨c, -, hc⟩ := GlobalTheory.BesselDegree.schur_fdeg hH k r (PI.BesselPeriodGGP.eps48 k r) μG hS.2.2.1.2.2.2.2.2.2.1
      have e : ν + eZ I.1 = ν := by
        rw [Finset.card_eq_zero.1 I.2]; funext a; simp [eZ]
      have e2 : dg' (ν + eZ I.1) = dg ν := by
        rw [e, dg_eq hS (fun mu R h => (hc mu R h).1) hν0, dg_eq hS' (fun mu R h => (hc mu R h).1) hν0]
      rw [e2, mul_div_assoc, div_self (hS.2.2.2 ν hν0).2.1.ne', mul_one, pow_zero]
      exact kappa_zero hT _ I hκ (hdual κ₁ hκ) (hnI h0)
    · obtain rfl := eq_of_heq h2
      exact GlobalTheory.T.mass_bound_low_types_alt hH k r Wp lam u b bv ga h q0 z π μW μN' μG _ _ _ _ hS l hl ν hν io pr ep hT hnz' I κ₁
        (hnI h0) hκ
  · exact mass_move (urep_of_isDS (hRI I)) ht (hS'.2.2.2 _ (firstNorm_add_subsetIndicator_le hνl I)).2.1
      (GlobalTheory.quotMeas_ae_mem_and_measurable hH.1.2.2.1 k r _ _ _ Wp z π u μW μN' μG _ hR hS.2.2.1).1
      (((GlobalTheory.MomMass.mom_mass hH k r Wp lam u' b bv ga h q0 z π μW μN' μG _ F' m₁ dg' hS' _ (firstNorm_add_subsetIndicator_le hνl I)).2
        (hnI (right_ne_zero_of_mul h0))).2 v hv)

end side

theorem pow_le_rpow {b x α β : ℝ} {j : ℕ} (hb : 1 ≤ b) (hx : 0 ≤ x) (h : x ≤ b ^ α) (hα : 0 ≤ α) (hj : (j : ℝ) ≤ β) :
    x ^ j ≤ b ^ (α * β) := by
  calc x ^ j ≤ (b ^ α) ^ j := pow_le_pow_left₀ hx h j
    _ = b ^ (α * j) := (Real.rpow_mul_natCast (by linarith) α j).symm
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hb (mul_le_mul_of_nonneg_left hj hα)

theorem coef_le {a x y d e s p p' N : ℝ} (hd : 0 < d) (he : 0 < e) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (ha : a ≤ Real.sqrt (d / e) * (x * y)) (h1 : x ^ 2 * d / e ≤ s ^ 2 * p) (h2 : y ^ 2 * d / e ≤ s ^ 2 * p')
    (h3 : e ≤ N * d) (hp : 1 ≤ p) (hp' : 1 ≤ p') (hN : 1 ≤ N) : a ≤ s ^ 2 * p * p' * N := by
  refine ha.trans ((pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).1 ?_)
  have h4 : e / d ≤ N := by rwa [div_le_iff₀ hd]
  have h5 : 1 ≤ p * p' * N := one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hp hp') hN
  calc (Real.sqrt (d / e) * (x * y)) ^ 2 = (x ^ 2 * d / e) * (y ^ 2 * d / e) * (e / d) := by
        rw [mul_pow, Real.sq_sqrt (by positivity)]; field_simp
    _ ≤ (s ^ 2 * p) * (s ^ 2 * p') * N := by gcongr
    _ = (s ^ 2) ^ 2 * (p * p' * N) * 1 := by ring
    _ ≤ (s ^ 2) ^ 2 * (p * p' * N) * (p * p' * N) := by gcongr
    _ = _ := by ring

theorem hsq_le {b T CT M m : ℝ} {l : ℕ} (hb : 1 ≤ b) (hM : 0 ≤ M) (hr : (r : ℝ) + 1 ≤ m) (hl : (l : ℝ) ≤ m)
    (hT : T ≤ b ^ (CT * m)) :
    1 ≤ Hsq r T (b ^ M) ^ l ∧ Hsq r T (b ^ M) ^ l ≤ b ^ ((|CT| + 20 * M) * m ^ 2) := by
  have hm : 0 ≤ m := le_trans (by positivity) hr
  have h1 : 1 ≤ Hsq r T (b ^ M) :=
    one_le_mul_of_one_le_of_one_le (le_max_left _ _) (one_le_pow₀ (Real.one_le_rpow hb hM))
  refine ⟨one_le_pow₀ h1, ?_⟩
  have h2 : Hsq r T (b ^ M) ≤ b ^ ((|CT| + 20 * M) * m) := by
    have a1 : max 1 T ≤ b ^ (|CT| * m) := max_le (Real.one_le_rpow hb (by positivity))
      (hT.trans (Real.rpow_le_rpow_of_exponent_le hb (mul_le_mul_of_nonneg_right (le_abs_self _) hm)))
    have a2 : (b ^ M) ^ (20 * (r + 1)) ≤ b ^ (M * (20 * m)) :=
      pow_le_rpow hb (by positivity) le_rfl hM (by push_cast; linarith)
    calc Hsq r T (b ^ M) ≤ b ^ (|CT| * m) * b ^ (M * (20 * m)) := mul_le_mul a1 a2 (by positivity) (by positivity)
      _ = _ := by rw [← Real.rpow_add (by linarith)]; congr 1; ring
  refine (pow_le_rpow hb (by linarith) h2 (by positivity) hl).trans (le_of_eq ?_)
  congr 1; ring

theorem eZ_inj {n l : ℕ} (ν : Fin n → ℤ) : Function.Injective fun I : Sub n l => ν + eZ I.1 := by
  intro I J h
  apply Subtype.ext
  ext a
  have h := congrFun (add_left_cancel h) a
  simp only [eZ] at h
  by_cases h1 : a ∈ I.1 <;> by_cases h2 : a ∈ J.1 <;> simp_all

theorem exists_fams (hH : Hyps) {lam : Fin (2 * r + k + 1) → ℝ} (hlam : ∀ ν : Fin (2 * r + k + 1) → ℤ, n1 ν ≤ q0 →
      IsHCParam fun a => lam a + (ν a : ℝ))
    (hP : ∃ P, PI.UpqRep.IsCayleyU k r (PI.BesselPeriodGGP.eps48 k r) P) {l : ℕ} (ν : Fin (2 * r + k + 1) → ℤ)
    (R₀ : Rep k r) (h0 : R₀.IsDS (PI.BesselPeriodGGP.eps48 k r) fun a => lam a + (ν a : ℝ))
    (gd : Sub (2 * r + k + 1) l → Prop) (X : Sub (2 * r + k + 1) l → Rep k r)
    (hX : ∀ I, gd I → (X I).IsDS (PI.BesselPeriodGGP.eps48 k r) fun a => lam a + ((ν + eZ I.1) a : ℝ)) :
    ∃ F F', IsFam lam q0 F ∧ IsFam lam q0 F' ∧ F ν = R₀ ∧ (∀ I, gd I → F' (ν + eZ I.1) = X I) ∧ (l = 0 ∨ F' = F) := by
  by_cases hl : l = 0
  · obtain ⟨F, hF, h1⟩ := exists_fam hH hlam hP (fun _ : Unit => ν) (fun _ _ _ => rfl) (fun _ => R₀) (fun _ => h0) R₀
    obtain ⟨F', hF', h2⟩ := exists_fam hH hlam hP (fun I : {I // gd I} => ν + eZ I.1.1)
      ((eZ_inj ν).comp Subtype.val_injective) (fun I => X I.1) (fun I => hX I.1 I.2) R₀
    exact ⟨F, F', hF, hF', h1 (), fun I hI => h2 ⟨I, hI⟩, Or.inl hl⟩
  · have hne : ∀ I : Sub (2 * r + k + 1) l, ν ≠ ν + eZ I.1 := fun I h => by
      obtain ⟨a, ha⟩ := Finset.card_pos.1 (by rw [I.2]; omega : 0 < I.1.card)
      have := congrFun h a
      simp [eZ, ha] at this
    obtain ⟨F, hF, h1⟩ := exists_fam hH hlam hP
      (fun i : Option {I // gd I} => i.elim ν fun I => ν + eZ I.1.1) (by
        rintro (_ | I) (_ | J) h
        · rfl
        · exact absurd h (hne _)
        · exact absurd h.symm (hne _)
        · exact congrArg some (Subtype.ext (eZ_inj ν h)))
      (fun i => i.elim R₀ fun I => X I.1) (by
        rintro (_ | I)
        · exact h0
        · exact hX I.1 I.2) R₀
    exact ⟨F, F, hF, hF, h1 none, fun I hI => h1 (some ⟨I, hI⟩), Or.inr rfl⟩

theorem scale_le {b v g Cg : ℝ} (hb : Real.exp 1 < b) (hv : 1 ≤ v) (hvb : 2 * v ≤ b) (hg : 1 ≤ g)
    (hgb : g ≤ b ^ (2 * Cg)) (hC : 8 ≤ Cg) :
    max (‖((2 * (Real.pi / v) / g : ℝ) : ℂ)‖ / 2) (2 / ‖((2 * (Real.pi / v) / g : ℝ) : ℂ)‖) ≤ b ^ (2 * Cg + 2) := by
  have h1 := Real.pi_gt_three
  have h2 := Real.pi_lt_four
  have h3 : 2 < b := lt_trans (by linarith [Real.exp_one_gt_d9]) hb
  have h4 : 1 ≤ b ^ (2 * Cg) := hg.trans hgb
  rw [Complex.norm_real, Real.norm_of_nonneg (by positivity), Real.rpow_add (by linarith), Real.rpow_two]
  refine max_le ?_ ?_
  · have : 2 * (Real.pi / v) / g / 2 = Real.pi / (v * g) := by field_simp
    rw [this]
    have : Real.pi / (v * g) ≤ Real.pi := div_le_self (by linarith) (by nlinarith)
    nlinarith
  · have : 2 / (2 * (Real.pi / v) / g) = g * v / Real.pi := by field_simp
    rw [this]
    have : g * v / Real.pi ≤ g * v := div_le_self (by positivity) (by linarith)
    exact this.trans (mul_le_mul hgb (by nlinarith) (by linarith) (by linarith))

set_option maxHeartbeats 1000000 in

theorem minor_line : Hyps → AmpKF → CellConv → ∀ Cg cb Cu cT CT C0 C1 : ℝ, ∃ C : ℝ, ∀ Cn : ℝ, ∃ m₀ : ℝ, ∀ (D : D7) (large₂ : SizeData₂ D) (C' Cl : ℝ), 1000 ≤ Cl → Big D large₂ Cl m₀ → cdScaleTie D → HypZ D large₂ C' Cl Cg cb Cu cT CT C0 → ∀ τ w w', HypTT D w w' → ∀ θ, normWin D large₂ C1 θ → ∀ W, GoodW D τ w w' θ W → ∀ lam', l1dist lam' (lamD D τ) ≤ Cn * D.R.k * (D.R.m : ℝ) ^ 3 → ∀ A₀ : LocS W, GoodS D lam' A₀ → ∀ l : ℕ, l ≤ D.R.rS + 1 → ∃ s : ℝ, (s = 1 ∨ s = -1) ∧ ∀ AI : Finset (Fin (2 * D.R.rS + D.R.k + 1)) → LocS W, (∀ I, I.card = l → (∃ A : LocS W, GoodS D (lam' + s • epsI I) A) → GoodS D (lam' + s • epsI I) (AI I)) → ∃ a : Finset (Fin (2 * D.R.rS + D.R.k + 1)) → ℂ, (∀ I, I.card = l → (¬ ∃ A : LocS W, GoodS D (lam' + s • epsI I) A) → a I = 0) ∧ (∑ I ∈ univ.filter (fun I => I.card = l), ‖a I‖) ≤ large₂.sc.b ^ (C * (D.R.m : ℝ) ^ 2) ∧ ∀ μsec, IsSection D.R.k D.R.rS W.z W.z' μsec → ∀ γ p, RelPt D W.z W.z' γ p → ∀ θ', normWin D large₂ C1 θ' → ∀ νR, RMeas D W γ θ' νR → DminN W.z W.z' γ l • jhUnit D w w' A₀ μsec νR γ = ∑ I ∈ univ.filter (fun I => I.card = l), a I • jhUnit D w w' (AI I) μsec νR γ := by
  intro hH hKF hCC Cg cb Cu cT CT C0 C1
  refine ⟨2 * (2 * Cg + 2) + 2 * (|CT| + 20 * max 2 Cu) + 2 * max 2 Cu, fun Cn => ?_⟩
  obtain ⟨m₁, hJ⟩ := GlobalTheory.T.exists_mmv_eq_const_div_deg_of_near_parameter hH hKF hCC Cg cb Cu cT CT C0 C1 (Cn + 1)
  refine ⟨max m₁ (Cn + 1), fun D large₂ C' Cl hCl hBig hcd hZ τ w w' hTT θ hθw W hW lam' hlam A₀ hA₀ l hl =>
    ⟨1, Or.inl rfl, fun AI hAI => ?_⟩⟩
  classical
  simp only [one_smul] at hAI ⊢
  haveI := FiniteDimensional.complete ℂ W.Wp
  haveI := FiniteDimensional.complete ℂ W.Wq
  replace hJ := hJ D large₂ C' Cl hCl ⟨hBig.1, hBig.2.1, (le_max_left _ _).trans hBig.2.2⟩ hcd hZ τ w w' hTT θ hθw W hW
  obtain ⟨-, -, hbe, hm, -, -, -, hmk, hv, -, hka, hvb, hg1, hgb, hCg, -, hTb, -, -⟩ :=
    GlobalTheory.Amp.SizesProof.sizes_of_hyp D large₂ C' Cl Cg cb Cu cT CT C0 hBig.1 hZ
  have hb1 : 1 ≤ large₂.sc.b := by linarith [Real.exp_one_gt_d9]
  have hθ : 0 < θ := lt_of_lt_of_le (by positivity) hθw.1
  have hka0 : 0 < D.host.ka / gg D := by rw [hka]; have := Real.pi_pos; positivity
  have hT : 0 < Tr D w := by unfold Tr; exact_mod_cast hTT.1.pos
  have hT' : 0 < Tr D w' := by unfold Tr; exact_mod_cast hTT.2.1.pos
  have hmR : (D.R.m : ℝ) = 2 * D.R.rS + 2 := by exact_mod_cast hm
  have hr0 : (0 : ℝ) ≤ D.R.rS := Nat.cast_nonneg _
  have hlR : (l : ℝ) ≤ D.R.rS + 1 := by exact_mod_cast hl
  have hk1 : (1 : ℝ) ≤ D.R.k := by
    have := D.R.m_add_three_le_k
    exact_mod_cast (by omega : 1 ≤ D.R.k)
  have hm2 : (D.R.m : ℝ) ^ 2 ≤ D.R.k * (D.R.m : ℝ) ^ 3 := by
    have : (D.R.m : ℝ) ^ 2 ≤ (D.R.m : ℝ) ^ 3 := pow_le_pow_right₀ (by linarith) (by norm_num)
    nlinarith [pow_nonneg (show (0 : ℝ) ≤ D.R.m by linarith) 3]
  obtain ⟨hNum, hgc, heps⟩ := GlobalTheory.T.momentPieriNumerics_of_sizeHyps D large₂ C' Cl Cg cb Cu cT CT C0 hZ hCl τ w
    (fun n => if h : n - 1 < D.R.k then uS D w τ ⟨n - 1, h⟩ else 0) (fun i => by simp)
  obtain ⟨⟨hbv, hbv', hnb, -, hok⟩, hnum⟩ := GlobalTheory.NumFam.num_fam _ _ _ _ _ _ _ _ _ hNum
  obtain ⟨ν, rfl⟩ : ∃ ν : Fin (2 * D.R.rS + D.R.k + 1) → ℤ, lam' = fun a => lamD D τ a + (ν a : ℝ) := by
    choose x hx using hA₀.1.2
    choose y hy using hNum.2.1.2
    refine ⟨x - y, funext fun a => ?_⟩
    simp only [Pi.sub_apply, Int.cast_sub]
    linarith [hx a, hy a]
  have hdist : ∀ μ : Fin (2 * D.R.rS + D.R.k + 1) → ℤ,
      l1dist (fun a => lamD D τ a + (μ a : ℝ)) (lamD D τ) = n1 μ := fun μ => by
    simp [l1dist, n1]
  rw [hdist] at hlam
  have hν : n1 ν + (D.R.rS + 1) * (D.R.rS + 2) ≤ D.R.k * D.R.m ^ 5 := by
    have h1 : Cn + 1 ≤ (D.R.m : ℝ) ^ 2 := by nlinarith [(le_max_right _ _).trans hBig.2.2]
    have h2 : (Cn + 1) * (D.R.k * (D.R.m : ℝ) ^ 3) ≤ (D.R.m : ℝ) ^ 2 * (D.R.k * (D.R.m : ℝ) ^ 3) :=
      mul_le_mul_of_nonneg_right h1 (by positivity)
    have h3 : ((D.R.rS : ℝ) + 1) * (D.R.rS + 2) ≤ (D.R.m : ℝ) ^ 2 := by rw [hmR]; nlinarith
    have : (n1 ν : ℝ) + ((D.R.rS : ℝ) + 1) * (D.R.rS + 2) ≤ D.R.k * (D.R.m : ℝ) ^ 5 := by nlinarith
    exact_mod_cast this
  have hν0 : n1 ν ≤ D.R.k * D.R.m ^ 5 := by omega
  have hνl : n1 ν + l ≤ D.R.k * D.R.m ^ 5 := by nlinarith
  have hsh : ∀ I : Finset (Fin (2 * D.R.rS + D.R.k + 1)), (fun a => lamD D τ a + (ν a : ℝ)) + epsI I =
      fun a => lamD D τ a + ((ν + eZ I) a : ℝ) := fun I => by
    funext a
    simp only [epsI, eZ, Pi.add_apply]
    split_ifs <;> push_cast <;> ring
  simp only [hsh] at hAI ⊢
  obtain ⟨F, F', hF, hF', hF0, hFI, hFF⟩ := exists_fams hH (fun μ h => (hnum μ h).1)
    (by rw [heps]; obtain ⟨P, hP, -⟩ := hA₀.2.1; exact ⟨P, hP⟩) ν ⟨A₀.H, A₀.σ⟩ (by rw [heps]; exact ⟨hA₀.1, hA₀.2.1⟩)
    (fun I : Sub _ l => ∃ A : LocS W, GoodS D (fun a => lamD D τ a + ((ν + eZ I.1) a : ℝ)) A)
    (fun I => ⟨(AI I.1).H, (AI I.1).σ⟩)
    (fun I hI => by rw [heps]; exact ⟨(hAI I.1 I.2 hI).1, (hAI I.1 I.2 hI).2.1⟩)
  have hc0 : ((2 * D.host.ka / ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)) : ℝ) : ℂ) ≠ 0 := by
    rw [Complex.ofReal_ne_zero, mul_div_assoc]
    exact (mul_pos two_pos hka0).ne'
  obtain ⟨t, ht, hNt, hz, hs⟩ := GlobalTheory.TorusScale.exists_torus_scale D.R.k D.R.rS _ hc0
  choose s hs0 hs1 hs2 hs3 using hs
  have hmod := GlobalTheory.T.torus_commutes_with_unipotent hH D large₂ C' Cl Cg cb Cu cT CT C0 hZ hCl τ w w' θ W hTT hθ hW t ht hNt
    (fun z h => (hz z h).2)
  obtain ⟨U, U', l₁, l₂, dg, S1, S2⟩ := hmod F hF
  obtain ⟨V, V', m₁, m₂, dg', T1, T2, hE⟩ : ∃ V V' m₁ m₂ dg',
      Setup (lamD D τ) V (large₂.sc.b ^ max 2 Cu) (bOne D τ 1) ((D.R.r : ℝ) * (D.R.m : ℝ) ^ 10) ((D.R.r : ℝ) ^ 19)
        (D.R.k * D.R.m ^ 5) W.z W.π W.μW (W.μN.map fun x => fun i j => (t⁻¹ * Matrix.of x * t) i j) W.μG
        (W.νS.map fun x => fun i j => (t⁻¹ * Matrix.of x) i j) F' m₁ dg' ∧
      Setup (lamD D τ) V' (large₂.sc.b ^ max 2 Cu) (bOne D τ 1) ((D.R.r : ℝ) * (D.R.m : ℝ) ^ 10) ((D.R.r : ℝ) ^ 19)
        (D.R.k * D.R.m ^ 5) W.z' W.π' W.μW' (W.μN.map fun x => fun i j => (t⁻¹ * Matrix.of x * t) i j) W.μG
        (W.νS'.map fun x => fun i j => (t⁻¹ * Matrix.of x) i j) F' m₂ dg' ∧
      (l = 0 ∨ (F' = F ∧ HEq m₁ l₁ ∧ HEq m₂ l₂ ∧ dg' = dg)) := by
    rcases hFF with h | rfl
    · obtain ⟨V, V', m₁, m₂, dg', T1, T2⟩ := hmod F' hF'
      exact ⟨V, V', m₁, m₂, dg', T1, T2, Or.inl h⟩
    · exact ⟨U, U', l₁, l₂, dg, S1, S2, Or.inr ⟨rfl, HEq.rfl, HEq.rfl, rfl⟩⟩
  have hNH : IsHaarOn (Nset D.R.k D.R.rS) W.μN := by
    rw [hW.2.2.2.2.2.2.2.2.2.2.2.1]
    exact GlobalTheory.T.haarLie_isHaarOn_unipotentRadical _ _ _ (ENNReal.ofReal_pos.2 (by positivity)) ENNReal.ofReal_lt_top
  have z1 := hW.2.2.1
  have z2 := hW.2.2.2.1
  have G1 : SideG D.R.k D.R.rS W.z W.π U W.μW W.μN W.μG W.νS :=
    ⟨z1, S1.2.2.1.2.1, S1.2.2.1.2.2.1, S1.2.2.1.2.2.2.1, S1.2.2.1.2.2.2.2.1, hNH, hW.2.2.2.2.2.2.1,
      hW.2.2.2.2.2.2.2.2.2.2.2.2.1⟩
  have G2 : SideG D.R.k D.R.rS W.z' W.π' U' W.μW' W.μN W.μG W.νS' :=
    ⟨z2, S2.2.2.1.2.1, S2.2.2.1.2.2.1, S2.2.2.1.2.2.2.1, S2.2.2.1.2.2.2.2.1, hNH, hW.2.2.2.2.2.2.1,
      hW.2.2.2.2.2.2.2.2.2.2.2.2.2⟩
  have hDS := hF ν hν0
  have hDI := fun I : Sub _ l => hF' _ (firstNorm_add_subsetIndicator_le hνl I)
  obtain ⟨io, pr, ep, hTH⟩ : ∃ io pr ep, TensH (cmp l) (cmp l (Hpk D.R.k D.R.rS)) (F ν)
      (fun I : Sub _ l => F' (ν + eZ I.1)) io pr ep := by
    have hI : ∀ I : Sub _ l, (F' (ν + eZ I.1)).IsDS (PI.BesselPeriodGGP.eps48 D.R.k D.R.rS)
        (addSet (fun a => lamD D τ a + (ν a : ℝ)) I.1) := fun I => by
      have := hDI I
      rwa [← hsh] at this
    obtain ⟨io, pr, hT⟩ := (hH.2.2.2.2.1 _ _ _ _ (F ν) hDS (hnum ν hν0).2.2.2).1 l _ hI
    exact GlobalTheory.TensOrth.tensH_of_raw hH _ _ _ _ _ _ l _ _ io pr _ _ _ hDS hI (GlobalTheory.TensExists.addSet_inj _)
      (GlobalTheory.WedgeFRep.isFRep_cmp _ _ l) hT
  obtain ⟨b1, e1⟩ := moved hH ht hNt (hz _ z1).2.1 (hz _ z1).2.2 G1 hDS (S1.2.2.2 ν hν0).1
  obtain ⟨b2, e2⟩ := moved hH ht hNt (hz _ z2).2.1 (hz _ z2).2.2 G2 hDS (S2.2.2.2 ν hν0).1
  have bI1 := fun I : Sub _ l => moved hH ht hNt (hz _ z1).2.1 (hz _ z1).2.2 G1 (hDI I) (T1.2.2.2 _ (firstNorm_add_subsetIndicator_le hνl I)).1
  have bI2 := fun I : Sub _ l => moved hH ht hNt (hz _ z2).2.1 (hz _ z2).2.2 G2 (hDI I) (T2.2.2.2 _ (firstNorm_add_subsetIndicator_le hνl I)).1
  have hgap := fun μ h => (hnum μ h).2.2.1
  rw [heps] at hDS hDI hgap
  obtain ⟨n₁, n₂, -⟩ := amp_eq hH D hF0 hθ hka0 hT hT' hW hA₀ (hgap ν hν0) hok b1 b2 e1 e2
  choose κ₀ hκ₀ hb₀ hm₀ using side_kappa hH ht S1 T1 hl (hE.imp id fun h => ⟨h.1, h.2.1, h.2.2.2⟩) hν hTH
    (cmp_wedge_eigen _ _ (fun a => s (Fin.castLE hl a)) fun a => hs3 _ _ z1) n₁
  choose κ₁ hκ₁ hb₁ hm₁ using side_kappa hH ht S2 T2 hl (hE.imp id fun h => ⟨h.1, h.2.2.1, h.2.2.2⟩) hν hTH
    (cmp_wedge_eigen _ _ (fun a => s (Fin.castLE hl a)) fun a => hs3 _ _ z2) n₂
  have hd0 := (S1.2.2.2 ν hν0).2
  have hdI := fun I : Sub _ l => (T1.2.2.2 _ (firstNorm_add_subsetIndicator_le hνl I)).2
  obtain ⟨a, ha0, ha1, ha2⟩ := line_of_tens hH hKF hCC D hcd hθ hka0 hT hT' hW hA₀ hl (AI := fun I => AI I.1)
    (fun I hI => hAI I.1 I.2 hI) hF0 hFI hDS (hgap ν hν0) (fun I => ⟨hDI I, hgap _ (firstNorm_add_subsetIndicator_le hνl I)⟩) hok hgc hTH
    b1 b2 e1 e2 (fun I => (bI1 I).1) (fun I => (bI2 I).1) (fun I => (bI1 I).2) (fun I => (bI2 I).2)
    (fun I v hv => ⟨hκ₀ I v hv, hκ₁ I v hv⟩)
    (fun I hI => by
      by_contra hn
      push Not at hn
      exact hI (GlobalTheory.T.bessel_map_pairing_bound hH D τ w w' θ W _ _ 0 _ _ _ hcd hW (hDI I) (bI1 I).1 (bI2 I).1 (hdI I).1
        (hm₀ I hn.1) (hm₁ I hn.2)))
    hd0.1 (fun I => (hdI I).1) hd0.2 (fun I => (hdI I).2)
  have hsum : ∀ {E : Type} [AddCommMonoid E] (f : Finset (Fin (2 * D.R.rS + D.R.k + 1)) → E),
      ∑ I ∈ univ.filter (fun I => I.card = l), f I = ∑ I : Sub _ l, f I.1 := fun f =>
    Finset.sum_subtype _ (by simp) f
  have haI : ∀ I : Sub (2 * D.R.rS + D.R.k + 1) l, (if h : I.1.card = l then a ⟨I.1, h⟩ else 0) = a I :=
    fun I => dif_pos I.2
  refine ⟨fun I => if h : I.card = l then a ⟨I, h⟩ else 0, fun I hI hn => (haI ⟨I, hI⟩).trans (ha0 _ hn), ?_, ?_⟩
  · rw [hsum]
    simp only [haI]
    have hM : (0 : ℝ) ≤ max 2 Cu := le_trans zero_le_two (le_max_left _ _)
    have hn1 : (1 : ℝ) ≤ 2 * D.R.rS + D.R.k + 1 := by linarith
    have hN : ((2 * D.R.rS + D.R.k + 1 : ℝ)) ^ l ≤ large₂.sc.b ^ (max 2 Cu * (D.R.m : ℝ) ^ 2) :=
      pow_le_rpow hb1 (by linarith) hnb hM (by rw [hmR]; nlinarith)
    have hS : ‖∏ a : Fin l, s (Fin.castLE hl a)‖ ≤ large₂.sc.b ^ ((2 * Cg + 2) * (D.R.m : ℝ) ^ 2) := by
      have hQ := scale_le hbe hv hvb hg1 hgb hCg
      rw [← hka] at hQ
      have h1 : ∀ a, ‖s a‖ ≤ large₂.sc.b ^ ((2 * Cg + 2) * (D.R.m : ℝ)) := fun a =>
        (hs1 a).trans (pow_le_rpow hb1 (le_max_of_le_left (by positivity)) hQ (by linarith) (by linarith))
      rw [norm_prod]
      refine (Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun a _ => h1 _).trans ?_
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      refine (pow_le_rpow (β := D.R.m) hb1 (by positivity) le_rfl
        (mul_nonneg (by linarith) (by linarith)) (by linarith)).trans (le_of_eq ?_)
      congr 1; ring
    obtain ⟨p1, p2⟩ := hsq_le (r := D.R.rS) (l := l) hb1 hM (by linarith) (by linarith) (hTb w)
    obtain ⟨q1, q2⟩ := hsq_le (r := D.R.rS) (l := l) hb1 hM (by linarith) (by linarith) (hTb w')
    rw [hW.2.2.2.2.1] at hb₀
    rw [hW.2.2.2.2.2.1] at hb₁
    obtain ⟨c, hc, hcc⟩ := GlobalTheory.BesselDegree.schur_fdeg hH D.R.k D.R.rS (PI.BesselPeriodGGP.eps48 _ _) W.μG
      hW.2.2.2.2.2.2.1
    have hone : ∀ I, ‖a I‖ ≤ (large₂.sc.b ^ ((2 * Cg + 2) * (D.R.m : ℝ) ^ 2)) ^ 2 *
        large₂.sc.b ^ ((|CT| + 20 * max 2 Cu) * (D.R.m : ℝ) ^ 2) * large₂.sc.b ^ ((|CT| + 20 * max 2 Cu) * (D.R.m : ℝ) ^ 2) *
        large₂.sc.b ^ (max 2 Cu * (D.R.m : ℝ) ^ 2) := fun I => by
      have h3 : dg' (ν + eZ I.1) ≤ ((2 * D.R.rS + D.R.k + 1 : ℝ)) ^ l * dg ν := by
        rw [dg_eq S1 (fun mu R h => (hcc mu R h).1) hν0, dg_eq T1 (fun mu R h => (hcc mu R h).1) (firstNorm_add_subsetIndicator_le hνl I),
          mul_left_comm]
        have := (GlobalTheory.FamilyDegreeRatio.degree_ratios _ _ _ _ _ _ _ _ _ hNum ν hν0).2.1 I.1
        rw [I.2] at this
        exact mul_le_mul_of_nonneg_left this hc.le
      refine (coef_le hd0.1 (hdI I).1 (norm_nonneg _) (norm_nonneg _) (ha1 I) (hb₀ I) (hb₁ I) h3 p1 q1
        (one_le_pow₀ hn1)).trans ?_
      gcongr
    refine (Finset.sum_le_card_nsmul _ _ _ fun I _ => hone I).trans ?_
    have hcard : ((univ : Finset (Sub (2 * D.R.rS + D.R.k + 1) l)).card : ℝ) ≤
        large₂.sc.b ^ (max 2 Cu * (D.R.m : ℝ) ^ 2) := by
      refine le_trans ?_ hN
      rw [Finset.card_univ, Fintype.card_finset_len, Fintype.card_fin]
      exact_mod_cast Nat.choose_le_pow _ _
    rw [nsmul_eq_mul]
    refine (mul_le_mul_of_nonneg_right hcard (by positivity)).trans (le_of_eq ?_)
    have hb0 : 0 < large₂.sc.b := by linarith
    rw [sq (large₂.sc.b ^ _), ← Real.rpow_add hb0, ← Real.rpow_add hb0, ← Real.rpow_add hb0, ← Real.rpow_add hb0,
      ← Real.rpow_add hb0]
    congr 1; ring
  · intro μsec hsec γ p hγ θ' hθ' νR hνR
    obtain ⟨K, hK, hMM⟩ := hJ μsec hsec
    rw [hsum]
    simp only [haI]
    refine ha2 μsec K hK (hMM _ ?_ _ hA₀) (fun I hI => hMM _ ?_ _ (hAI I.1 I.2 hI)) γ p hγ θ'
      (lt_of_lt_of_le (by positivity) hθ'.1) νR hνR
    · rw [hdist]; nlinarith [sq_nonneg (D.R.m : ℝ)]
    · rw [hdist]
      have h1 : (n1 (ν + eZ I.1) : ℝ) ≤ n1 ν + l := by exact_mod_cast firstNorm_add_subsetIndicator_le (le_refl (n1 ν + l)) I
      have h2 : (l : ℝ) ≤ (D.R.m : ℝ) ^ 2 := by rw [hmR]; nlinarith
      nlinarith

end GlobalTheory.CellMinorLine
