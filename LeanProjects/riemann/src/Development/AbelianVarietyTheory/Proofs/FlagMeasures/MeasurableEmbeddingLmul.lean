import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.OnePlaceKF
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Formalism.SharpRestriction.CuspSpanNormBounds.LeadMinorK
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.DegVand
import Formalism.LocalRingCardinality.DataTies
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.BesselGapExistsFunctional
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.GapCoefficientDerivativeBound
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.BesselFunctionalSideGrowth
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.HaarEqSmul
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.DiscreteSeriesUnitarySmoothBasic
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CapParamOfIsHCTypeW
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HaarLieIsHaarOnUnipotentRadicalStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TorusNormaliserBesselStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsUnitaryTorusScaleBesselCharacterStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MomentPieriNumericsOfSizeHypsStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DiscreteSeriesBesselGapStatement
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LowerSmoothStability.ExistsFinStableOfMemSSup
import Formalism.HermitianCurvature.HermitianCurvatureProofs.UhMeasurableSet

open BranchingSupport GlobalTheory.CellAmp GlobalTheory.Amp Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.BesselSchur

theorem fdegHC_pos {n : ℕ} {mu : Fin n → ℝ} (h : StrictAnti mu) : 0 < Formalism.QuantumDeterminants.fdegHC mu := by
  unfold Formalism.QuantumDeterminants.fdegHC
  refine div_pos (Finset.prod_pos fun a _ => Finset.prod_pos fun b hb => ?_)
    (Finset.prod_pos fun a _ => Finset.prod_pos fun b hb => ?_)
  · have := h (Finset.mem_filter.1 hb).2
    exact abs_pos.2 (sub_ne_zero.2 this.ne')
  · have : (a : ℕ) < b := (Finset.mem_filter.1 hb).2
    have : ((a : ℕ) : ℝ) < ((b : ℕ) : ℝ) := by exact_mod_cast this
    linarith

theorem measurableEmbedding_lmul {k r : ℕ} {t : MatKR k r} (ht : IsUnit t.det) :
    MeasurableEmbedding (fun x : Mt k r => (fun i j => (t⁻¹ * Matrix.of x) i j : Mt k r)) := by
  have hc : ∀ s : MatKR k r, Continuous (fun x : Mt k r => (fun i j => (s * Matrix.of x) i j : Mt k r)) := fun s => by
    have h1 : Continuous (fun x : Mt k r => (Matrix.of x : MatKR k r)) := continuous_id
    exact continuous_const.matrix_mul h1
  let e : Mt k r ≃ᵐ Mt k r :=
    { toFun := fun x => fun i j => (t⁻¹ * Matrix.of x) i j
      invFun := fun x => fun i j => (t * Matrix.of x) i j
      left_inv := fun x => by
        show t * (t⁻¹ * Matrix.of x) = Matrix.of x
        rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ ht, Matrix.one_mul]
      right_inv := fun x => by
        show t⁻¹ * (t * Matrix.of x) = Matrix.of x
        rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ ht, Matrix.one_mul]
      measurable_toFun := (hc _).measurable
      measurable_invFun := (hc _).measurable }
  exact e.measurableEmbedding

theorem exists_mass_eq (hH : Hyps) {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool} {mu : Fin (2 * r + k + 1) → ℝ} {h : ℝ}
    (R : Rep k r) {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp]
    [FiniteDimensional ℂ Wp] {z : Fin (2 * r + k + 1) → ℂ} {π : MatKR k r → (Wp →L[ℂ] Wp)} {u : ℕ → ℝ} {c : ℂ}
    {μW μN μG νq : Measure (Mt k r)} {B : R.H → Wp} {w : R.H} (hc : c ≠ 0) (hDS : R.IsDS ε mu)
    (hgap : GapAtLeast ε mu h) (hok : Formalism.FourierDecayAlt.ThreeDimData.GapOK k r h) (hS : SideG k r z π u μW μN μG νq)
    (hB : PI.BesselMapUniq.IsBesselMapSm (k := k) (r := r) z (psi k r z c) R.σ π B) (hw : R.KFin w)
    (h0 : PI.BesselPeriodGGP.l2SG νq (fun g => B (R.σ g w)) ≠ 0)
    (h1 : PI.BesselPeriodGGP.l2SG νq (fun g => B (R.σ g w)) ≠ ⊤) :
    ∃ a : ℝ≥0∞, ∀ v ∈ R.sm, PI.BesselPeriodGGP.l2SG νq (fun g => B (R.σ g v)) = a * (‖v‖₊ : ℝ≥0∞) ^ 2 := by
  obtain ⟨t, htG, htN, htz, -⟩ := GlobalTheory.T.exists_unitaryTorus_scale_besselCharacter k r c hc
  obtain ⟨-, htW, htψ⟩ := htz z hS.1
  obtain ⟨hS', hR⟩ := GlobalTheory.T.torus_normaliser_bessel hH k r Wp z π u c μW μN μG νq t htG htN htW htψ hS
  obtain ⟨hmul, hone, hinn, hsm, hTK, -, hKT, -, hcont⟩ := GlobalTheory.rep_basic_of_isDS hH.1.2.2.1 k r ε mu R hDS
  have hU : Formalism.MainNotions.S.IsURepOn (BranchingSupport.GG k r) R.σ := by
    refine ⟨⟨?_, ?_⟩, fun g hg v => ?_, hcont⟩
    · ext v; simpa using hone v
    · intro a ha b hb; ext v; simpa using hmul a ha b hb v
    · have := hinn g hg v v
      rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at this
      have h2 : ‖R.σ g v‖ ^ 2 = ‖v‖ ^ 2 := by exact_mod_cast this
      exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h2
  have hB' := ((hR R hU).1 B).1 hB
  obtain ⟨htu, htinv, -⟩ := PI.UnitaryGroupMassFormula.CapelliEig.unitary_Hecke_group k r t htG
  have hdet : IsUnit t.det := (Matrix.isUnit_iff_isUnit_det t).mp htu
  have hae : ∀ {μN νq : Measure (Mt k r)}, SideG k r z π u μW μN μG νq →
      ∀ᵐ x ∂νq, Matrix.of x ∈ UH (Hpk k r) := fun hS => by
    obtain ⟨-, -, -, -, hW, hN, hG, hq⟩ := hS
    obtain ⟨hS0, hS1⟩ := Formalism.FourierDecayAlt.P.DDSmoothness.muSof_facts hW hN
    exact Formalism.FourierDecayAlt.P.DDSmoothness.ae_UH_of_quot hG.2.2.1 hS0 hS1 hq
  have hmove : ∀ v, PI.BesselPeriodGGP.l2SG (νq.map fun x => fun i j => (t⁻¹ * Matrix.of x) i j)
      (fun g => B (R.σ t (R.σ g v))) = PI.BesselPeriodGGP.l2SG νq (fun g => B (R.σ g v)) := fun v => by
    unfold PI.BesselPeriodGGP.l2SG
    rw [(measurableEmbedding_lmul hdet).lintegral_map]
    refine lintegral_congr_ae ?_
    filter_upwards [hae hS] with x hx
    have e : R.σ t (R.σ (t⁻¹ * Matrix.of x) v) = R.σ (Matrix.of x) v := by
      rw [← hmul t htG _ (Formalism.FourierDecayAlt.P.DDSmoothness.uh_mul htinv hx), ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hdet,
        Matrix.one_mul]
    exact congrArg (fun y => ((‖B y‖₊ : ℝ≥0∞)) ^ 2) e
  obtain ⟨l, hl⟩ := GlobalTheory.exists_normalised_bessel_map hH k r ε mu h R Wp z π u _ _ _ _ hDS hgap hok hS'
  obtain ⟨v₁, hv₁, hlv⟩ := GlobalTheory.T.discrete_series_bessel_gap hH k r ε mu h R Wp z π u _ _ _ _ _ l w hDS hgap hok hS' hB' hw
    (by rw [hmove]; exact h0) (by rw [hmove]; exact h1) hl
  obtain ⟨c₀, hc₀, hfd⟩ := GlobalTheory.BesselDegree.schur_fdeg hH k r ε μG hS.2.2.2.2.2.2.1
  have hdd : 0 < c₀ * Formalism.QuantumDeterminants.fdegHC mu := mul_pos hc₀ (fdegHC_pos hDS.1.1)
  have hv₁s : v₁ ∈ R.sm := hTK _ (hKT _ hv₁)
  obtain ⟨hb, hiso⟩ := GlobalTheory.scaled_bessel_isometric hH k r ε mu h R Wp z π u _ _ _ _ l _ hDS hgap hok hS' hl
    (hfd mu R hDS).1 ⟨v₁, hv₁s, hlv⟩
  obtain ⟨a, ha⟩ := GlobalTheory.BesselLine.bessel_line hH k r ε mu R Wp z π u _ _ _ _ _ _ hDS hS' hb
    ⟨v₁, hv₁s, smul_ne_zero (Complex.ofReal_ne_zero.2 (Real.sqrt_pos.2 hdd).ne') hlv⟩ hB'
  refine ⟨(‖a‖₊ : ℝ≥0∞) ^ 2, fun v hv => ?_⟩
  have e : ((‖v‖₊ : ℝ≥0∞)) ^ 2 = ENNReal.ofReal (‖v‖ ^ 2) := by
    rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]; rfl
  rw [← hmove, e, ← hiso v hv]
  unfold PI.BesselPeriodGGP.l2SG
  rw [← lintegral_const_mul' _ _ (ENNReal.pow_ne_top ENNReal.coe_ne_top)]
  refine lintegral_congr_ae ?_
  filter_upwards [hae hS'] with x hx
  rw [ha _ (hsm _ hx v hv), nnnorm_smul, ENNReal.coe_mul, mul_pow]

theorem isBesselMapSm_of {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {Wp : Type}
    [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] {z : Fin (2 * r + k + 1) → ℂ} {ψ : MatKR k r → ℂ}
    {σ : MatKR k r → (H →L[ℂ] H)} {π : MatKR k r → (Wp →L[ℂ] Wp)} {B : H → Wp} (h : IsBesselMapSm z ψ σ π B) :
    PI.BesselMapUniq.IsBesselMapSm (k := k) (r := r) z ψ σ π B := by
  have e : ∀ (w : List (MatKR k r)) (v : H), PI.UpqRep.dsigW (k := k) (r := r) σ w v = dsigW σ w v := fun w v => by
    induction w with
    | nil => rfl
    | cons X w ih => exact congrArg (dsig σ X) ih
  obtain ⟨h1, h2, h3, C, Ws, h4, h5⟩ := h
  refine ⟨h1, h2, h3, C, Ws, h4, fun v hv => ?_⟩
  simpa only [e] using h5 v hv

theorem bessel_schur : Hyps → ∀ (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT C0 : ℝ), 1000 ≤ Cl → (∀ τ w w' θ (W : LocW D.R.k D.R.rS), GoodW D τ w w' θ W → 0 < θ) → (∀ w, 0 < Tr D w) → BSch D large₂ C' Cl Cg cb Cu cT CT C0 := by
  intro hH D large₂ C' Cl Cg cb Cu cT CT C0 hCl hθ _ hZ τ w w' θ W hW A hA hT v hv
  have hθ0 := hθ τ w w' θ W hW
  have := FiniteDimensional.complete ℂ W.Wp
  have hU : ∀ i : Fin D.R.k, uOne D w τ (i.val + 1) = uS D w τ i := fun i => by
    unfold uOne
    rw [dif_pos ⟨by omega, i.isLt⟩]
    rfl
  obtain ⟨hnum, -, heps⟩ := GlobalTheory.T.momentPieriNumerics_of_sizeHyps D large₂ C' Cl Cg cb Cu cT CT C0 hZ hCl τ w _ hU
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hgap, hok, -, hh, -⟩ := hnum
  rw [heps] at hgap
  have hgap' : GapAtLeast (epsSH D.R) (lamD D τ) ((D.R.r : ℝ) ^ 19 / 4) := fun a b hab =>
    le_trans (by have : (0 : ℝ) ≤ (D.R.r : ℝ) ^ 19 := by positivity
                 linarith) (hgap a b hab)
  have hv1 : 1 ≤ D.host.v := hZ.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hvpos : 0 < D.host.v := by linarith
  obtain ⟨c1, -, z1, -, t1, -, hG, w1, -, -, -, hN, q1, -⟩ := hW
  obtain ⟨hpar, hds, b1, -, hsm, hv0, ⟨P, hP, hlow⟩, hc, l1, -, -⟩ := hA
  have hTz : 0 < Tz D.R.k D.R.rS W.z := by rw [t1]; exact hT
  have hNH : IsHaarOn (Nset D.R.k D.R.rS) W.μN := by
    rw [hN]
    exact GlobalTheory.T.haarLie_isHaarOn_unipotentRadical _ _ _ (ENNReal.ofReal_pos.2 (by positivity)) ENNReal.ofReal_lt_top
  have hS : SideG D.R.k D.R.rS W.z W.π (uOne D w τ) W.μW W.μN W.μG W.νS :=
    ⟨z1, hTz, ⟨_, c1⟩, GlobalTheory.ThA.capParam_of_isHCTypeW _ _ _ _ _ _ _ z1 hTz c1 hU, w1, hNH, hG, q1⟩
  have hka : 0 < D.host.ka := div_pos Real.pi_pos hvpos
  have hg0 : (0 : ℝ) < D.host.g 0 := by exact_mod_cast (D.host.g_prime 0).pos
  have hg1 : (0 : ℝ) < D.host.g 1 := by exact_mod_cast (D.host.g_prime 1).pos
  have hcne : ((2 * D.host.ka / ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)) : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.2 (by positivity)
  have hKF : (⟨A.H, A.σ⟩ : Rep D.R.k D.R.rS).KFin A.v0 := by
    obtain ⟨S, ⟨hfd, hst⟩, hwS⟩ := PI.UnitaryGroupMassFormula.LowSmooth.exists_finStable_of_mem_sSup (Formalism.REAL.Kset (epsSH D.R))
      (fun g => A.σ (P⁻¹ * g * P))
      (F := {S | IsKTypeOf (epsSH D.R) (fun g => A.σ (P⁻¹ * g * P)) (lowK (epsSH D.R) (lamD D τ)) S})
      (fun S hS => ⟨hS.1, hS.2.1⟩) hlow
    refine ⟨S, hfd, hwS, fun g hg x hx => ?_⟩
    obtain ⟨hK, hback⟩ := PI.UnitaryGroupMassFormula.LowSmooth.conj_mem_Kset hP hg
    have h := hst _ hK x hx
    simp only at h
    rwa [hback] at h
  have hnt : Nontrivial W.Wp := by
    obtain ⟨g, -, hnt, -⟩ := c1
    exact hnt
  have hrk : (0 : ℝ) < Module.finrank ℂ W.Wp := by exact_mod_cast Module.finrank_pos
  have l1' : PI.BesselPeriodGGP.l2SG W.νS (fun g => A.B (A.σ g A.v0)) =
      ENNReal.ofReal (A.cN * Module.finrank ℂ W.Wp) := l1
  obtain ⟨a, ha⟩ := exists_mass_eq hH (⟨A.H, A.σ⟩ : Rep D.R.k D.R.rS) (B := A.B) (w := A.v0) hcne ⟨hpar, hds⟩ hgap' hok
    hS (isBesselMapSm_of b1) hKF (by rw [l1']; exact (ENNReal.ofReal_pos.2 (mul_pos hc hrk)).ne') (by rw [l1']; exact ENNReal.ofReal_ne_top)
  have e1 : l2SG W.νS (fun g => A.B (A.σ g v)) = a * (‖v‖₊ : ℝ≥0∞) ^ 2 := ha v hv
  have e2 : l2SG W.νS A.Φ = a * (‖A.v0‖₊ : ℝ≥0∞) ^ 2 := ha A.v0 hsm
  rw [e1, e2]
  ring

theorem theta_pos (D : D7) {τ : D.what₂.Tau} {w w' : D.what₂.Word} {θ : ℝ} {W : LocW D.R.k D.R.rS}
    (hv : 0 ≤ D.host.v) (hW : GoodW D τ w w' θ W) : 0 < θ := by
  by_contra hθ
  obtain ⟨-, -, -, -, -, -, hG, -, -, -, -, hN, q1, -⟩ := hW
  have hk : kapN D θ = 0 :=
    ENNReal.ofReal_eq_zero.2 (mul_nonpos_of_nonneg_of_nonpos (Real.rpow_nonneg (by positivity) _) (not_lt.1 hθ))
  have hN0 : W.μN = 0 := by rw [hN, hk]; unfold haarLie; exact zero_smul _ _
  have h1 := q1 (fun _ => 1) measurable_const
  rw [hN0] at h1
  simp only [muS, Measure.prod_zero, Measure.map_zero, lintegral_const, one_mul, Measure.coe_zero,
    Pi.zero_apply, zero_mul] at h1
  exact hG.2.1 (Measure.measure_univ_eq_zero.1 h1)

end GlobalTheory.BesselSchur
