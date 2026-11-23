import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.UniqGapOfUniq
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.OnePlaceKF
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Formalism.SharpRestriction.CuspSpanNormBounds.LeadMinorK
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.DegVand
import Formalism.LocalRingCardinality.DataTies
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FirstNormAddSubsetIndicatorLe
import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.TensorMomentEstimateStatement
import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.FamilySetupBesselGrowthStatement
import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.HaarEqSmul
import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.PieriTensorDecompositionStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AmplitudeEqSmulNormalisedAmplitudeLargeGapStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NormalizedBesselMapsAnyScalePieriConstants
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AmplitudePieriRelevantCellLargeGapStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DatumDegreeEqMulFormalDegreeGap
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsGoodLocalDatumOfNonzeroPeriodsGapStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AmplitudeLocalDataMomentPieriHypothesesStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselExteriorPowerConstantBoundLargeGapStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FamiliesHaveLargeGapOfNumericalHypothesesStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.OpenCellAmplitudeNormEqConstDivDegreeLargeGapStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TrivialWedgeDecompositionDiscreteSeriesLargeGapsStatement

open BranchingSupport GlobalTheory.CellAmp GlobalTheory.Amp Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.CellMinorLineGap

open GlobalTheory.CellMinorLine GlobalTheory.BesselMove

variable {k r q0 : ℕ}

theorem exists_famG (hH : GlobalTheory.GapIn.Hyp) {lam : Fin (2 * r + k + 1) → ℝ}
    (hlam : ∀ ν : Fin (2 * r + k + 1) → ℤ, n1 ν ≤ q0 → IsHCParam fun a => lam a + (ν a : ℝ))
    (hgap : ∀ ν : Fin (2 * r + k + 1) → ℤ, n1 ν ≤ q0 → ∃ h, GapAtLeast (PI.BesselPeriodGGP.eps48 k r)
      (fun a => lam a + (ν a : ℝ)) h ∧ Formalism.FourierDecayAlt.ThreeDimData.GapOK k r h)
    (hP : ∃ P, PI.UpqRep.IsCayleyU k r (PI.BesselPeriodGGP.eps48 k r) P) {ι : Type}
    (p : ι → Fin (2 * r + k + 1) → ℤ) (hp : Function.Injective p) (X : ι → Rep k r)
    (hX : ∀ i, (X i).IsDG (PI.BesselPeriodGGP.eps48 k r) fun a => lam a + (p i a : ℝ)) (R₀ : Rep k r) :
    ∃ R, IsFamG lam q0 R ∧ ∀ i, R (p i) = X i := by
  have h1 : ∀ ν : Fin (2 * r + k + 1) → ℤ, ∃ R : Rep k r, (∀ i, p i = ν → R = X i) ∧
      (n1 ν ≤ q0 → R.IsDG (PI.BesselPeriodGGP.eps48 k r) fun a => lam a + (ν a : ℝ)) := by
    intro ν
    by_cases h : ∃ i, p i = ν
    · obtain ⟨i, rfl⟩ := h
      exact ⟨X i, fun j hj => by rw [hp hj], fun _ => hX i⟩
    · by_cases hq : n1 ν ≤ q0
      · obtain ⟨R, hR⟩ := hH.1.2.2.2.1 k r _ _ (hlam ν hq) hP (hgap ν hq)
        exact ⟨R, fun i hi => absurd ⟨i, hi⟩ h, fun _ => hR⟩
      · exact ⟨R₀, fun i hi => absurd ⟨i, hi⟩ h, fun h' => absurd h' hq⟩
  choose R h2 h3 using h1
  exact ⟨R, fun ν hν => h3 ν hν, fun i => h2 _ i rfl⟩

theorem isFam_of_isFamG {lam : Fin (2 * r + k + 1) → ℝ} {R : (Fin (2 * r + k + 1) → ℤ) → Rep k r}
    (h : IsFamG lam q0 R) : IsFam lam q0 R := fun ν hν => GlobalTheory.isDS_of_isDG (h ν hν)

theorem amp_eq (hH : GlobalTheory.GapIn.Hyp) (D : D7) {τ w w' θ} {W : LocW D.R.k D.R.rS} [CompleteSpace W.Wp]
    [CompleteSpace W.Wq]
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
  exact GlobalTheory.T.amplitude_eq_smul_normalisedAmplitude_largeGap hH D τ w w' θ W lam A h l l' hθ hka hT hT' hW hA hg hok b1 b2 e1 e2

set_option maxHeartbeats 1000000 in

theorem line_of_tens (hH : GlobalTheory.GapIn.Hyp) (hKF : GlobalTheory.GapIn.AmpKF0) (hCC : CellConv) (D : D7) {τ w w' θ}
    {W : LocW D.R.k D.R.rS}
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
  obtain ⟨c, hc, hdeg⟩ := GlobalTheory.GapDegreeTie.deg_eq_mul_fdegH hH D τ w w' θ W hcd hW
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
  have key := GlobalTheory.T.amplitude_pieri_relevantCell_largeGap hH hKF hCC D.R.k D.R.rS _ _ (cmp l) (cmp l (Hpk D.R.k D.R.rS)) l
    (toBessel D τ w w' θ W lam A₀ hW hA₀ hT hT') R RI io pr ep lam lamI h W.μG _ _ B B' BI BI' w0 wI κ₀ κ₁
    hDS hg hDI hok hgc hc0 ENNReal.ofReal_ne_top hW.2.2.2.2.2.2.1 (GlobalTheory.WedgeFRep.isFRep_cmp _ _ l) hTH
    (GlobalTheory.T.flagWedge_fixed_and_length_eq_prod_distances _ _ l hl W.z hW.2.2.1).1 (GlobalTheory.T.flagWedge_fixed_and_length_eq_prod_distances _ _ l hl W.z' hW.2.2.2.1).1 e1 e2
    (fun I => ⟨eI1 I, eI2 I⟩) n1 n2 hw0 hwI hκ g₀ μR ν₀ ν hcell
  rw [GlobalTheory.PrincipalMinorExterior.pairing_eq_leading_minor, hd _ (ne_zero_of_low hw0)] at key
  have hDm : DminN W.z W.z' g₀ l =
      ((Zhat D.R.k D.R.rS W.z W.z' g₀).submatrix (Fin.castLE hl) (Fin.castLE hl)).det := by
    rw [DminN, dif_pos (by omega)]; rfl
  have hdc : (d : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hd0.ne'
  rw [hD, jhUnit, hs _ _ hA₀, hJ _ _ hcell.1 hν₀, hM,
    deg_eq hR (fun v hv => hdeg _ _ hA₀ ⟨h, hg, hok⟩ v hv) hd (ne_zero_of_low hw0)]
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
      deg_eq (hRI I hI) (fun v hv => hdeg _ _ (hAI I hI) ⟨h, (hDI I).2, hok⟩ v hv) (hdI I)
        (ne_zero_of_low (hwI I)), hMd,
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

theorem moved (hH : GlobalTheory.GapIn.Hyp) {u : ℕ → ℝ} {c : ℂ} (ht : t ∈ GG k r)
    (hN : ∀ n, n ∈ Nset k r ↔ t * n * t⁻¹ ∈ Nset k r)
    (hc : ∀ h ∈ UWset k r z, t * h = h * t)
    (hψ : ∀ n ∈ Nset k r, psi k r z cStd n = psi k r z c (t * n * t⁻¹)) (hS : SideG k r z π u μW μN μG νq)
    {R : Rep k r} {ε mu} (hR : R.IsDS ε mu) {l₁ : R.H → Wp}
    (hl : IsBeL R z π μW (μN.map fun x => fun i j => (t⁻¹ * Matrix.of x * t) i j) l₁) :
    PI.BesselMapUniq.IsBesselMapSm (k := k) (r := r) z (psi k r z c) R.σ π (fun v => l₁ (R.σ t⁻¹ v)) ∧
    ∀ x ∈ R.sm, ∀ v ∈ R.TK, Formalism.FourierDecayAlt.ThreeDimData.be z c π R.σ μW μN x v =
      (innerSL ℂ (l₁ (R.σ t⁻¹ v))).smulRight (l₁ (R.σ t⁻¹ x)) := by
  have hU := urep_of_isDS hR
  obtain ⟨h1, h2⟩ := (GlobalTheory.BesselMoveGap.bessel_move_gap hH k r Wp z π u c μW μN μG νq t ht hN hc hψ hS).2 R hU
  refine ⟨(h1 _).2 ?_, h2 l₁ hl⟩
  have e : (fun v => l₁ (R.σ t⁻¹ (R.σ t v))) = l₁ := by
    funext v
    rw [← sig_mul hU (inv_mem ht) ht, inv_mul' ht, sig_one hU]
  rw [e]
  exact hl.1

omit [FiniteDimensional ℂ Wp] in
theorem dg_eq {lam u b bv ga h R l dg}
    (hS : SetupG (k := k) (r := r) lam u b bv ga h q0 z π μW μN μG νq R l dg) {c : ℝ}
    (hc : ∀ mu (R : Rep k r), R.IsDG (PI.BesselPeriodGGP.eps48 k r) mu → ∀ w, w ≠ 0 →
      PI.BesselPeriodGGP.fdegH μG R.σ w = c * fdegHC mu) {ν} (hν : n1 ν ≤ q0) :
    dg ν = c * fdegHC fun a => lam a + (ν a : ℝ) := by
  obtain ⟨w, -, hw⟩ := GlobalTheory.exists_isLowUnitH_of_isDSHpk (hS.2.1 ν hν).2
  rw [← (hS.2.2.2 ν hν).2.2 w (ne_zero_of_low hw), hc _ _ (hS.2.1 ν hν) w (ne_zero_of_low hw)]

omit [FiniteDimensional ℂ Wp] in
theorem setupG_of {lam u b bv ga h R l dg}
    (hS : Setup (k := k) (r := r) lam u b bv ga h q0 z π μW μN μG νq R l dg) :
    SetupG (k := k) (r := r) lam u b bv ga h q0 z π μW μN μG νq R l dg :=
  (GlobalTheory.T.families_have_largeGap_of_numericalHypotheses.2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).1 hS

theorem side_kappa (hH : GlobalTheory.GapIn.Hyp) (ht : t ∈ GG k r) {lam u u' b bv ga h F F' l₁ m₁ dg dg'}
    {μN' : Measure (Mt k r)}
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
  have hSG := setupG_of hS
  have hSG' := setupG_of hS'
  have hν0 : n1 ν ≤ q0 := by omega
  have hνl : n1 ν + l ≤ q0 := by nlinarith
  have hR := hS.2.1 ν hν0
  have hRG := hSG.2.1 ν hν0
  have hRIG := fun J : Sub (2 * r + k + 1) l => hSG'.2.1 _ (firstNorm_add_subsetIndicator_le hνl J)
  have hRI := fun J : Sub (2 * r + k + 1) l => hS'.2.1 _ (firstNorm_add_subsetIndicator_le hνl J)
  have hU := urep_of_isDS hR
  have hb := GlobalTheory.rep_basic_of_isDS hH.1.1.2.2.1 k r _ _ _ hR
  have hnz' : NzOn (F ν) (l₁ ν) := by
    obtain ⟨v, hv, hv0⟩ := hnz
    exact ⟨_, sig_sm hU (inv_mem ht) (hb.2.2.2.2.1 v (hb.2.2.2.2.2.2.1 v hv)), hv0⟩
  obtain ⟨⟨κ₁, hκ⟩, hdual⟩ := Gp91.GlobalTheory.T.bessel_tensor_projection_scalar_and_adjoint hH.1 k r _ _ _ _ l _ _ io pr ep _ _ _ Wp z π u μW μN' μG _ _
    (l₁ ν) hRG hRIG (GlobalTheory.WedgeFRep.isFRep_cmp k r l) hT hS.2.2.1 (GlobalTheory.T.flagWedge_fixed_and_length_eq_prod_distances k r l hl z hS.2.2.1.1).1
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
    · obtain ⟨c, -, hc⟩ := Gp91.GlobalTheory.BesselDegree.schur_fdeg hH.1 k r (PI.BesselPeriodGGP.eps48 k r) μG
        hS.2.2.1.2.2.2.2.2.2.1
      have e : ν + eZ I.1 = ν := by
        rw [Finset.card_eq_zero.1 I.2]; funext a; simp [eZ]
      have e2 : dg' (ν + eZ I.1) = dg ν := by
        rw [e, dg_eq hSG (fun mu R h => (hc mu R h).1) hν0, dg_eq hSG' (fun mu R h => (hc mu R h).1) hν0]
      rw [e2, mul_div_assoc, div_self (hS.2.2.2 ν hν0).2.1.ne', mul_one, pow_zero]
      exact kappa_zero hT _ I hκ (hdual κ₁ hκ) (hnI h0)
    · obtain rfl := eq_of_heq h2
      exact GlobalTheory.T.besselExteriorPower_constant_bound_largeGap hH k r Wp lam u b bv ga h q0 z π μW μN' μG _ _ _ _ hS l hl ν hν io pr ep hT hnz' I κ₁
        (hnI h0) hκ
  · exact mass_move (urep_of_isDS (hRI I)) ht (hS'.2.2.2 _ (firstNorm_add_subsetIndicator_le hνl I)).2.1
      (GlobalTheory.quotMeas_ae_mem_and_measurable hH.1.1.2.2.1 k r _ _ _ Wp z π u μW μN' μG _ hR hS.2.2.1).1
      (((Gp91.GlobalTheory.T.bessel_functional_l2_bound_and_isometry hH.1 k r Wp lam u' b bv ga h q0 z π μW μN' μG _ F' m₁ dg' hSG' _ (firstNorm_add_subsetIndicator_le hνl I)).2
        (hnI (right_ne_zero_of_mul h0))).2 v hv)

end side

theorem tens_zero : HypsG → ∀ (k r : ℕ) (lam : Fin (2 * r + k + 1) → ℝ) (u : ℕ → ℝ) (b bv ga h : ℝ) (q0 : ℕ)
    (F F' : (Fin (2 * r + k + 1) → ℤ) → Rep k r) (ν : Fin (2 * r + k + 1) → ℤ), Num k r lam u b bv ga h q0 →
    IsFamG lam q0 F → IsFamG lam q0 F' → n1 ν + 2 ≤ q0 →
    ∃ io pr ep, TensH (cmp 0) (cmp 0 (Hpk k r)) (F ν) (fun I : Sub (2 * r + k + 1) 0 => F' (ν + eZ I.1)) io pr ep :=
  GlobalTheory.T.trivialWedgeDecomposition_discreteSeries_largeGaps

theorem exists_fams (hH : GlobalTheory.GapIn.Hyp) {lam : Fin (2 * r + k + 1) → ℝ}
    (hlam : ∀ ν : Fin (2 * r + k + 1) → ℤ, n1 ν ≤ q0 → IsHCParam fun a => lam a + (ν a : ℝ))
    (hgap : ∀ ν : Fin (2 * r + k + 1) → ℤ, n1 ν ≤ q0 → ∃ h, GapAtLeast (PI.BesselPeriodGGP.eps48 k r)
      (fun a => lam a + (ν a : ℝ)) h ∧ Formalism.FourierDecayAlt.ThreeDimData.GapOK k r h)
    (hP : ∃ P, PI.UpqRep.IsCayleyU k r (PI.BesselPeriodGGP.eps48 k r) P) {l : ℕ} (ν : Fin (2 * r + k + 1) → ℤ)
    (R₀ : Rep k r) (h0 : R₀.IsDG (PI.BesselPeriodGGP.eps48 k r) fun a => lam a + (ν a : ℝ))
    (gd : Sub (2 * r + k + 1) l → Prop) (X : Sub (2 * r + k + 1) l → Rep k r)
    (hX : ∀ I, gd I → (X I).IsDG (PI.BesselPeriodGGP.eps48 k r) fun a => lam a + ((ν + eZ I.1) a : ℝ)) :
    ∃ F F', IsFamG lam q0 F ∧ IsFamG lam q0 F' ∧ F ν = R₀ ∧ (∀ I, gd I → F' (ν + eZ I.1) = X I) ∧
      (l = 0 ∨ F' = F) := by
  by_cases hl : l = 0
  · obtain ⟨F, hF, h1⟩ := exists_famG hH hlam hgap hP (fun _ : Unit => ν) (fun _ _ _ => rfl) (fun _ => R₀)
      (fun _ => h0) R₀
    obtain ⟨F', hF', h2⟩ := exists_famG hH hlam hgap hP (fun I : {I // gd I} => ν + eZ I.1.1)
      ((eZ_inj ν).comp Subtype.val_injective) (fun I => X I.1) (fun I => hX I.1 I.2) R₀
    exact ⟨F, F', hF, hF', h1 (), fun I hI => h2 ⟨I, hI⟩, Or.inl hl⟩
  · have hne : ∀ I : Sub (2 * r + k + 1) l, ν ≠ ν + eZ I.1 := fun I h => by
      obtain ⟨a, ha⟩ := Finset.card_pos.1 (by rw [I.2]; omega : 0 < I.1.card)
      have := congrFun h a
      simp [eZ, ha] at this
    obtain ⟨F, hF, h1⟩ := exists_famG hH hlam hgap hP
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

set_option maxHeartbeats 1000000 in

theorem minor_line : GlobalTheory.GapIn.Hyp → GlobalTheory.GapIn.AmpKF0 → CellConv → ∀ Cg cb Cu cT CT C0 C1 : ℝ, ∃ C : ℝ, ∀ Cn : ℝ, ∃ m₀ : ℝ, ∀ (D : D7) (large₂ : SizeData₂ D) (C' Cl : ℝ), 1000 ≤ Cl → Big D large₂ Cl m₀ → cdScaleTie D → HypZ D large₂ C' Cl Cg cb Cu cT CT C0 → ∀ τ w w', HypTT D w w' → ∀ θ, normWin D large₂ C1 θ → ∀ W, GoodW D τ w w' θ W → ∀ lam', l1dist lam' (lamD D τ) ≤ Cn * D.R.k * (D.R.m : ℝ) ^ 3 → ∀ A₀ : LocS W, GoodS D lam' A₀ → ∀ l : ℕ, l ≤ D.R.rS + 1 → ∃ s : ℝ, (s = 1 ∨ s = -1) ∧ ∀ AI : Finset (Fin (2 * D.R.rS + D.R.k + 1)) → LocS W, (∀ I, I.card = l → (∃ A : LocS W, GoodS D (lam' + s • epsI I) A) → GoodS D (lam' + s • epsI I) (AI I)) → ∃ a : Finset (Fin (2 * D.R.rS + D.R.k + 1)) → ℂ, (∀ I, I.card = l → (¬ ∃ A : LocS W, GoodS D (lam' + s • epsI I) A) → a I = 0) ∧ (∑ I ∈ univ.filter (fun I => I.card = l), ‖a I‖) ≤ large₂.sc.b ^ (C * (D.R.m : ℝ) ^ 2) ∧ ∀ μsec, IsSection D.R.k D.R.rS W.z W.z' μsec → ∀ γ p, RelPt D W.z W.z' γ p → ∀ θ', normWin D large₂ C1 θ' → ∀ νR, RMeas D W γ θ' νR → DminN W.z W.z' γ l • jhUnit D w w' A₀ μsec νR γ = ∑ I ∈ univ.filter (fun I => I.card = l), a I • jhUnit D w w' (AI I) μsec νR γ := by
  intro hH hKF hCC Cg cb Cu cT CT C0 C1
  refine ⟨2 * (2 * Cg + 2) + 2 * (|CT| + 20 * max 2 Cu) + 2 * max 2 Cu, fun Cn => ?_⟩
  obtain ⟨m₁, hJ⟩ := GlobalTheory.T.openCellAmplitudeNorm_eq_const_div_degree_largeGap hH hKF hCC Cg cb Cu cT CT C0 C1 (Cn + 1)
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
  have hgapF : ∀ μ : Fin (2 * D.R.rS + D.R.k + 1) → ℤ, n1 μ ≤ D.R.k * D.R.m ^ 5 →
      ∃ h, GapAtLeast (PI.BesselPeriodGGP.eps48 D.R.k D.R.rS) (fun a => lamD D τ a + (μ a : ℝ)) h ∧
        Formalism.FourierDecayAlt.ThreeDimData.GapOK D.R.k D.R.rS h := fun μ hμ => ⟨_, (hnum μ hμ).2.2.1, hok⟩
  obtain ⟨F, F', hFG, hFG', hF0, hFI, hFF⟩ := exists_fams hH (fun μ h => (hnum μ h).1) hgapF
    (by rw [heps]; obtain ⟨P, hP, -⟩ := hA₀.2.1; exact ⟨P, hP⟩) ν ⟨A₀.H, A₀.σ⟩
    (by
      refine ⟨?_, ?_, hgapF ν hν0⟩
      · exact hA₀.1
      · rw [heps]; exact hA₀.2.1)
    (fun I : Sub _ l => ∃ A : LocS W, GoodS D (fun a => lamD D τ a + ((ν + eZ I.1) a : ℝ)) A)
    (fun I => ⟨(AI I.1).H, (AI I.1).σ⟩)
    (fun I hI => by
      refine ⟨?_, ?_, hgapF _ (firstNorm_add_subsetIndicator_le hνl I)⟩
      · exact (hAI I.1 I.2 hI).1
      · rw [heps]; exact (hAI I.1 I.2 hI).2.1)
  have hF := isFam_of_isFamG hFG
  have hF' := isFam_of_isFamG hFG'
  have hc0 : ((2 * D.host.ka / ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)) : ℝ) : ℂ) ≠ 0 := by
    rw [Complex.ofReal_ne_zero, mul_div_assoc]
    exact (mul_pos two_pos hka0).ne'
  obtain ⟨t, ht, hNt, hz, hs⟩ := GlobalTheory.TorusScale.exists_torus_scale D.R.k D.R.rS _ hc0
  choose s hs0 hs1 hs2 hs3 using hs
  have hmod := GlobalTheory.T.amplitudeLocalData_momentPieriHypotheses hH D large₂ C' Cl Cg cb Cu cT CT C0 hZ hCl τ w w' θ W hTT hθ hW t ht hNt
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
    rcases hFF with h0 | h1
    · subst h0
      exact tens_zero hH.1 _ _ _ _ _ _ _ _ _ F F' ν hNum hFG hFG' (by nlinarith)
    · rw [h1]
      exact (Gp91.GlobalTheory.T.pieri_tensor_decomposition hH.1 _ _ _ _ _ _ _ _ _ F hNum hFG ν).1 l hνl
  obtain ⟨b1, e1⟩ := moved hH ht hNt (hz _ z1).2.1 (hz _ z1).2.2 G1 hDS (S1.2.2.2 ν hν0).1
  obtain ⟨b2, e2⟩ := moved hH ht hNt (hz _ z2).2.1 (hz _ z2).2.2 G2 hDS (S2.2.2.2 ν hν0).1
  have bI1 := fun I : Sub _ l => moved hH ht hNt (hz _ z1).2.1 (hz _ z1).2.2 G1 (hDI I) (T1.2.2.2 _ (firstNorm_add_subsetIndicator_le hνl I)).1
  have bI2 := fun I : Sub _ l => moved hH ht hNt (hz _ z2).2.1 (hz _ z2).2.2 G2 (hDI I) (T2.2.2.2 _ (firstNorm_add_subsetIndicator_le hνl I)).1
  have hDIG := fun I : Sub _ l => hFG' _ (firstNorm_add_subsetIndicator_le hνl I)
  have hgap := fun μ h => (hnum μ h).2.2.1
  rw [heps] at hDS hDI hgap hDIG
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
      exact hI (GlobalTheory.T.exists_goodLocalDatum_of_nonzero_periods_gap hH D τ w w' θ W _ _ 0 _ _ _ hcd hW (hDIG I) (bI1 I).1 (bI2 I).1 (hdI I).1
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
    obtain ⟨c, hc, hcc⟩ := Gp91.GlobalTheory.BesselDegree.schur_fdeg hH.1 D.R.k D.R.rS (PI.BesselPeriodGGP.eps48 _ _) W.μG
      hW.2.2.2.2.2.2.1
    have S1G := setupG_of S1
    have T1G := setupG_of T1
    have hone : ∀ I, ‖a I‖ ≤ (large₂.sc.b ^ ((2 * Cg + 2) * (D.R.m : ℝ) ^ 2)) ^ 2 *
        large₂.sc.b ^ ((|CT| + 20 * max 2 Cu) * (D.R.m : ℝ) ^ 2) * large₂.sc.b ^ ((|CT| + 20 * max 2 Cu) * (D.R.m : ℝ) ^ 2) *
        large₂.sc.b ^ (max 2 Cu * (D.R.m : ℝ) ^ 2) := fun I => by
      have h3 : dg' (ν + eZ I.1) ≤ ((2 * D.R.rS + D.R.k + 1 : ℝ)) ^ l * dg ν := by
        rw [dg_eq S1G (fun mu R h => (hcc mu R h).1) hν0, dg_eq T1G (fun mu R h => (hcc mu R h).1) (firstNorm_add_subsetIndicator_le hνl I),
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

end GlobalTheory.CellMinorLineGap
