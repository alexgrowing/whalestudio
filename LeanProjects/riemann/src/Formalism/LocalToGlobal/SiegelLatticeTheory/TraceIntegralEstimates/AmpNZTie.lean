import Formalism.SharpRestriction.CuspSpanNormBounds.FrobeniusCoefficientMemLp.BetaCut
import Formalism.SharpRestriction.CuspSpanNormBounds.FrobeniusCoefficientMemLp.FramesTurn
import Formalism.SharpRestriction.CuspSpanNormBounds.FrameBlockSums
import Formalism.SharpRestriction.CuspSpanNormBounds.BigCellDensity
import Formalism.SharpRestriction.CuspSpanNormBounds.LowestKTypeMultiplicity
import Formalism.SharpRestriction.CuspSpanNormBounds.FrobeniusCoefficientMemLp.AmpBig
import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.OrderedAtRanksOfPositionElement
import Formalism.SharpRestriction.CuspSpanNormBounds.FrobeniusCoefficientMemLp.SigmaFiniteAmplitudes.SigmaFiniteOfUnfold
import Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.PeriodG
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BXiAsm

set_option linter.unusedVariables false

open MeasureTheory Matrix
open scoped ENNReal InnerProductSpace

noncomputable section

namespace Formalism.L2.S.Pv.AmpNZTie

open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.MainNotions.FrameBoundFromBesselTorus Formalism.MainNotions.S.Pv.Frames Formalism.MainNotions.S.Pv.LemmaJ

variable {k r : ℕ}

abbrev stdL (L : LocBessel k r) (ka : ℝ) (hka : 0 < ka) : LocBessel k r :=
  trDat (turnL L ka) ka⁻¹ 1 (inv_pos.2 hka) one_pos

abbrev stdF (L : LocBessel k r) (ka : ℝ) (f : Mx k r → (L.Wq →L[ℂ] L.Wp)) : Mx k r → (L.Wq →L[ℂ] L.Wp) :=
  fun x => turnF L ka f (cjI k r ka⁻¹ 1 x)

theorem stdL_c (L : LocBessel k r) (ka : ℝ) (hka : 0 < ka) : (stdL L ka hka).c = cStd := by
  show ((ka⁻¹ : ℝ) : ℂ) * cOfDpsi (ka : ℂ) = cStd
  have hk0 : (ka : ℂ) ≠ 0 := by exact_mod_cast hka.ne'
  simp only [cOfDpsi, cStd, Complex.ofReal_inv]
  first
  | (rw [mul_comm, mul_assoc, mul_inv_cancel₀ hk0, mul_one])
  | field_simp
  | (field_simp; ring)

theorem jNorm2_std (L : LocBessel k r) (ka : ℝ) (hka : 0 < ka) (hc : L.c = ((2 * ka : ℝ) : ℂ)) (hk2 : 2 ≤ k)
    (f : Mx k r → (L.Wq →L[ℂ] L.Wp)) (μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ)
    (hsec : IsSection k r L.z L.z' μsec) :
    jNorm2 (stdL L ka hka) (stdF L ka f) (secTr 1 μsec) =
      ENNReal.ofReal (jacBig r ka⁻¹ 1 * wBig k r ka⁻¹ 1 * ‖(1 : ℂ)‖ ^ 2) * jNorm2 L f μsec := by
  have hκ : 0 < ka⁻¹ := inv_pos.2 hka
  have hτ : (0 : ℝ) < 1 := one_pos
  have e1 : Tz k r (stdL L ka hka).z = (1 : ℝ) ^ 2 * Tz k r (turnL L ka).z := Tz_smul _ _
  have e2 : Tz k r (stdL L ka hka).z' = (1 : ℝ) ^ 2 * Tz k r (turnL L ka).z' := Tz_smul _ _
  rw [← jNorm2_turn L ka hc f μsec]
  refine jNorm2_tr hκ hτ (turnL L ka) (stdL L ka hka) e1 e2 (turnF L ka f) (stdF L ka f) μsec (secTr 1 μsec) 1 hk2
    fun p hp hζ => ?_
  rw [secTr_sBig hτ]
  have hb : bigCell k r (sBig r ka⁻¹ 1 p).1 (μsec p.2) = cj k r ka⁻¹ 1 (bigCell k r p.1 (μsec p.2)) := by
    rw [bigCell_cj hκ hτ]; rfl
  rw [hb]
  show @hsNormSq L.Wp L.Wq _ _ _ _ _ ((stdL L ka hka).J (stdF L ka f) (cj k r ka⁻¹ 1 (bigCell k r p.1 (μsec p.2)))) = _
  rw [J_trD hκ hτ (turnL L ka)]
  have hfe : (fun x => stdF L ka f (cj k r ka⁻¹ 1 x)) = turnF L ka f := by
    funext x; show turnF L ka f (cjI k r ka⁻¹ 1 (cj k r ka⁻¹ 1 x)) = _; rw [cjI_cj hκ hτ]
  rw [hfe, norm_one, one_pow, one_mul]

theorem hsNormSq_eq_norm_hsVec {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (A : Wq →L[ℂ] Wp) :
    hsNormSq A = ‖Formalism.FourierDecayAlt.B.hsVec A‖ ^ 2 := by
  simp only [Formalism.MainNotions.S.hsNormSq, Formalism.MainNotions.S.hsInner, Formalism.FourierDecayAlt.B.hsVec, PiLp.norm_sq_eq_of_L2, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact inner_self_eq_norm_sq (𝕜 := ℂ) (A (stdOrthonormalBasis ℂ Wq i))

theorem JF_congr {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] (D : Formalism.FourierDecayAlt.B.RealPlaceData k r Wp Wq) {F F' : Mx k r → (Wq →L[ℂ] Wp)}
    (h : ∀ x ∈ UH (Hpk k r), F x = F' x) {g : Mx k r} (hg : g ∈ UH (Hpk k r)) :
    Formalism.FourierDecayAlt.B.JF D F g = Formalism.FourierDecayAlt.B.JF D F' g := by
  unfold Formalism.FourierDecayAlt.B.JF besselJ
  have : SigmaFinite D.μW := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite D.haarW
  have : SigmaFinite D.μN := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite D.haarN
  have : SigmaFinite D.μW' := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite D.haarW'
  have hW : ∀ᵐ x ∂D.μW, Matrix.of x ∈ UWset k r D.z := by
    rw [ae_iff]; exact D.haarW.conc
  have hN : ∀ᵐ x ∂D.μN, Matrix.of x ∈ Nset k r := by
    rw [ae_iff]; exact D.haarN.conc
  have hW' : ∀ᵐ x ∂D.μW', Matrix.of x ∈ UWset k r D.z' := by
    rw [ae_iff]; exact D.haarW'.conc
  have g1 : ∀ᵐ p ∂((D.μW.prod D.μN).prod (D.μW'.prod D.μN)), Matrix.of p.1.1 ∈ UWset k r D.z :=
    (Measure.quasiMeasurePreserving_fst.comp Measure.quasiMeasurePreserving_fst).ae hW
  have g2 : ∀ᵐ p ∂((D.μW.prod D.μN).prod (D.μW'.prod D.μN)), Matrix.of p.1.2 ∈ Nset k r :=
    (Measure.quasiMeasurePreserving_snd.comp Measure.quasiMeasurePreserving_fst).ae hN
  have g3 : ∀ᵐ p ∂((D.μW.prod D.μN).prod (D.μW'.prod D.μN)), Matrix.of p.2.1 ∈ UWset k r D.z' :=
    (Measure.quasiMeasurePreserving_fst.comp Measure.quasiMeasurePreserving_snd).ae hW'
  have g4 : ∀ᵐ p ∂((D.μW.prod D.μN).prod (D.μW'.prod D.μN)), Matrix.of p.2.2 ∈ Nset k r :=
    (Measure.quasiMeasurePreserving_snd.comp Measure.quasiMeasurePreserving_snd).ae hN
  refine integral_congr_ae ?_
  filter_upwards [g1, g2, g3, g4] with p h1 h2 h3 h4
  have hm : (Matrix.of p.1.1)⁻¹ * (Matrix.of p.1.2)⁻¹ * g * Matrix.of p.2.2 * Matrix.of p.2.1 ∈ UH (Hpk k r) :=
    WeylGroupFacts.uh_mul (WeylGroupFacts.uh_mul (WeylGroupFacts.uh_mul (WeylGroupFacts.uh_mul (WeylGroupFacts.uh_inv h1.1) (WeylGroupFacts.uh_inv h2.1)) hg) h4.1) h3.1
  simp only [h _ hm]

theorem normSq_tie {k0 r : ℕ} (hk2 : 2 ≤ k0 + 1) (L : LocBessel (k0 + 1) r) (hc : L.c = cStd)
    (μsec : ℂ → Matrix (Fin (k0 + 1 + 1)) (Fin (k0 + 1 + 1)) ℂ) (hsec : IsSection (k0 + 1) r L.z L.z' μsec)
    (D : Formalism.FourierDecayAlt.B.RealPlaceData (k0 + 1) r L.Wp L.Wq)
    (hD : D.z = L.z ∧ D.z' = L.z' ∧ D.π = L.π ∧ D.π' = L.π' ∧ D.μW = L.μW ∧ D.μN = L.μN ∧ D.μW' = L.μW' ∧ D.μsec = μsec)
    (F F' : Mx (k0 + 1) r → (L.Wq →L[ℂ] L.Wp)) (hFF : ∀ x ∈ UH (Hpk (k0 + 1) r), F x = F' x) :
    Formalism.FourierDecayAlt.B.normSq D F = jNorm2 L F' μsec := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hD
  unfold Formalism.FourierDecayAlt.B.normSq jNorm2 jNormSq
  rw [h1, h2]
  refine lintegral_congr fun q => ?_
  by_cases hw0 : bcWeight (k0 + 1) r (Tz (k0 + 1) r L.z) (Tz (k0 + 1) r L.z') q = 0
  · rw [hw0, zero_mul, zero_mul]
  obtain ⟨hcq, hζ⟩ := bcWeight_ne hk2 hw0
  have hμ := (hsec.2 q.2 hζ).1
  have hgU : bigCell (k0 + 1) r q.1 (μsec q.2) ∈ UH (Hpk (k0 + 1) r) := Formalism.QuantumDeterminants.bigCellMem _ _ _ _ hcq hμ
  congr 2
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt (hsNormSq_nonneg' _),
    hsNormSq_eq_norm_hsVec]
  have hg : Formalism.FourierDecayAlt.B.gq D q = bigCell (k0 + 1) r q.1 (μsec q.2) := by
    unfold Formalism.FourierDecayAlt.B.gq; rw [h8]
  show ‖Formalism.FourierDecayAlt.B.hsVec (Formalism.FourierDecayAlt.B.JF D F (Formalism.FourierDecayAlt.B.gq D q))‖ ^ 2 = _
  rw [hg, JF_congr D hFF hgU]
  congr 2
  unfold Formalism.FourierDecayAlt.B.JF
  rw [h1, h2, h3, h4, h5, h6, h7, ← hc]
  rfl

theorem inner_iso {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (T : H →L[ℂ] H) (hT : ∀ u, ‖T u‖ = ‖u‖)
    (a b : H) : ⟪T a, T b⟫_ℂ = ⟪a, b⟫_ℂ := by
  let T' : H →ₗᵢ[ℂ] H := { toLinearMap := (T : H →ₗ[ℂ] H), norm_map' := hT }
  exact T'.inner_map_map a b

theorem stdF_coef (L : LocBessel k r) (ka : ℝ) (hka : 0 < ka) (v v' : L.Hs) (ξ : L.Wp) (ξ' : L.Wq) :
    ∀ x ∈ UH (Hpk k r), stdF L ka (Formalism.MainNotions.S.Pv.AmpDD.coefF L v v' ξ ξ') x =
      Formalism.MainNotions.S.Pv.BetaCut.coefM (turnL L ka).σ ((turnL L ka).σ (dMi k r ka⁻¹ 1) v)
        ((turnL L ka).σ (dMi k r ka⁻¹ 1) v') ξ ξ' x := by
  intro x hx
  have hκ : 0 < ka⁻¹ := inv_pos.2 hka
  obtain ⟨h1, hmul, hiso⟩ := Formalism.MainNotions.LeviCoordinates.discrete_series_unitary_rep (turn_hσ L)
  have h1' : (turnL L ka).σ 1 = 1 := h1
  have hmul' : ∀ a ∈ UH (Hpk k r), ∀ b ∈ UH (Hpk k r),
      (turnL L ka).σ (a * b) = ((turnL L ka).σ a).comp ((turnL L ka).σ b) := hmul
  have hiso' : ∀ a ∈ UH (Hpk k r), ∀ u : L.Hs, ‖(turnL L ka).σ a u‖ = ‖u‖ := hiso
  have hdM := dM_mem_UH (k := k) (r := r) hκ one_pos
  have hdMi := dMi_mem_UH (k := k) (r := r) hκ one_pos
  have e1 : (turnL L ka).σ (dM k r ka⁻¹ 1 * x * dMi k r ka⁻¹ 1) =
      ((turnL L ka).σ (dM k r ka⁻¹ 1)).comp (((turnL L ka).σ x).comp ((turnL L ka).σ (dMi k r ka⁻¹ 1))) := by
    rw [hmul' _ (WeylGroupFacts.uh_mul hdM hx) _ hdMi, hmul' _ hdM _ hx, ContinuousLinearMap.comp_assoc]
  have e2 : ∀ a b : L.Hs, ⟪a, (turnL L ka).σ (dM k r ka⁻¹ 1) b⟫_ℂ = ⟪(turnL L ka).σ (dMi k r ka⁻¹ 1) a, b⟫_ℂ := by
    intro a b
    rw [← inner_iso ((turnL L ka).σ (dM k r ka⁻¹ 1)) (hiso' _ hdM) ((turnL L ka).σ (dMi k r ka⁻¹ 1) a) b]
    congr 1
    rw [← ContinuousLinearMap.comp_apply, ← hmul' _ hdM _ hdMi, dM_mul_dMi hκ one_pos, h1']
    rfl
  show (innerSL ℂ ξ').smulRight (⟪v, (turnL L ka).σ (dM k r ka⁻¹ 1 * x * dMi k r ka⁻¹ 1) v'⟫_ℂ • ξ) =
    (innerSL ℂ ξ').smulRight (⟪(turnL L ka).σ (dMi k r ka⁻¹ 1) v,
      (turnL L ka).σ x ((turnL L ka).σ (dMi k r ka⁻¹ 1) v')⟫_ℂ • ξ)
  rw [e1, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, e2]

theorem be_turn (L : LocBessel k r) (ka : ℝ) (hc : L.c = ((2 * ka : ℝ) : ℂ)) [SigmaFinite L.μN] (v w : L.Hs) :
    Formalism.FourierDecayAlt.ThreeDimData.be L.z (cOfDpsi (ka : ℂ)) (turnL L ka).π (turnL L ka).σ L.μW L.μN v w =
      Formalism.FourierDecayAlt.ThreeDimData.be L.z L.c L.π L.σ L.μW L.μN v w := by
  have : SigmaFinite L.μW := L.hμW.1.1
  have hc' : cOfDpsi (ka : ℂ) * Complex.I = L.c := by rw [hc]; exact turn_c ka
  have hinv : L.μW.prod L.μN = (L.μW.prod L.μN).map (Prod.map (cA k r) (cA k r)) := by
    rw [← Measure.map_prod_map _ _ continuous_cA.measurable continuous_cA.measurable, map_cA_UW L.hμW.1]
    congr 1
    exact (map_cA_haarLie L.κN).symm
  unfold Formalism.FourierDecayAlt.ThreeDimData.be
  conv_lhs => rw [hinv]
  rw [show (Prod.map (cA k r) (cA k r) : Mt k r × Mt k r → Mt k r × Mt k r) = ⇑((cAE k r).prodCongr (cAE k r)) from rfl,
    integral_map_equiv]
  refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
  obtain ⟨a, b⟩ := p
  show Formalism.FourierDecayAlt.ThreeDimData.beInt L.z (cOfDpsi (ka : ℂ)) (turnL L ka).π (turnL L ka).σ v w (cA k r a, cA k r b) =
    Formalism.FourierDecayAlt.ThreeDimData.beInt L.z L.c L.π L.σ v w (a, b)
  unfold Formalism.FourierDecayAlt.ThreeDimData.beInt
  simp only [of_cA]
  rw [psi_conjI L.hz.1 hc' (Matrix.of b)]
  have e1 : tT k r * (tTi k r * Matrix.of a * tT k r * (tTi k r * Matrix.of b * tT k r)) * tTi k r =
      Matrix.of a * Matrix.of b := by
    rw [← conjI_mul, conj_conjI]
  have e2 : tT k r * (tTi k r * Matrix.of a * tT k r)⁻¹ * tTi k r = (Matrix.of a)⁻¹ := by
    rw [← conjI_inv, conj_conjI]
  show (⟪w, L.σ (tT k r * (tTi k r * Matrix.of a * tT k r * (tTi k r * Matrix.of b * tT k r)) * tTi k r) v⟫_ℂ *
      star (psi k r L.z L.c (Matrix.of b))) • L.π (tT k r * (tTi k r * Matrix.of a * tT k r)⁻¹ * tTi k r) = _
  rw [e1, e2]

theorem be_dil (L : LocBessel k r) (ka : ℝ) (hka : 0 < ka) [SigmaFinite L.μN] (v w : L.Hs) :
    Formalism.FourierDecayAlt.ThreeDimData.be (stdL L ka hka).z cStd (stdL L ka hka).π (turnL L ka).σ (stdL L ka hka).μW (stdL L ka hka).μN
              ((turnL L ka).σ (dMi k r ka⁻¹ 1) v) ((turnL L ka).σ (dMi k r ka⁻¹ 1) w) =
      Formalism.FourierDecayAlt.ThreeDimData.be L.z (cOfDpsi (ka : ℂ)) (turnL L ka).π (turnL L ka).σ L.μW L.μN v w := by
  have hκ : 0 < ka⁻¹ := inv_pos.2 hka
  have : SigmaFinite L.μW := L.hμW.1.1
  obtain ⟨h1, hmul, hiso⟩ := Formalism.MainNotions.LeviCoordinates.discrete_series_unitary_rep (turn_hσ L)
  have h1' : (turnL L ka).σ 1 = 1 := h1
  have hmul' : ∀ a ∈ UH (Hpk k r), ∀ b ∈ UH (Hpk k r),
      (turnL L ka).σ (a * b) = ((turnL L ka).σ a).comp ((turnL L ka).σ b) := hmul
  have hiso' : ∀ a ∈ UH (Hpk k r), ∀ u : L.Hs, ‖(turnL L ka).σ a u‖ = ‖u‖ := hiso
  have hdM := dM_mem_UH (k := k) (r := r) hκ one_pos
  have hdMi := dMi_mem_UH (k := k) (r := r) hκ one_pos
  have hN : (stdL L ka hka).μN = L.μN.map (cjT k r ka⁻¹ 1) := (map_haarLie_N hκ one_pos L.κN).symm
  have hprod : (stdL L ka hka).μW.prod (stdL L ka hka).μN =
      (L.μW.prod L.μN).map (Prod.map (cjT k r ka⁻¹ 1) (cjT k r ka⁻¹ 1)) := by
    rw [hN, ← Measure.map_prod_map _ _ measurable_cjT measurable_cjT]
    rfl
  have hcs : cStd = ((ka⁻¹ : ℝ) : ℂ) * cOfDpsi (ka : ℂ) := (stdL_c L ka hka).symm
  unfold Formalism.FourierDecayAlt.ThreeDimData.be
  rw [hprod, show (Prod.map (cjT k r ka⁻¹ 1) (cjT k r ka⁻¹ 1) : Mt k r × Mt k r → Mt k r × Mt k r) =
    ⇑((cjE (k := k) (r := r) hκ one_pos).prodCongr (cjE hκ one_pos)) from rfl, integral_map_equiv]
  have hW : ∀ᵐ x ∂L.μW, Matrix.of x ∈ UWset k r L.z := by
    rw [ae_iff]; simpa using L.hμW.1.2.2.1
  have hNa : ∀ᵐ x ∂L.μN, Matrix.of x ∈ Nset k r := Formalism.MainNotions.S.Pv.AmpDDPf.ae_mem_haarLieN L.κN
  have g1 : ∀ᵐ p ∂(L.μW.prod L.μN), Matrix.of p.1 ∈ UWset k r L.z :=
    Measure.quasiMeasurePreserving_fst.ae hW
  have g2 : ∀ᵐ p ∂(L.μW.prod L.μN), Matrix.of p.2 ∈ Nset k r :=
    Measure.quasiMeasurePreserving_snd.ae hNa
  refine integral_congr_ae ?_
  filter_upwards [g1, g2] with p hp1 hp2
  obtain ⟨a, b⟩ := p
  have ha : Matrix.of a ∈ UH (Hpk k r) := hp1.1
  have hb : Matrix.of b ∈ UH (Hpk k r) := hp2.1
  show Formalism.FourierDecayAlt.ThreeDimData.beInt (stdL L ka hka).z cStd (stdL L ka hka).π (turnL L ka).σ
      ((turnL L ka).σ (dMi k r ka⁻¹ 1) v) ((turnL L ka).σ (dMi k r ka⁻¹ 1) w) (cjT k r ka⁻¹ 1 a, cjT k r ka⁻¹ 1 b) =
    Formalism.FourierDecayAlt.ThreeDimData.beInt L.z (cOfDpsi (ka : ℂ)) (turnL L ka).π (turnL L ka).σ v w (a, b)
  unfold Formalism.FourierDecayAlt.ThreeDimData.beInt
  simp only [of_cjT]

  have hps : Formalism.QuantumDeterminants.psi k r (stdL L ka hka).z cStd (cj k r ka⁻¹ 1 (Matrix.of b)) =
      Formalism.QuantumDeterminants.psi k r L.z (cOfDpsi (ka : ℂ)) (Matrix.of b) := by
    rw [hcs]; exact psi_cj hκ one_pos L.hz.1 _ _

  have hpi : (stdL L ka hka).π (cj k r ka⁻¹ 1 (Matrix.of a))⁻¹ = (turnL L ka).π (Matrix.of a)⁻¹ := by
    show (turnL L ka).π (cjI k r ka⁻¹ 1 (cj k r ka⁻¹ 1 (Matrix.of a))⁻¹) = _
    rw [← cj_inv hκ one_pos, cjI_cj hκ one_pos]

  have hca := (cj_mem_UH_iff hκ one_pos _).2 ha
  have hcb := (cj_mem_UH_iff hκ one_pos _).2 hb
  have hin : ⟪(turnL L ka).σ (dMi k r ka⁻¹ 1) w,
      (turnL L ka).σ (cj k r ka⁻¹ 1 (Matrix.of a) * cj k r ka⁻¹ 1 (Matrix.of b)) ((turnL L ka).σ (dMi k r ka⁻¹ 1) v)⟫_ℂ =
      ⟪w, (turnL L ka).σ (Matrix.of a * Matrix.of b) v⟫_ℂ := by
    rw [← inner_iso ((turnL L ka).σ (dM k r ka⁻¹ 1)) (hiso' _ hdM)]
    rw [← ContinuousLinearMap.comp_apply ((turnL L ka).σ (dM k r ka⁻¹ 1)) ((turnL L ka).σ (dMi k r ka⁻¹ 1)),
      ← hmul' _ hdM _ hdMi, dM_mul_dMi hκ one_pos, h1', ContinuousLinearMap.one_apply]
    congr 1
    have hcab := WeylGroupFacts.uh_mul hca hcb
    have hmat : dM k r ka⁻¹ 1 * (cj k r ka⁻¹ 1 (Matrix.of a) * cj k r ka⁻¹ 1 (Matrix.of b)) * dMi k r ka⁻¹ 1 =
        Matrix.of a * Matrix.of b := by
      rw [← cj_mul hκ one_pos]
      unfold cj
      have e : ∀ X : Mx k r, dM k r ka⁻¹ 1 * (dMi k r ka⁻¹ 1 * X * dM k r ka⁻¹ 1) * dMi k r ka⁻¹ 1 =
          (dM k r ka⁻¹ 1 * dMi k r ka⁻¹ 1) * X * (dM k r ka⁻¹ 1 * dMi k r ka⁻¹ 1) := by
        intro X; simp only [Matrix.mul_assoc]
      rw [e, dM_mul_dMi hκ one_pos, Matrix.one_mul, Matrix.mul_one]
    rw [← ContinuousLinearMap.comp_apply ((turnL L ka).σ (cj k r ka⁻¹ 1 (Matrix.of a) * cj k r ka⁻¹ 1 (Matrix.of b)))
      ((turnL L ka).σ (dMi k r ka⁻¹ 1)), ← hmul' _ hcab _ hdMi,
      ← ContinuousLinearMap.comp_apply ((turnL L ka).σ (dM k r ka⁻¹ 1)), ← hmul' _ hdM _ (WeylGroupFacts.uh_mul hcab hdMi),
      ← Matrix.mul_assoc, hmat]
  rw [hps, hpi, hin]
  rfl

theorem be_turn' (L : LocBessel k r) (ka : ℝ) (hc : L.c = ((2 * ka : ℝ) : ℂ)) [SigmaFinite L.μN] (v w : L.Hs) :
    Formalism.FourierDecayAlt.ThreeDimData.be L.z' (cOfDpsi (ka : ℂ)) (turnL L ka).π' (turnL L ka).σ L.μW' L.μN v w =
      Formalism.FourierDecayAlt.ThreeDimData.be L.z' L.c L.π' L.σ L.μW' L.μN v w := by
  have : SigmaFinite L.μW' := L.hμW'.1.1
  have hc' : cOfDpsi (ka : ℂ) * Complex.I = L.c := by rw [hc]; exact turn_c ka
  have hinv : L.μW'.prod L.μN = (L.μW'.prod L.μN).map (Prod.map (cA k r) (cA k r)) := by
    rw [← Measure.map_prod_map _ _ continuous_cA.measurable continuous_cA.measurable, map_cA_UW L.hμW'.1]
    congr 1
    exact (map_cA_haarLie L.κN).symm
  unfold Formalism.FourierDecayAlt.ThreeDimData.be
  conv_lhs => rw [hinv]
  rw [show (Prod.map (cA k r) (cA k r) : Mt k r × Mt k r → Mt k r × Mt k r) = ⇑((cAE k r).prodCongr (cAE k r)) from rfl,
    integral_map_equiv]
  refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
  obtain ⟨a, b⟩ := p
  show Formalism.FourierDecayAlt.ThreeDimData.beInt L.z' (cOfDpsi (ka : ℂ)) (turnL L ka).π' (turnL L ka).σ v w (cA k r a, cA k r b) =
    Formalism.FourierDecayAlt.ThreeDimData.beInt L.z' L.c L.π' L.σ v w (a, b)
  unfold Formalism.FourierDecayAlt.ThreeDimData.beInt
  simp only [of_cA]
  rw [psi_conjI L.hz'.1 hc' (Matrix.of b)]
  have e1 : tT k r * (tTi k r * Matrix.of a * tT k r * (tTi k r * Matrix.of b * tT k r)) * tTi k r =
      Matrix.of a * Matrix.of b := by
    rw [← conjI_mul, conj_conjI]
  have e2 : tT k r * (tTi k r * Matrix.of a * tT k r)⁻¹ * tTi k r = (Matrix.of a)⁻¹ := by
    rw [← conjI_inv, conj_conjI]
  show (⟪w, L.σ (tT k r * (tTi k r * Matrix.of a * tT k r * (tTi k r * Matrix.of b * tT k r)) * tTi k r) v⟫_ℂ *
      star (psi k r L.z' L.c (Matrix.of b))) • L.π' (tT k r * (tTi k r * Matrix.of a * tT k r)⁻¹ * tTi k r) = _
  rw [e1, e2]

theorem be_dil' (L : LocBessel k r) (ka : ℝ) (hka : 0 < ka) [SigmaFinite L.μN] (v w : L.Hs) :
    Formalism.FourierDecayAlt.ThreeDimData.be (stdL L ka hka).z' cStd (stdL L ka hka).π' (turnL L ka).σ (stdL L ka hka).μW' (stdL L ka hka).μN
              ((turnL L ka).σ (dMi k r ka⁻¹ 1) v) ((turnL L ka).σ (dMi k r ka⁻¹ 1) w) =
      Formalism.FourierDecayAlt.ThreeDimData.be L.z' (cOfDpsi (ka : ℂ)) (turnL L ka).π' (turnL L ka).σ L.μW' L.μN v w := by
  have hκ : 0 < ka⁻¹ := inv_pos.2 hka
  have : SigmaFinite L.μW' := L.hμW'.1.1
  obtain ⟨h1, hmul, hiso⟩ := Formalism.MainNotions.LeviCoordinates.discrete_series_unitary_rep (turn_hσ L)
  have h1' : (turnL L ka).σ 1 = 1 := h1
  have hmul' : ∀ a ∈ UH (Hpk k r), ∀ b ∈ UH (Hpk k r),
      (turnL L ka).σ (a * b) = ((turnL L ka).σ a).comp ((turnL L ka).σ b) := hmul
  have hiso' : ∀ a ∈ UH (Hpk k r), ∀ u : L.Hs, ‖(turnL L ka).σ a u‖ = ‖u‖ := hiso
  have hdM := dM_mem_UH (k := k) (r := r) hκ one_pos
  have hdMi := dMi_mem_UH (k := k) (r := r) hκ one_pos
  have hN : (stdL L ka hka).μN = L.μN.map (cjT k r ka⁻¹ 1) := (map_haarLie_N hκ one_pos L.κN).symm
  have hprod : (stdL L ka hka).μW'.prod (stdL L ka hka).μN =
      (L.μW'.prod L.μN).map (Prod.map (cjT k r ka⁻¹ 1) (cjT k r ka⁻¹ 1)) := by
    rw [hN, ← Measure.map_prod_map _ _ measurable_cjT measurable_cjT]
    rfl
  have hcs : cStd = ((ka⁻¹ : ℝ) : ℂ) * cOfDpsi (ka : ℂ) := (stdL_c L ka hka).symm
  unfold Formalism.FourierDecayAlt.ThreeDimData.be
  rw [hprod, show (Prod.map (cjT k r ka⁻¹ 1) (cjT k r ka⁻¹ 1) : Mt k r × Mt k r → Mt k r × Mt k r) =
    ⇑((cjE (k := k) (r := r) hκ one_pos).prodCongr (cjE hκ one_pos)) from rfl, integral_map_equiv]
  have hW : ∀ᵐ x ∂L.μW', Matrix.of x ∈ UWset k r L.z' := by
    rw [ae_iff]; simpa using L.hμW'.1.2.2.1
  have hNa : ∀ᵐ x ∂L.μN, Matrix.of x ∈ Nset k r := Formalism.MainNotions.S.Pv.AmpDDPf.ae_mem_haarLieN L.κN
  have g1 : ∀ᵐ p ∂(L.μW'.prod L.μN), Matrix.of p.1 ∈ UWset k r L.z' :=
    Measure.quasiMeasurePreserving_fst.ae hW
  have g2 : ∀ᵐ p ∂(L.μW'.prod L.μN), Matrix.of p.2 ∈ Nset k r :=
    Measure.quasiMeasurePreserving_snd.ae hNa
  refine integral_congr_ae ?_
  filter_upwards [g1, g2] with p hp1 hp2
  obtain ⟨a, b⟩ := p
  have ha : Matrix.of a ∈ UH (Hpk k r) := hp1.1
  have hb : Matrix.of b ∈ UH (Hpk k r) := hp2.1
  show Formalism.FourierDecayAlt.ThreeDimData.beInt (stdL L ka hka).z' cStd (stdL L ka hka).π' (turnL L ka).σ
      ((turnL L ka).σ (dMi k r ka⁻¹ 1) v) ((turnL L ka).σ (dMi k r ka⁻¹ 1) w) (cjT k r ka⁻¹ 1 a, cjT k r ka⁻¹ 1 b) =
    Formalism.FourierDecayAlt.ThreeDimData.beInt L.z' (cOfDpsi (ka : ℂ)) (turnL L ka).π' (turnL L ka).σ v w (a, b)
  unfold Formalism.FourierDecayAlt.ThreeDimData.beInt
  simp only [of_cjT]

  have hps : Formalism.QuantumDeterminants.psi k r (stdL L ka hka).z' cStd (cj k r ka⁻¹ 1 (Matrix.of b)) =
      Formalism.QuantumDeterminants.psi k r L.z' (cOfDpsi (ka : ℂ)) (Matrix.of b) := by
    rw [hcs]; exact psi_cj hκ one_pos L.hz'.1 _ _

  have hpi : (stdL L ka hka).π' (cj k r ka⁻¹ 1 (Matrix.of a))⁻¹ = (turnL L ka).π' (Matrix.of a)⁻¹ := by
    show (turnL L ka).π' (cjI k r ka⁻¹ 1 (cj k r ka⁻¹ 1 (Matrix.of a))⁻¹) = _
    rw [← cj_inv hκ one_pos, cjI_cj hκ one_pos]

  have hca := (cj_mem_UH_iff hκ one_pos _).2 ha
  have hcb := (cj_mem_UH_iff hκ one_pos _).2 hb
  have hin : ⟪(turnL L ka).σ (dMi k r ka⁻¹ 1) w,
      (turnL L ka).σ (cj k r ka⁻¹ 1 (Matrix.of a) * cj k r ka⁻¹ 1 (Matrix.of b)) ((turnL L ka).σ (dMi k r ka⁻¹ 1) v)⟫_ℂ =
      ⟪w, (turnL L ka).σ (Matrix.of a * Matrix.of b) v⟫_ℂ := by
    rw [← inner_iso ((turnL L ka).σ (dM k r ka⁻¹ 1)) (hiso' _ hdM)]
    rw [← ContinuousLinearMap.comp_apply ((turnL L ka).σ (dM k r ka⁻¹ 1)) ((turnL L ka).σ (dMi k r ka⁻¹ 1)),
      ← hmul' _ hdM _ hdMi, dM_mul_dMi hκ one_pos, h1', ContinuousLinearMap.one_apply]
    congr 1
    have hcab := WeylGroupFacts.uh_mul hca hcb
    have hmat : dM k r ka⁻¹ 1 * (cj k r ka⁻¹ 1 (Matrix.of a) * cj k r ka⁻¹ 1 (Matrix.of b)) * dMi k r ka⁻¹ 1 =
        Matrix.of a * Matrix.of b := by
      rw [← cj_mul hκ one_pos]
      unfold cj
      have e : ∀ X : Mx k r, dM k r ka⁻¹ 1 * (dMi k r ka⁻¹ 1 * X * dM k r ka⁻¹ 1) * dMi k r ka⁻¹ 1 =
          (dM k r ka⁻¹ 1 * dMi k r ka⁻¹ 1) * X * (dM k r ka⁻¹ 1 * dMi k r ka⁻¹ 1) := by
        intro X; simp only [Matrix.mul_assoc]
      rw [e, dM_mul_dMi hκ one_pos, Matrix.one_mul, Matrix.mul_one]
    rw [← ContinuousLinearMap.comp_apply ((turnL L ka).σ (cj k r ka⁻¹ 1 (Matrix.of a) * cj k r ka⁻¹ 1 (Matrix.of b)))
      ((turnL L ka).σ (dMi k r ka⁻¹ 1)), ← hmul' _ hcab _ hdMi,
      ← ContinuousLinearMap.comp_apply ((turnL L ka).σ (dM k r ka⁻¹ 1)), ← hmul' _ hdM _ (WeylGroupFacts.uh_mul hcab hdMi),
      ← Matrix.mul_assoc, hmat]
  rw [hps, hpi, hin]
  rfl

theorem bcWeight_nonneg' (k r : ℕ) (T T' : ℝ) (p : (Fin r → ℂ) × ℂ) : 0 ≤ bcWeight k r T T' p := by
  unfold Formalism.QuantumDeterminants.bcWeight
  split_ifs with h
  · exact mul_nonneg (Finset.prod_nonneg fun a _ => by positivity) (pow_nonneg (sub_nonneg.2 h) _)
  · exact le_refl 0

theorem normSq_ne_of_beta {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (D : Formalism.FourierDecayAlt.B.RealPlaceData k r Wp Wq) (F : Mx k r → (Wq →L[ℂ] Wp))
    (h : Formalism.FourierDecayAlt.B.beta D F F ≠ 0) : Formalism.FourierDecayAlt.B.normSq D F ≠ 0 := by
  intro h0
  apply h
  unfold Formalism.FourierDecayAlt.B.normSq Formalism.QuantumDeterminants.jNormSq at h0
  unfold Formalism.FourierDecayAlt.B.beta Formalism.QuantumDeterminants.betaBig
  have key : ∀ f : (Fin r → ℂ) × ℂ → ℝ, (∀ p, 0 ≤ f p) → ∫⁻ p, ENNReal.ofReal (f p) = 0 →
      ∫ p, (f p : ℂ) = 0 := by
    intro f hf0 hl
    first
    | rw [integral_complex_ofReal]
    | rw [← integral_complex_ofReal]
    | rw [integral_ofReal (𝕜 := ℂ)]
    by_cases hm : AEStronglyMeasurable f (volume : Measure ((Fin r → ℂ) × ℂ))
    · rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hf0) hm, hl, ENNReal.toReal_zero,
        Complex.ofReal_zero]
    · rw [integral_non_aestronglyMeasurable hm, Complex.ofReal_zero]
  have hz := key _ ?nn h0
  case nn =>
    intro p
    exact mul_nonneg (bcWeight_nonneg' k r _ _ p) (sq_nonneg _)
  rw [← hz]
  congr 1
  funext p
  beta_reduce
  rw [inner_self_eq_norm_sq_to_K, Complex.ofReal_mul, Complex.ofReal_pow]
  rfl

theorem jNorm2_coef_ne {k0 r : ℕ} (hk2 : 2 ≤ k0 + 1) (L : LocBessel (k0 + 1) r)
    (ka : ℝ) (hka : 0 < ka) (hc : L.c = ((2 * ka : ℝ) : ℂ)) (hκ0 : L.κN ≠ 0) (hκT : L.κN ≠ ⊤)
    (μsec : ℂ → Matrix (Fin (k0 + 1 + 1)) (Fin (k0 + 1 + 1)) ℂ) (hsec : IsSection (k0 + 1) r L.z L.z' μsec)
    (h : ℝ) (hgap : GapAtLeast L.ε L.lam h) (hok : Formalism.FourierDecayAlt.ThreeDimData.GapOK (k0 + 1) r h)
    (v v' : L.Hs) (hv : v ∈ PI.UpqRep.smoothVecs (k := k0 + 1) (r := r) (turnL L ka).σ)
    (hv' : v' ∈ PI.UpqRep.smoothVecs (k := k0 + 1) (r := r) (turnL L ka).σ)
    (l : L.Wp) (l' : L.Wq) (ξ : L.Wp) (ξ' : L.Wq)
    (hbe : Formalism.FourierDecayAlt.ThreeDimData.be L.z L.c L.π L.σ L.μW L.μN v v = (innerSL ℂ l).smulRight l)
    (hbe' : Formalism.FourierDecayAlt.ThreeDimData.be L.z' L.c L.π' L.σ L.μW' L.μN v' v' = (innerSL ℂ l').smulRight l')
    (hl : ⟪l, ξ⟫_ℂ ≠ 0) (hl' : ⟪ξ', l'⟫_ℂ ≠ 0)
    (hCI : Formalism.MainNotions.S.Pv.BetaCut.CoefInCC) (hBI : Formalism.MainNotions.S.Pv.BetaCut.BetaInfCoefNZ) :
    jNorm2 L (Formalism.MainNotions.S.Pv.AmpDD.coefF L v v' ξ ξ') μsec ≠ 0 := by
  intro h0
  have hκ : 0 < ka⁻¹ := inv_pos.2 hka
  have hstd := jNorm2_std L ka hka hc hk2 (Formalism.MainNotions.S.Pv.AmpDD.coefF L v v' ξ ξ') μsec hsec
  rw [h0, mul_zero] at hstd
  have hsec₁ : IsSection (k0 + 1) r (stdL L ka hka).z (stdL L ka hka).z' (secTr 1 μsec) := isSection_tr one_pos hsec
  have hκ0₁ : (stdL L ka hka).κN ≠ 0 :=
    mul_ne_zero hκ0 (ENNReal.ofReal_pos.2 (deltaN_pos hκ one_pos)).ne'
  have hκT₁ : (stdL L ka hka).κN ≠ ⊤ := ENNReal.mul_ne_top hκT ENNReal.ofReal_ne_top
  obtain ⟨D, hDz, hDz', hDπ, hDπ', hDμW, hDμN, hDμW', hDsec⟩ :=
    Formalism.MainNotions.BigCellDensity.settingTie k0 r (stdL L ka hka) (secTr 1 μsec) (stdL_c L ka hka) hsec₁ hκ0₁ hκT₁
  have hσt := turn_hσ L
  obtain ⟨-, hmulT, -⟩ := Formalism.MainNotions.LeviCoordinates.discrete_series_unitary_rep hσt
  have hdMi := dMi_mem_UH (k := k0 + 1) (r := r) hκ one_pos
  have hvt : (turnL L ka).σ (dMi (k0 + 1) r ka⁻¹ 1) v ∈ PI.UpqRep.smoothVecs (k := k0 + 1) (r := r) (turnL L ka).σ :=
    Formalism.MainNotions.LeviCoordinates.smooth_vectors_translate (turnL L ka).σ hmulT hdMi hv
  have hvt' : (turnL L ka).σ (dMi (k0 + 1) r ka⁻¹ 1) v' ∈ PI.UpqRep.smoothVecs (k := k0 + 1) (r := r) (turnL L ka).σ :=
    Formalism.MainNotions.LeviCoordinates.smooth_vectors_translate (turnL L ka).σ hmulT hdMi hv'
  set Fc := Formalism.MainNotions.S.Pv.BetaCut.coefM (turnL L ka).σ ((turnL L ka).σ (dMi (k0 + 1) r ka⁻¹ 1) v)
    ((turnL L ka).σ (dMi (k0 + 1) r ka⁻¹ 1) v') ξ ξ' with hFc
  have hN : Formalism.FourierDecayAlt.B.normSq D Fc = 0 := by
    rw [normSq_tie hk2 (stdL L ka hka) (stdL_c L ka hka) (secTr 1 μsec) hsec₁ D
      ⟨hDz, hDz', hDπ, hDπ', hDμW, hDμN, hDμW', hDsec⟩ Fc (stdF L ka (Formalism.MainNotions.S.Pv.AmpDD.coefF L v v' ξ ξ'))
      (fun x hx => (stdF_coef L ka hka v v' ξ ξ' x hx).symm)]
    exact hstd

  obtain ⟨m, hmA, hmh⟩ := Formalism.L2.S.Pv.PeriodG.exponent_ok (k0 + 1) r hok L.ε
  have hAm : Formalism.FourierDecayAlt.B.AB (k0 + 1) r ≤ m := by
    have hle : Formalism.FourierDecayAlt.B.AB (k0 + 1) r ≤ Formalism.FourierDecayAlt.ThreeDimData.AG (k0 + 1) r := by
      unfold Formalism.FourierDecayAlt.B.AB Formalism.FourierDecayAlt.ThreeDimData.AG
      have h1 : (1 : ℝ) ≤ ((k0 + 1 : ℕ) : ℝ) + r := by push_cast; linarith [(Nat.cast_nonneg k0 : (0:ℝ) ≤ k0), (Nat.cast_nonneg r : (0:ℝ) ≤ r)]
      have h2 : (1 : ℝ) ≤ (r : ℝ) + 1 := by linarith [(Nat.cast_nonneg r : (0:ℝ) ≤ r)]
      nlinarith
    linarith
  obtain ⟨c, hc0, -, -, hβ, -, -⟩ := Formalism.FourierDecayAlt.P.b_any_of_xi (k0 + 1) r _ _ D (Formalism.FourierDecayAlt.B.AB (k0 + 1) r) le_rfl
  have hF5 : Formalism.FourierDecayAlt.B.InCC (Formalism.FourierDecayAlt.B.AB (k0 + 1) r) 5 Fc :=
    hCI (k0 + 1) r L.ε L.lam L.Hs (turnL L ka).σ h m _ L.hlam hσt hgap hmh hAm _ hvt _ hvt' L.Wp L.Wq ξ ξ'
  have : SigmaFinite L.μN := (Formalism.MainNotions.BridgeCSB.haarLieN _ _ _ hκ0 hκT).1
  have hbD : Formalism.FourierDecayAlt.ThreeDimData.be D.z cStd D.π (turnL L ka).σ D.μW D.μN ((turnL L ka).σ (dMi (k0 + 1) r ka⁻¹ 1) v)
      ((turnL L ka).σ (dMi (k0 + 1) r ka⁻¹ 1) v) = (innerSL ℂ ((fun _ => l) ((turnL L ka).σ (dMi (k0 + 1) r ka⁻¹ 1) v))).smulRight
        ((fun _ => l) ((turnL L ka).σ (dMi (k0 + 1) r ka⁻¹ 1) v)) := by
    rw [hDz, hDπ, hDμW, hDμN, be_dil L ka hka v v, be_turn L ka hc v v]
    exact hbe
  have hbD' : Formalism.FourierDecayAlt.ThreeDimData.be D.z' cStd D.π' (turnL L ka).σ D.μW' D.μN ((turnL L ka).σ (dMi (k0 + 1) r ka⁻¹ 1) v')
      ((turnL L ka).σ (dMi (k0 + 1) r ka⁻¹ 1) v') = (innerSL ℂ ((fun _ => l') ((turnL L ka).σ (dMi (k0 + 1) r ka⁻¹ 1) v'))).smulRight
        ((fun _ => l') ((turnL L ka).σ (dMi (k0 + 1) r ka⁻¹ 1) v')) := by
    rw [hDz', hDπ', hDμW', hDμN, be_dil' L ka hka v' v', be_turn' L ka hc v' v']
    exact hbe'
  have hbI := hBI (k0 + 1) r _ _ D L.ε L.lam L.Hs (turnL L ka).σ h L.hlam hσt hgap hok _ _ (fun _ => l) (fun _ => l')
    ξ ξ' hvt hvt' hbD hbD' hl hl'
  have hbeta : Formalism.FourierDecayAlt.B.beta D Fc Fc ≠ 0 := by
    rw [hβ Fc Fc hF5 hF5]
    exact mul_ne_zero (by exact_mod_cast hc0.ne') hbI
  exact normSq_ne_of_beta D Fc hbeta hN

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace in
theorem smooth_turn (L : LocBessel k r) (ka : ℝ) {v : L.Hs} (hv : v ∈ PI.UpqRep.smoothVecs (k := k) (r := r) L.σ) :
    v ∈ PI.UpqRep.smoothVecs (k := k) (r := r) (turnL L ka).σ := by
  have hTi : tTi k r * tT k r = 1 := by
    have h1 := tT_mul_tTi k r
    unfold tT tTi at h1 ⊢
    rw [Matrix.diagonal_mul_diagonal] at h1 ⊢
    first
    | (simpa only [mul_comm] using h1)
    | (convert h1 using 3 <;> ring)
  have hTH : (tT k r)ᴴ = tTi k r := by
    unfold tT tTi
    rw [Matrix.diagonal_conjTranspose]
    rfl
  have hTiH : (tTi k r)ᴴ = tT k r := by rw [← hTH, Matrix.conjTranspose_conjTranspose]
  have hHT : (tT k r)ᴴ * Hpk k r * tT k r = Hpk k r := by
    rw [← Hpk_tTi, Matrix.mul_assoc, hTi, Matrix.mul_one]
  have hconj : ∀ g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ, gᴴ * Hpk k r * g = Hpk k r →
      (tT k r * g * tTi k r)ᴴ * Hpk k r * (tT k r * g * tTi k r) = Hpk k r := by
    intro g hg
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hTiH]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (tT k r)ᴴ, ← Matrix.mul_assoc ((tT k r)ᴴ * Hpk k r), hHT]
    rw [← Matrix.mul_assoc gᴴ, ← Matrix.mul_assoc (gᴴ * Hpk k r), hg]
    rw [Hpk_tTi, ← Matrix.mul_assoc, hTH, tT_mul_tTi, Matrix.one_mul]
  let Φ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ →ₗ[ℝ] Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ :=
    { toFun := fun g => tT k r * g * tTi k r
      map_add' := by intro a b; simp [Matrix.mul_add, Matrix.add_mul]
      map_smul' := by intro c a; simp [Matrix.mul_smul, Matrix.smul_mul] }
  have hcont : Continuous fun g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ => tT k r * g * tTi k r :=
    (LinearMap.toContinuousLinearMap Φ).continuous
  simp only [PI.UpqRep.smoothVecs, Set.mem_setOf_eq, PI.UpqRep.IsSmoothVec] at hv ⊢
  intro g₀ hg₀
  obtain ⟨U, F, hU, hgU, hF, hEq⟩ := hv (tT k r * g₀ * tTi k r) (hconj g₀ hg₀)
  refine ⟨(fun g => tT k r * g * tTi k r) ⁻¹' U, fun g => F (tT k r * g * tTi k r), hU.preimage hcont, hgU, ?_, ?_⟩
  · exact hF.comp (LinearMap.toContinuousLinearMap Φ).contDiff.contDiffOn (fun g hg => hg)
  · intro g hg hgH
    exact hEq _ hg (hconj g hgH)

theorem jNorm2_coef_ne' {k r : ℕ} (hk2 : 2 ≤ k) (L : LocBessel k r)
    (ka : ℝ) (hka : 0 < ka) (hc : L.c = ((2 * ka : ℝ) : ℂ)) (hκ0 : L.κN ≠ 0) (hκT : L.κN ≠ ⊤)
    (μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (hsec : IsSection k r L.z L.z' μsec)
    (h : ℝ) (hgap : GapAtLeast L.ε L.lam h) (hok : Formalism.FourierDecayAlt.ThreeDimData.GapOK k r h)
    (v v' : L.Hs) (hv : v ∈ PI.UpqRep.smoothVecs (k := k) (r := r) L.σ)
    (hv' : v' ∈ PI.UpqRep.smoothVecs (k := k) (r := r) L.σ)
    (l : L.Wp) (l' : L.Wq) (ξ : L.Wp) (ξ' : L.Wq)
    (hbe : Formalism.FourierDecayAlt.ThreeDimData.be L.z L.c L.π L.σ L.μW L.μN v v = (innerSL ℂ l).smulRight l)
    (hbe' : Formalism.FourierDecayAlt.ThreeDimData.be L.z' L.c L.π' L.σ L.μW' L.μN v' v' = (innerSL ℂ l').smulRight l')
    (hl : ⟪l, ξ⟫_ℂ ≠ 0) (hl' : ⟪ξ', l'⟫_ℂ ≠ 0)
    (hCI : Formalism.MainNotions.S.Pv.BetaCut.CoefInCC) (hBI : Formalism.MainNotions.S.Pv.BetaCut.BetaInfCoefNZ) :
    jNorm2 L (Formalism.MainNotions.S.Pv.AmpDD.coefF L v v' ξ ξ') μsec ≠ 0 := by
  obtain ⟨k0, rfl⟩ : ∃ k0, k = k0 + 1 := ⟨k - 1, by omega⟩
  exact jNorm2_coef_ne hk2 L ka hka hc hκ0 hκT μsec hsec h hgap hok v v' (smooth_turn L ka hv) (smooth_turn L ka hv')
    l l' ξ ξ' hbe hbe' hl hl' hCI hBI

end Formalism.L2.S.Pv.AmpNZTie
