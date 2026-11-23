import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.InfClassAt
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.DictAt
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumOKEx
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasCompactSupportFlatIntegrand
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneCosetOfIsTensor
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationLeOneOfMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteCoefficientBound
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlatIntegrandFlippedTensorLocallyConstantCompact
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralUnfoldingVariablesMemFieldRange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemVarLat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralEqVolumeSumCharacterTwistedCosetsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VariablesUniformizerPowerLatticeBasisOpenVolumeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StepVariablesCountGridLocalFlipGridLeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffValuationLossFinsetSumAndInvPowStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffPlaceValuationResidueFieldCardEqZeroOfNotMeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MovedStaircaseTensorPeriodicUniformizerPowStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AddCharNegUnfoldingPhaseMulUniformizerPowLatticeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MovedTensorChosenPlaceCoeffValuationLossLeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MovedTensorFactorCoeffValuationLossLeAwayPrimeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffValuationLossLeAddCharNegUnfoldingPhaseStatement

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RowTest GlobalTheory.SumSize GlobalTheory.RowClaim
open Formalism.DivisionValues (vw lw)
open MeasureTheory ValuativeRel GlobalTheory.UnfoldLoss

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField GlobalTheory.FunObj.borelKw
  GlobalTheory.FunObj.borelSpaceKw

noncomputable section

namespace GlobalTheory.UnfoldLoss

theorem varsVol_isAddLeftInvariant {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [MeasurableSpace k] [BorelSpace k] (G : Grid k) (ν : Measure k) [ν.IsAddHaarMeasure] : (varsVol G ν).IsAddLeftInvariant := by
  obtain ⟨_, _⟩ := Model.secondCountable_and_t2_local_field (k := k)
  unfold varsVol
  infer_instance

theorem lossLe_mul' {D : D7} {w : PlL D} {z z' : ℂ} {a a' : ℝ} (h : LossLe w z a) (h' : LossLe w z' a') :
    LossLe w (z * z') (a + a') := by
  obtain ⟨y, rfl, hy⟩ := h
  obtain ⟨y', rfl, hy'⟩ := h'
  refine ⟨y * y', map_mul _ _ _, ?_⟩
  by_cases h0 : y = 0
  · exact Or.inl (by simp [h0])
  by_cases h0' : y' = 0
  · exact Or.inl (by simp [h0'])
  rcases hy with h1 | h1
  · exact absurd h1 h0
  rcases hy' with h2 | h2
  · exact absurd h2 h0'
  refine Or.inr ?_
  rw [Formalism.DivisionValues.ValuationRepresentative.vw_mul w _ _ h0 h0', Int.cast_add]
  linarith

section Main

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks]
  [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}

theorem datum_loss {large₂ : SizeData₂ D} {F : Face D A} {CF b : ℝ} (hS : HidaSetting large₂ R F) (ch : Choice R) (hIs : ch.Is)
    (hSc : ch.AtScale CF b) (hF : ch.FieldOK) (t : T) (Φ : ch.G.Datum) (β : CosFam ch.G t) (hβ : β ∈ ch.S.supp t Φ)
    (P : locPl ch.G t) (w : PlL D)
    (hcase : (P : Pl D.host.E) ∈ ch.G.pl.W0 ∨ ((Formalism.EigenvalueLevelCeiling.plc (P : Pl D.host.E) : ℕ) : 𝓞 D.what₂.LL) ∉ w.asIdeal)
    (c : ℝ) (hc : 0 ≤ c) (hT : ∀ z, LossLe w (Tflip ch.W ch.S.B t Φ P z) c) (X Y) :
    LossLe w ((ch.S.term t Φ β P).datum X Y) (c + 2 * (D.R.m : ℝ) ^ 2 * (bigN D : ℝ) ^ 2 * (cosExp ch.G P : ℝ) *
      (vw w ((resCard (Kw (P : Pl D.host.E)) : ℕ) : D.what₂.LL) : ℝ)) := by
  classical
  have hL : R.toLevCh.Is A.μ0 := hS.core.lev
  have hde := GlobalTheory.FlipIntegrand.pde_ne_q_of_setting hS
  have hc' : ∀ Q ∈ R.toLevCh.Q t, ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ Q.asIdeal := hIs.guard t
  have hm : 0 < D.R.m := by have := D.R.two_le_m; omega
  have hTT := isTensor_Tflip hL ch.W ch.S.B t Φ hde hc' P.2
  have hcond : HasConductor (psiAt ch.W P.1) 1 :=
    (((Good.locGrid_isGood hL ch.G ch.W t hde hc').1 P.1 P.2).square 0 hm 0 hm).cond
  haveI := (isUnitVol_unitVol P.1).1
  obtain ⟨_, _⟩ := Model.secondCountable_and_t2_local_field (k := Kw P.1)
  haveI : (varsVol (locGrid ch.G t P) (unitVol P.1)).IsAddLeftInvariant := varsVol_isAddLeftInvariant _ _
  set S := moved (locGrid ch.G t P) (keepAt ch.G P) ((repsAt ch.G t P).elt (β P)) (Tflip ch.W ch.S.B t Φ P) with hSdef
  set f := flatIntegrand one_le_sLen (psiAt ch.W P.1) S X Y with hf
  have hdat : (ch.S.term t Φ β P).datum X Y = ∫ e, f e ∂(varsVol (locGrid ch.G t P) (unitVol P.1)) := rfl
  have hcpt : HasCompactSupport f := hasCompactSupport_flatIntegrand one_le_sLen _ hTT _ _ X Y
  set q : ℕ := resCard (Kw (P : Pl D.host.E)) with hq
  set vq : ℝ := (vw w ((q : ℕ) : D.what₂.LL) : ℝ) with hvq
  have hvq0 : 0 ≤ vq := by
    rw [hvq]; exact_mod_cast ResidueCardinalityNilpotence.GlobalTheory.CompanionTheory.VolVal.vw_nat_nonneg w q
  have hq0 : 0 < q := Nat.pos_of_ne_zero (ResidueCardinalityNilpotence.GlobalTheory.CompanionTheory.VolVal.resCard_ne P.1)
  by_cases h0 : (ch.S.term t Φ β P).datum X Y = 0
  · rw [h0]; exact ⟨0, map_zero _, Or.inl rfl⟩
  have hval : ∀ K1 : ℝ, (∀ z, LossLe w (S z) (c + K1)) → ∀ v, LossLe w (f v) (c + K1) := by
    intro K1 hK v
    by_cases hv : S (fill one_le_sLen X Y v) = 0
    · have : f v = 0 := by simp [hf, flatIntegrand, hv]
      rw [this]; exact ⟨0, map_zero _, Or.inl rfl⟩
    · have hψ := GlobalTheory.T.coeffValuationLossLe_addChar_neg_unfoldingPhase ch large₂ F CF b hS hIs hSc hF t Φ β hβ P X Y v h0 hv w
      have := lossLe_mul' (hK (fill one_le_sLen X Y v)) hψ
      rw [add_zero] at this
      exact this
  have hint : ∀ (n : ℕ) (K1 : ℝ), (∀ v, ∀ u ∈ varLat (locGrid ch.G t P) (unifAt P.1) n,
      ∀ u' ∈ varLat (locGrid ch.G t P) (unifAt P.1) n, f (v + u + u') * f v = f (v + u) * f (v + u')) →
      (∀ v, LossLe w (f v) (c + K1)) →
      LossLe w ((ch.S.term t Φ β P).datum X Y) (c + K1 + ((n * varCount (locGrid ch.G t P) : ℕ) : ℝ) * vq) := by
    intro n K1 hrel hv
    obtain ⟨-, hlat⟩ := GlobalTheory.T.variablesUniformizerPowerLattice_basis_open_volume (locGrid ch.G t P) (unitVol P.1) (isUnitVol_unitVol P.1) (unifAt P.1) (isUnif_unifAt P.1)
    obtain ⟨hop, hfin, hvol⟩ := hlat n
    obtain ⟨s, hs⟩ := GlobalTheory.T.integral_eq_volume_sum_characterTwistedCosets (varsVol (locGrid ch.G t P) (unitVol P.1)) _ hop hfin f hcpt hrel
    rw [hdat, hs, hvol]
    obtain ⟨h1, h2⟩ := GlobalTheory.T.coeffValuationLoss_finsetSum_and_invPow w
    exact lossLe_mul' (h1 s f _ fun i _ => hv i) (h2 q _ hq0)
  by_cases hW : (P : Pl D.host.E) ∈ ch.G.pl.W0
  · set e := cosExp ch.G P with he
    have hdep : depthAt ch.G P = e := by
      obtain ⟨v, hv, hvP⟩ := Finset.mem_image.1 hW
      have := depthAt_w ch.G hv
      rw [he, ← hvP, this.1, this.2]
    rw [hdep] at hTT
    have hkeep : keepAt ch.G P = false := by simp [keepAt, hW]
    have hO := oneCoset one_le_sLen (psiAt ch.W P.1) (unitVol P.1) (givenLevel ch.G t P) (Tflip ch.W ch.S.B t Φ P) (unifAt P.1) e
      D.R.m_even (isUnif_unifAt P.1) hcond hTT (fun j hj _ => ResidueCardinalityNilpotence.GlobalTheory.CompanionTheory.VolVal.givenLevel_KO ch.G t P hj)
    have hb : β P ∈ unfSupport (psiAt ch.W P.1) (unitVol P.1) false
        (Reps.through one_le_sLen (givenLevel ch.G t P) (stair (locGrid ch.G t P) (unifAt P.1) e)) (Tflip ch.W ch.S.B t Φ P) := by
      have := hβ P
      rw [hkeep] at this
      exact this
    have hβ' := funext (hO _ hb)
    have hSeq : S = moved (locGrid ch.G t P) (keepAt ch.G P)
        ((Reps.through one_le_sLen (givenLevel ch.G t P) (stair (locGrid ch.G t P) (unifAt P.1) e)).elt
          fun i => DoubleCoset.mk _ _ (stair (locGrid ch.G t P) (unifAt P.1) e (i + 1))) (Tflip ch.W ch.S.B t Φ P) := by
      rw [hSdef, ← hβ']; rfl
    have hrel : ∀ v, ∀ u ∈ varLat (locGrid ch.G t P) (unifAt P.1) (D.R.m * e),
        ∀ u' ∈ varLat (locGrid ch.G t P) (unifAt P.1) (D.R.m * e), f (v + u + u') * f v = f (v + u) * f (v + u') := by
      intro v u hu u' hu'
      have hper := GlobalTheory.T.movedStaircaseTensor_periodic_uniformizerPow (locGrid ch.G t P) one_le_sLen (unifAt P.1) (isUnif_unifAt P.1) e _ hTT (givenLevel ch.G t P)
        (keepAt ch.G P) X Y
      have hψ2 := GlobalTheory.T.addChar_neg_unfoldingPhase_mul_uniformizerPowLattice (locGrid ch.G t P) (psiAt ch.W P.1) hcond (unifAt P.1) (isUnif_unifAt P.1) _ X v u u' hu hu'
      have e1 := hper (v + u) u' hu'
      have e2 := hper v u hu
      have e3 := hper v u' hu'
      rw [← hSeq] at e1 e2 e3
      simp only [hf, flatIntegrand]
      rw [e1, e2, e3]
      linear_combination (S (fill one_le_sLen X Y v)) ^ 2 * hψ2
    have hmov := GlobalTheory.T.movedTensorChosenPlace_coeffValuationLoss_le ch large₂ F CF b hS hIs hSc hF t Φ β hβ P hW w c hc hT
    have h1 := hint (D.R.m * e) _ hrel (hval _ hmov)
    refine h1.mono ?_
    have hcount := GlobalTheory.T.stepVariablesCount_gridLocalFlipGrid_le ch.G t P
    have hle : ((D.R.m * e * varCount (locGrid ch.G t P) : ℕ) : ℝ) ≤ (D.R.m : ℝ) ^ 2 * (bigN D : ℝ) ^ 2 * (e : ℝ) := by
      have h2 : D.R.m * e * varCount (locGrid ch.G t P) ≤ D.R.m * e * (D.R.m * bigN D ^ 2) := Nat.mul_le_mul_left _ hcount
      calc ((D.R.m * e * varCount (locGrid ch.G t P) : ℕ) : ℝ) ≤ ((D.R.m * e * (D.R.m * bigN D ^ 2) : ℕ) : ℝ) := by
            exact_mod_cast h2
        _ = _ := by push_cast; ring
    have h3 := mul_le_mul_of_nonneg_right hle hvq0
    nlinarith
  · have hw : ((Formalism.EigenvalueLevelCeiling.plc (P : Pl D.host.E) : ℕ) : 𝓞 D.what₂.LL) ∉ w.asIdeal := hcase.resolve_left hW
    have hv0 : vq = 0 := by rw [hvq]; exact_mod_cast GlobalTheory.T.coeffPlace_valuation_residueFieldCard_eq_zero_of_not_mem P.1 w hw
    have he0 : cosExp ch.G P = 0 := (depthAt_of_notMem ch.G hW).1
    have hlc : IsLocallyConstant f := by
      have hmv : Continuous ((locGrid ch.G t P).moveArgs .one ((repsAt ch.G t P).elt (β P))) := continuous_pi fun b =>
        (continuous_const.matrix_mul (continuous_apply b)).matrix_mul continuous_const
      have hψ : IsLocallyConstant fun e => ((psiAt ch.W P.1 (-phase X e) : Circle) : ℂ) :=
        ((hcond.isLocallyConstant.comp Subtype.val).comp_continuous (continuous_phase X).neg)
      exact ((IsLocallyConstant.const _).mul ((IsLocallyConstant.const _).mul
        ((isLocallyConstant_of_isTensor hTT).comp_continuous (hmv.comp (continuous_fill one_le_sLen X Y))))).mul hψ
    obtain ⟨hbasis, -⟩ := GlobalTheory.T.variablesUniformizerPowerLattice_basis_open_volume (locGrid ch.G t P) (unitVol P.1) (isUnitVol_unitVol P.1) (unifAt P.1) (isUnif_unifAt P.1)
    obtain ⟨n, hn⟩ := hbasis _ ((GlobalTheory.LCIntegralField.isOpen_stab hlc hcpt).mem_nhds (zero_mem _))
    have hrel : ∀ v, ∀ u ∈ varLat (locGrid ch.G t P) (unifAt P.1) n,
        ∀ u' ∈ varLat (locGrid ch.G t P) (unifAt P.1) n, f (v + u + u') * f v = f (v + u) * f (v + u') := by
      intro v u hu u' hu'
      have e1 : ∀ y, f (y + u) = f y := hn hu
      have e2 : ∀ y, f (y + u') = f y := hn hu'
      rw [e2, e1, e2]
    have hmov := GlobalTheory.T.movedTensorFactor_coeffValuationLossLe_awayPrime ch large₂ F CF b hS hIs hSc hF t Φ β hβ P hW w hw c hc hT
    have h1 := hint n 0 hrel (hval 0 fun z => by simpa using hmov z)
    simpa [he0, hv0] using h1

end Main

theorem unfold_loss : ∃ CF0 : ℝ, ∀ CF : ℝ, CF0 ≤ CF → ∃ c₂ : ℝ, ∀ ε : ℝ, ∃ x₀ : ℝ, ∀ (D : D7) (large₂ : SizeData₂ D), large₂.sc.eps = ε → x₀ ≤ large₂.sc.x →
    ∀ (Γ : Type) [Group Γ] [Fintype Γ] (Pl0 T : Type) (A : FamIn D.what₂.LL Γ Pl0 T D.R.m)
      (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), HidaSetting large₂ R F →
      ∀ ch : Choice R, ch.Is → ch.AtScale CF large₂.sc.b → ch.FieldOK →
      ∀ (t : T) (Φ : ch.G.Datum), ∀ β ∈ ch.S.supp t Φ, ∀ (P : locPl ch.G t) (w : PlL D),
        ((P : Pl D.host.E) ∈ ch.G.pl.W0 ∨ ((Formalism.EigenvalueLevelCeiling.plc (P : Pl D.host.E) : ℕ) : 𝓞 D.what₂.LL) ∉ w.asIdeal) →
        ∀ c : ℝ, 0 ≤ c → (∀ z, LossLe w (Tflip ch.W ch.S.B t Φ P z) c) →
        ∀ X Y, LossLe w ((ch.S.term t Φ β P).datum X Y) (c + c₂ * (D.R.m : ℝ) ^ 2 * (bigN D : ℝ) ^ 2 * (cosExp ch.G P : ℝ) *
          (vw w ((resCard (Kw (P : Pl D.host.E)) : ℕ) : D.what₂.LL) : ℝ)) :=
  ⟨0, fun _ _ => ⟨2, fun _ => ⟨0, fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hS ch hIs hSc hF t Φ β hβ P w hcase c hc hT X Y =>
    datum_loss hS ch hIs hSc hF t Φ β hβ P w hcase c hc hT X Y⟩⟩⟩

end GlobalTheory.UnfoldLoss

end
