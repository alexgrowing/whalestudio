import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.UniqGapOfUniq
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.OnePlaceKF
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Formalism.SharpRestriction.CuspSpanNormBounds.LeadMinorK
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.KfinCoefMulSplit
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegrableCellOrbitalIntegralRankOneKFiniteStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BlockProjectionBessel
import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.HaarEqSmul
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.DiscreteSeriesUnitarySmoothBasic
open BranchingSupport GlobalTheory.CellAmp Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

noncomputable section

namespace GlobalTheory.CellPieriG

open GlobalTheory.CellPieri

variable {k r : ℕ}

theorem amp_eq_orb (hH : GlobalTheory.GapIn.Hyp) (hA : GlobalTheory.GapIn.AmpKF0) (hC : CellConv) (L : LocBessel k r) (R : Rep k r)
    (mu : Fin (2 * r + k + 1) → ℝ) (h : ℝ) (μG : Measure (Mt k r)) (l : R.H → L.Wp) (l' : R.H → L.Wq) (w : R.H)
    [CompleteSpace L.Wp] [CompleteSpace L.Wq]
    (hR : R.IsDS L.ε mu) (hgap : GapAtLeast L.ε mu h) (hok : Formalism.FourierDecayAlt.ThreeDimData.GapOK k r h) (hcell : GapCell k r h)
    (hc : L.c ≠ 0) (hκ : L.κN ≠ ⊤) (hG : IsHaarOn (UH (Hpk k r)) μG)
    (hl : ∀ x ∈ R.sm, ∀ v ∈ R.TK,
      Formalism.FourierDecayAlt.ThreeDimData.be L.z L.c L.π R.σ L.μW L.μN x v = (innerSL ℂ (l v)).smulRight (l x))
    (hl' : ∀ x ∈ R.sm, ∀ v ∈ R.TK,
      Formalism.FourierDecayAlt.ThreeDimData.be L.z' L.c L.π' R.σ L.μW' L.μN x v = (innerSL ℂ (l' v)).smulRight (l' x))
    (hw : PI.UpqRep.IsLowUnitH k r L.ε mu R.σ w)
    (γ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (μR νR : Measure (Mt k r))
    (ν : Measure (PairSp k r)) (hD : CellData L μG γ μR νR ν) (v v' : R.H) (hv : R.KFin v) (hv' : R.KFin v')
    (ξ : L.Wp) (ξ' : L.Wq) :
    Integrable (besselIntg L (coefR R v v' ξ ξ') γ) ν ∧
      ((PI.BesselPeriodGGP.fdegH μG R.σ w : ℂ) * (⟪l v, ξ⟫_ℂ * ⟪ξ', l' v'⟫_ℂ)) • amp R l l' w νR γ =
        OrbInt L (coefR R v v' ξ ξ') γ ν := by
  have hKF : PI.KFinSmooth := hH.1.1.2.2.1
  obtain ⟨-, -, -, -, hsm, -, hKT, -, -⟩ := GlobalTheory.rep_basic_of_isDS hKF k r L.ε mu R hR
  have hwK : R.KFin w := PI.UnitaryGroupMassFormula.LowSmooth.isKFinHpk_of_lowUnit hw
  have hle : ∀ x ∈ Formalism.FourierDecayAlt.ThreeDimData.DDsp R.σ w, x ∈ R.TK := by
    intro x hx
    refine Submodule.span_mono ?_ hx
    rintro _ ⟨g, hg, rfl⟩
    exact ⟨g, hg, w, hwK, rfl⟩
  have hD' : CellData (withRep L R mu hR) μG γ μR νR ν := hD
  obtain ⟨b, hb0, hb1, hb2⟩ := hC k r L h μG γ μR νR ν hκ hok hcell hD hD.2.2.1
  have hAG : 0 ≤ Formalism.FourierDecayAlt.ThreeDimData.AG k r := by
    unfold Formalism.FourierDecayAlt.ThreeDimData.AG; positivity
  have hOne : OnePlaceKF (withRep L R mu hR) h μG w l l' :=
    ⟨⟨hgap, hok, hc, hw, hG, fun x hx y hy => hl x (hsm x (hle x hx)) y (hle y hy),
      fun x hx y hy => hl' x (hsm x (hle x hx)) y (hle y hy)⟩,
      fun x hx y hy => hl x (hsm x (hle x hx)) y (hKT y hy),
      fun x hx y hy => hl' x (hsm x (hle x hx)) y (hKT y hy)⟩
  have h1 := hA k r (withRep L R mu hR) h μG w l l' hOne γ μR νR ν hD' b hb0 hb1 hb2 v v' hv hv' ξ ξ'
  have h2 := (GlobalTheory.T.integrable_cellOrbitalIntegral_rankOne_kFinite hH k r (withRep L R mu hR) h μG γ μR νR ν hgap hok hκ hD').2 b hb0 (by linarith)
    hb2 v v' hv hv' ξ ξ'
  refine ⟨h2, ?_⟩
  obtain ⟨c, hc0, hc1⟩ := Gp91.GlobalTheory.BesselDegree.schur_fdeg hH.1 k r L.ε μG hG
  have hw0 : w ≠ 0 := by
    obtain ⟨P, -, hn, -⟩ := hw
    intro h0
    rw [h0, norm_zero] at hn
    exact zero_ne_one hn
  have hDG : R.IsDG L.ε mu := ⟨hR.1, hR.2, h, hgap, hok⟩
  have hf : (PI.BesselPeriodGGP.fdegH μG R.σ w : ℂ) ≠ 0 := by
    rw [(hc1 mu R hDG).1 w hw0]
    exact Complex.ofReal_ne_zero.mpr (mul_pos hc0 (fdegHC_pos hR.1.1)).ne'
  have h3 : (⟪l v, ξ⟫_ℂ * ⟪ξ', l' v'⟫_ℂ) • amp R l l' w νR γ =
      ((PI.BesselPeriodGGP.fdegH μG R.σ w : ℂ)⁻¹) • OrbInt L (coefR R v v' ξ ξ') γ ν := h1
  rw [mul_smul, h3, smul_smul, mul_inv_cancel₀ hf, one_smul]

theorem amp_pieri : GlobalTheory.GapIn.Hyp → GlobalTheory.GapIn.AmpKF0 → CellConv → ∀ (k r : ℕ) (ι κ : Type) [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] (ρ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → Matrix ι ι ℂ) (Γ : Matrix ι ι ℂ) (d : ℕ) (L : LocBessel k r) (R : Rep k r) (RI : κ → Rep k r) (io : ∀ I, ι → (RI I).H → R.H) (pr : ∀ I, ι → R.H → (RI I).H) (ep : κ → ℝ) (mu : Fin (2 * r + k + 1) → ℝ) (muI : κ → Fin (2 * r + k + 1) → ℝ) (h : ℝ) (μG : Measure (Mt k r)) (om om' : ι → ℂ) (l : R.H → L.Wp) (l' : R.H → L.Wq) (lI : ∀ I, (RI I).H → L.Wp) (lI' : ∀ I, (RI I).H → L.Wq) (w : R.H) (wI : ∀ I, (RI I).H) (κ₀ κ₁ : κ → ℂ), haveI := FiniteDimensional.complete ℂ L.Wp; haveI := FiniteDimensional.complete ℂ L.Wq; R.IsDS L.ε mu → GapAtLeast L.ε mu h → (∀ I, (RI I).IsDS L.ε (muI I) ∧ GapAtLeast L.ε (muI I) h) → Formalism.FourierDecayAlt.ThreeDimData.GapOK k r h → GapCell k r h → L.c ≠ 0 → L.κN ≠ ⊤ → IsHaarOn (UH (Hpk k r)) μG → IsFRep ρ Γ d → TensH ρ Γ R RI io pr ep → (∀ g ∈ Sset k r L.z, ρ g *ᵥ om = om) → (∀ g ∈ Sset k r L.z', ρ g *ᵥ om' = om') → (∀ x ∈ R.sm, ∀ v ∈ R.TK, Formalism.FourierDecayAlt.ThreeDimData.be L.z L.c L.π R.σ L.μW L.μN x v = (innerSL ℂ (l v)).smulRight (l x)) → (∀ x ∈ R.sm, ∀ v ∈ R.TK, Formalism.FourierDecayAlt.ThreeDimData.be L.z' L.c L.π' R.σ L.μW' L.μN x v = (innerSL ℂ (l' v)).smulRight (l' x)) → (∀ I, (∀ x ∈ (RI I).sm, ∀ v ∈ (RI I).TK, Formalism.FourierDecayAlt.ThreeDimData.be L.z L.c L.π (RI I).σ L.μW L.μN x v = (innerSL ℂ (lI I v)).smulRight (lI I x)) ∧ (∀ x ∈ (RI I).sm, ∀ v ∈ (RI I).TK, Formalism.FourierDecayAlt.ThreeDimData.be L.z' L.c L.π' (RI I).σ L.μW' L.μN x v = (innerSL ℂ (lI' I v)).smulRight (lI' I x))) → (∃ v, R.KFin v ∧ l v ≠ 0) → (∃ v, R.KFin v ∧ l' v ≠ 0) → PI.UpqRep.IsLowUnitH k r L.ε mu R.σ w → (∀ I, PI.UpqRep.IsLowUnitH k r L.ε (muI I) (RI I).σ (wI I)) → (∀ I, ∀ v ∈ R.sm, lI I (∑ c, pr I c (tm R om v c)) = κ₀ I • l v ∧ lI' I (∑ c, pr I c (tm R om' v c)) = κ₁ I • l' v) → ∀ (γ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (μR νR : Measure (Mt k r)) (ν : Measure (PairSp k r)), CellData L μG γ μR νR ν → (herm Γ (ρ γ *ᵥ om') om * (PI.BesselPeriodGGP.fdegH μG R.σ w : ℂ)) • amp R l l' w νR γ = ∑ I, ((ep I : ℂ) * κ₁ I * star (κ₀ I) * (PI.BesselPeriodGGP.fdegH μG (RI I).σ (wI I) : ℂ)) • amp (RI I) (lI I) (lI' I) (wI I) νR γ := by
  intro hH hA hC k r ι κ _ _ _ _ ρ Γ d L R RI io pr ep mu muI h μG om om' l l' lI lI' w wI κ₀ κ₁
  haveI := FiniteDimensional.complete ℂ L.Wp
  haveI := FiniteDimensional.complete ℂ L.Wq
  intro hR hgap hRI hok hcell hc hκ hG hρ hT hom hom' hl hl' hlI ⟨v, hv, hv0⟩ ⟨v', hv', hv0'⟩ hw hwI hκI γ μR νR ν hD
  have hKF : PI.KFinSmooth := hH.1.1.2.2.1
  have hvs : v ∈ R.sm := hKF k r L.ε mu R.H R.σ hR.1 hR.2 v hv
  have hvs' : v' ∈ R.sm := hKF k r L.ε mu R.H R.σ hR.1 hR.2 v' hv'
  obtain ⟨hK, hsplit⟩ := GlobalTheory.KFinCoefSplit.kfin_coef_mul_split hKF k r ι κ ρ Γ d R RI io pr ep L.ε mu muI om om' v v' hR
    (fun I => (hRI I).1) hρ hT hv hv'
  obtain ⟨-, e0⟩ := amp_eq_orb hH hA hC L R mu h μG l l' w hR hgap hok hcell hc hκ hG hl hl' hw γ μR νR ν hD
    v v' hv hv' (l v) (l' v')
  have eI := fun I => amp_eq_orb hH hA hC L (RI I) (muI I) h μG (lI I) (lI' I) (wI I) (hRI I).1 (hRI I).2 hok hcell
    hc hκ hG (hlI I).1 (hlI I).2 (hwI I) γ μR νR ν hD _ _ (hK I).1 (hK I).2 (l v) (l' v')
  have hae := (GlobalTheory.T.integrable_cellOrbitalIntegral_rankOne_kFinite hH k r (withRep L R mu hR) h μG γ μR νR ν hgap hok hκ hD).1
  have hc0 : ⟪l v, l v⟫_ℂ * ⟪l' v', l' v'⟫_ℂ ≠ 0 :=
    mul_ne_zero (inner_self_ne_zero.mpr hv0) (inner_self_ne_zero.mpr hv0')
  have horb : herm Γ (ρ γ *ᵥ om') om • OrbInt L (coefR R v v' (l v) (l' v')) γ ν =
      ∑ I, (ep I : ℂ) • OrbInt L (coefR (RI I) (∑ c, pr I c (tm R om v c)) (∑ c, pr I c (tm R om' v' c))
        (l v) (l' v')) γ ν := by
    unfold OrbInt
    simp only [← integral_smul]
    refine Eq.trans (integral_congr_ae ?_) (integral_finset_sum _ (fun I _ => (eI I).1.smul (ep I : ℂ)))
    filter_upwards [hae] with p hp
    obtain ⟨hm, he⟩ := herm_cell hρ hom hom' hD.1 hp.1 hp.2.1 hp.2.2.1 hp.2.2.2
    have hs := hsplit _ hm
    rw [he] at hs
    ext x
    simp only [besselIntg, coefR, ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.sum_apply, ContinuousLinearMap.smulRight_apply, map_smul, smul_smul, Pi.smul_apply,
      ← Finset.sum_smul]
    congr 1
    have key : ∀ (D A B C : ℂ) (e f : κ → ℂ), D * C = ∑ I, e I * f I →
        D * A * (B * C) = ∑ I, e I * A * (B * f I) := by
      intro D A B C e f hh
      rw [show D * A * (B * C) = D * C * (A * B) by ring, hh, Finset.sum_mul]
      exact Finset.sum_congr rfl fun I _ => by ring
    exact key _ _ _ _ _ _ hs
  apply smul_right_injective _ hc0
  simp only [Finset.smul_sum, smul_smul]
  rw [mul_comm, mul_assoc, mul_smul, e0, horb]
  refine Finset.sum_congr rfl fun I _ => ?_
  rw [← (eI I).2, smul_smul, (hκI I v hvs).1, (hκI I v' hvs').2, inner_smul_left, inner_smul_right]
  congr 1
  simp only [RCLike.star_def]
  ring

end GlobalTheory.CellPieriG

end
