import Formalism.SharpRestriction.CuspSpanNormBounds.FrobeniusCoefficientMemLp.SigmaFiniteAmplitudes.NormPiLeOne

noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal NNReal

namespace Formalism.MainNotions.S.Pv.AmpDDPf

open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S

variable {k r : ℕ}

attribute [local instance] Formalism.FourierDecayAlt.P.B7.properFD

section Gen

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] {μ : Measure α} {ν : Measure β}
  {E F : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem enorm_rankOne (w : E) (u : F) : ‖(innerSL ℂ w).smulRight u‖ₑ = ‖w‖ₑ * ‖u‖ₑ := by
  rw [← ofReal_norm, ← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_mul (norm_nonneg _),
    ContinuousLinearMap.norm_smulRight_apply, innerSL_apply_norm]

theorem rankOne_smul (w : E) (u : F) (c d : ℂ) :
    (innerSL ℂ (d • w)).smulRight (c • u) = (c * star d) • (innerSL ℂ w).smulRight u := by
  ext η
  simp only [ContinuousLinearMap.smulRight_apply, innerSL_apply_apply,
    _root_.smul_apply, inner_smul_left, smul_smul, starRingEnd_apply]
  congr 1
  ring

theorem integral_inner_left {f : α → E} (hf : Integrable f μ) (η : E) :
    ∫ x, ⟪f x, η⟫_ℂ ∂μ = ⟪∫ x, f x ∂μ, η⟫_ℂ := by
  have h1 : (fun x => ⟪f x, η⟫_ℂ) = fun x => (starRingEnd ℂ) ⟪η, f x⟫_ℂ := by
    funext x; rw [inner_conj_symm]
  rw [h1, integral_conj, integral_inner hf, inner_conj_symm]

theorem integral_rankOne_prod [SFinite μ] [SFinite ν] {a : α → F} {b : β → E} (ha : Integrable a μ)
    (hb : Integrable b ν) (hI : Integrable (fun q : α × β => (innerSL ℂ (b q.2)).smulRight (a q.1)) (μ.prod ν)) :
    ∫ q, (innerSL ℂ (b q.2)).smulRight (a q.1) ∂(μ.prod ν) = (innerSL ℂ (∫ y, b y ∂ν)).smulRight (∫ x, a x ∂μ) := by
  ext η
  rw [ContinuousLinearMap.integral_apply hI η]
  simp only [ContinuousLinearMap.smulRight_apply, innerSL_apply_apply]
  have hI' : Integrable (fun q : α × β => ⟪b q.2, η⟫_ℂ • a q.1) (μ.prod ν) := by
    simpa only [ContinuousLinearMap.smulRight_apply, innerSL_apply_apply] using hI.apply_continuousLinearMap η
  rw [integral_prod (fun q : α × β => ⟪b q.2, η⟫_ℂ • a q.1) hI']
  simp only
  simp_rw [integral_smul_const]
  rw [integral_inner_left hb, integral_smul]

end Gen

section Pt

variable {H Wp : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [NormedAddCommGroup Wp]
  [InnerProductSpace ℂ Wp]

theorem aM_eq (z : Fin (2 * r + k + 1) → ℂ) (c : ℂ)
    (π : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (Wp →L[ℂ] Wp))
    (σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)) (w0 v : H) (ξ : Wp)
    {t : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (ht : t ∈ UH (Hpk k r)) {p1 : Mt k r × Mt k r}
    (hp1 : Matrix.of p1.1 ∈ UWset k r z) (hp2 : Matrix.of p1.2 ∈ Nset k r) :
    aM z c π σ w0 v ξ (t : Mt k r) p1 = aVec z c π σ w0 v ξ t p1 := by
  have g : (Matrix.of p1.1)⁻¹ * (Matrix.of p1.2)⁻¹ * t ∈ UH (Hpk k r) :=
    Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul (Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul (Formalism.QuantumDeterminants.WeylGroupFacts.uh_inv hp1.1)
      (Formalism.QuantumDeterminants.WeylGroupFacts.uh_inv hp2.1)) ht
  have e1 : cM σ v w0 (Formalism.FourierDecayAlt.P.B7.mulM (Formalism.FourierDecayAlt.P.B7.mulM (Formalism.FourierDecayAlt.P.B7.invM p1.1)
      (Formalism.FourierDecayAlt.P.B7.invM p1.2)) (t : Mt k r)) = ⟪v, σ ((Matrix.of p1.1)⁻¹ * (Matrix.of p1.2)⁻¹ * t) w0⟫_ℂ :=
    Set.indicator_of_mem (s := {g : Mt k r | Matrix.of g ∈ UH (Hpk k r)}) g _
  have e2 : piV z π ξ p1.1 = π (Matrix.of p1.1) ξ :=
    Set.indicator_of_mem (s := {h : Mt k r | Matrix.of h ∈ UWset k r z}) hp1 _
  simp only [aM, aVec]
  rw [e1, e2]

theorem aesm_aVec [FiniteDimensional ℂ Wp] {ε : Fin (2 * r + k + 1) → Bool} {lam : Fin (2 * r + k + 1) → ℝ}
    {σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)}
    (hσ : PI.UpqRep.IsDSHpk k r ε lam σ) {z : Fin (2 * r + k + 1) → ℂ} {u : Fin k → ℝ}
    {π : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (Wp →L[ℂ] Wp)}
    (hT : 0 < Tz k r z) (hπ : PI.UpqRep.IsHCTypeW k r z u π) (c : ℂ) (w0 v : H) (ξ : Wp)
    {t : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (ht : t ∈ UH (Hpk k r))
    {μW μN : Measure (Mt k r)} [SFinite μW] [SFinite μN]
    (h1 : ∀ᵐ x ∂μW, Matrix.of x ∈ UWset k r z) (h2 : ∀ᵐ x ∂μN, Matrix.of x ∈ Nset k r) :
    AEStronglyMeasurable (aVec z c π σ w0 v ξ t) (μW.prod μN) := by
  have hs := sm_aM hσ hT hπ c w0 v ξ (t := fun _ : Mt k r × Mt k r => (t : Mt k r)) (p1 := id)
    measurable_const measurable_id
  refine hs.aestronglyMeasurable.congr ?_
  have h1' : ∀ᵐ p ∂(μW.prod μN), Matrix.of p.1 ∈ UWset k r z := Measure.quasiMeasurePreserving_fst.ae h1
  have h2' : ∀ᵐ p ∂(μW.prod μN), Matrix.of p.2 ∈ Nset k r := Measure.quasiMeasurePreserving_snd.ae h2
  filter_upwards [h1', h2'] with p hp1 hp2
  exact aM_eq z c π σ w0 v ξ ht hp1 hp2

end Pt

theorem rankOne_zero_right {E F : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] (w : E) : (innerSL ℂ w).smulRight (0 : F) = 0 := by
  ext η; simp

theorem rankOne_zero_left {E F : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] (u : F) : (innerSL ℂ (0 : E)).smulRight u = 0 := by
  ext η; simp

theorem pair_split (L : LocBessel k r) [SFinite L.μW] [SFinite L.μW'] [SFinite L.μN]
    (hιW : MeasurePreserving (Formalism.FourierDecayAlt.P.B7.invM (k := k) (r := r)) L.μW L.μW)
    (hιW' : MeasurePreserving (Formalism.FourierDecayAlt.P.B7.invM (k := k) (r := r)) L.μW' L.μW')
    (hιN : MeasurePreserving (Formalism.FourierDecayAlt.P.B7.invM (k := k) (r := r)) L.μN L.μN)
    (hW1 : ∀ᵐ x ∂L.μW, Matrix.of x ∈ UWset k r L.z) (hW1' : ∀ᵐ x ∂L.μW', Matrix.of x ∈ UWset k r L.z')
    (hN1 : ∀ᵐ x ∂L.μN, Matrix.of x ∈ Nset k r)
    (w0 v v' : L.Hs) (ξ : L.Wp) (ξ' : L.Wq) (l : L.Hs → L.Wp) (l' : L.Hs → L.Wq)
    {γ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} {x : Mt k r}
    (hx : Matrix.of x ∈ UH (Hpk k r)) (hγx : γ * Matrix.of x ∈ UH (Hpk k r))
    (hbe : Formalism.FourierDecayAlt.ThreeDimData.be L.z L.c L.π L.σ L.μW L.μN (L.σ (γ * Matrix.of x) w0) v =
      (innerSL ℂ (l v)).smulRight (l (L.σ (γ * Matrix.of x) w0)))
    (hbe' : Formalism.FourierDecayAlt.ThreeDimData.be L.z' L.c L.π' L.σ L.μW' L.μN (L.σ (Matrix.of x) w0) v' =
      (innerSL ℂ (l' v')).smulRight (l' (L.σ (Matrix.of x) w0)))
    (hI : Integrable (fun p => Psi L w0 v v' ξ ξ' γ p x) (pairMeas L)) :
    ∫ p, Psi L w0 v v' ξ ξ' γ p x ∂(pairMeas L) =
      (⟪l v, ξ⟫_ℂ * ⟪ξ', l' v'⟫_ℂ) • (innerSL ℂ (l' (L.σ (Matrix.of x) w0))).smulRight (l (L.σ (γ * Matrix.of x) w0)) := by
  have hσ : PI.UpqRep.IsDSHpk k r L.ε L.lam L.σ := L.hσ
  set a := aVec L.z L.c L.π L.σ w0 v ξ (γ * Matrix.of x) with ha_def
  set b := aVec L.z' L.c L.π' L.σ w0 v' ξ' (Matrix.of x) with hb_def
  have hPsi : (fun p => Psi L w0 v v' ξ ξ' γ p x) = fun q : PairSp k r => (innerSL ℂ (b q.2)).smulRight (a q.1) := rfl
  have hpm : pairMeas L = (L.μW.prod L.μN).prod (L.μW'.prod L.μN) := rfl
  have haS : AEStronglyMeasurable a (L.μW.prod L.μN) := aesm_aVec hσ L.hz.2 L.hπ L.c w0 v ξ hγx hW1 hN1
  have hbS : AEStronglyMeasurable b (L.μW'.prod L.μN) := aesm_aVec hσ L.hz'.2 L.hπ' L.c w0 v' ξ' hx hW1' hN1
  have ha_eq := fun hA => int_a_eq hσ L.hz.1 L.hz.2 L.hπ L.c w0 v ξ hγx hιW hιN hW1 hN1 l hbe hA
  have hb_eq := fun hB => int_a_eq hσ L.hz'.1 L.hz'.2 L.hπ' L.c w0 v' ξ' hx hιW' hιN hW1' hN1 l' hbe' hB
  have hRHS : (⟪l v, ξ⟫_ℂ * ⟪ξ', l' v'⟫_ℂ) •
      (innerSL ℂ (l' (L.σ (Matrix.of x) w0))).smulRight (l (L.σ (γ * Matrix.of x) w0)) =
      (innerSL ℂ (⟪l' v', ξ'⟫_ℂ • l' (L.σ (Matrix.of x) w0))).smulRight (⟪l v, ξ⟫_ℂ • l (L.σ (γ * Matrix.of x) w0)) := by
    rw [rankOne_smul]
    congr 2
    rw [← starRingEnd_apply, inner_conj_symm]
  rw [hRHS, hPsi, hpm]
  rw [hpm, hPsi] at hI
  have hprod : ∫⁻ q : PairSp k r, ‖(innerSL ℂ (b q.2)).smulRight (a q.1)‖ₑ ∂((L.μW.prod L.μN).prod (L.μW'.prod L.μN)) =
      (∫⁻ p, ‖a p‖ₑ ∂(L.μW.prod L.μN)) * ∫⁻ p, ‖b p‖ₑ ∂(L.μW'.prod L.μN) := by
    simp_rw [enorm_rankOne, mul_comm (‖b _‖ₑ)]
    exact lintegral_prod_mul haS.enorm hbS.enorm
  have hfin : (∫⁻ p, ‖a p‖ₑ ∂(L.μW.prod L.μN)) * ∫⁻ p, ‖b p‖ₑ ∂(L.μW'.prod L.μN) < ⊤ := by
    rw [← hprod]; exact hI.2
  by_cases hA0 : ∫⁻ p, ‖a p‖ₑ ∂(L.μW.prod L.μN) = 0
  · have hz : ∀ᵐ p ∂(L.μW.prod L.μN), a p = 0 :=
      ((lintegral_eq_zero_iff' haS.enorm).mp hA0).mono fun p hp => enorm_eq_zero.mp hp
    have e := ha_eq (Or.inr hz)
    rw [integral_eq_zero_of_ae hz] at e
    rw [← e, rankOne_zero_right]
    refine integral_eq_zero_of_ae ?_
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae hz] with q hq
    rw [hq, rankOne_zero_right]; rfl
  by_cases hB0 : ∫⁻ p, ‖b p‖ₑ ∂(L.μW'.prod L.μN) = 0
  · have hz : ∀ᵐ p ∂(L.μW'.prod L.μN), b p = 0 :=
      ((lintegral_eq_zero_iff' hbS.enorm).mp hB0).mono fun p hp => enorm_eq_zero.mp hp
    have e := hb_eq (Or.inr hz)
    rw [integral_eq_zero_of_ae hz] at e
    rw [← e, rankOne_zero_left]
    refine integral_eq_zero_of_ae ?_
    filter_upwards [Measure.quasiMeasurePreserving_snd.ae hz] with q hq
    rw [hq, rankOne_zero_left]; rfl
  have hAB := ENNReal.mul_lt_top_iff.mp hfin
  have hlt : (∫⁻ p, ‖a p‖ₑ ∂(L.μW.prod L.μN)) < ⊤ ∧ (∫⁻ p, ‖b p‖ₑ ∂(L.μW'.prod L.μN)) < ⊤ := by
    rcases hAB with h | h | h
    · exact h
    · exact absurd h hA0
    · exact absurd h hB0
  have haI : Integrable a (L.μW.prod L.μN) := ⟨haS, hlt.1⟩
  have hbI : Integrable b (L.μW'.prod L.μN) := ⟨hbS, hlt.2⟩
  rw [integral_rankOne_prod haI hbI hI, ha_eq (Or.inl haI), hb_eq (Or.inl hbI)]

end Formalism.MainNotions.S.Pv.AmpDDPf
