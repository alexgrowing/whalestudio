import Formalism.SharpRestriction.CuspSpanNormBounds.FrobeniusCoefficientMemLp.SigmaFiniteAmplitudes.NormPsiOne

noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal NNReal

namespace Formalism.MainNotions.S.Pv.AmpDDPf

open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S

variable {k r : ℕ}

attribute [local instance] Formalism.FourierDecayAlt.P.B7.properFD

section Ext

variable {H Wp : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [NormedAddCommGroup Wp]
  [InnerProductSpace ℂ Wp]

def cM (σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)) (v w0 : H) : Mt k r → ℂ :=
  {g : Mt k r | Matrix.of g ∈ UH (Hpk k r)}.indicator fun g => ⟪v, σ (Matrix.of g) w0⟫_ℂ

def piV (z : Fin (2 * r + k + 1) → ℂ)
    (π : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (Wp →L[ℂ] Wp)) (ξ : Wp) : Mt k r → Wp :=
  {h : Mt k r | Matrix.of h ∈ UWset k r z}.indicator fun h => π (Matrix.of h) ξ

def aM (z : Fin (2 * r + k + 1) → ℂ) (c : ℂ)
    (π : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (Wp →L[ℂ] Wp))
    (σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)) (w0 v : H) (ξ : Wp)
    (t : Mt k r) (p1 : Mt k r × Mt k r) : Wp :=
  (psi k r z c (Matrix.of p1.2) *
      cM σ v w0 (Formalism.FourierDecayAlt.P.B7.mulM (Formalism.FourierDecayAlt.P.B7.mulM (Formalism.FourierDecayAlt.P.B7.invM p1.1) (Formalism.FourierDecayAlt.P.B7.invM p1.2)) t)) •
    piV z π ξ p1.1

theorem meas_cM {ε : Fin (2 * r + k + 1) → Bool} {lam : Fin (2 * r + k + 1) → ℝ}
    {σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)}
    (hσ : PI.UpqRep.IsDSHpk k r ε lam σ) (v w0 : H) : Measurable (cM (k := k) (r := r) σ v w0) := by
  have h1 : ContinuousOn (fun g : Mt k r => σ (Matrix.of g) w0) {g : Mt k r | Matrix.of g ∈ UH (Hpk k r)} :=
    Formalism.FourierDecayAlt.P.S3dx4.sigma_contOn hσ w0
  exact Formalism.FourierDecayAlt.P.B7.meas_ind Formalism.FourierDecayAlt.P.B7.isClosed_GV.measurableSet (continuousOn_const.inner h1)

theorem sm_piV [FiniteDimensional ℂ Wp] {z : Fin (2 * r + k + 1) → ℂ} {u : Fin k → ℝ}
    {π : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (Wp →L[ℂ] Wp)}
    (hT : 0 < Tz k r z) (hπ : PI.UpqRep.IsHCTypeW k r z u π) (ξ : Wp) :
    StronglyMeasurable (piV (k := k) (r := r) z π ξ) := by
  have h1 : ContinuousOn (fun h : Mt k r => π (Matrix.of h) ξ) {h : Mt k r | Matrix.of h ∈ UWset k r z} :=
    Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.piW_cont hT hπ ξ
  exact Formalism.FourierDecayAlt.P.B7.sm_ind (Formalism.FourierDecayAlt.P.B7.isClosed_UW z).measurableSet h1

theorem measurable_mul_inv_inv {α : Type*} [MeasurableSpace α] {f g t : α → Mt k r} (hf : Measurable f)
    (hg : Measurable g) (ht : Measurable t) :
    Measurable fun a => Formalism.FourierDecayAlt.P.B7.mulM (Formalism.FourierDecayAlt.P.B7.mulM (Formalism.FourierDecayAlt.P.B7.invM (f a))
      (Formalism.FourierDecayAlt.P.B7.invM (g a))) (t a) :=
  Formalism.FourierDecayAlt.P.B7.meas_mulM (Formalism.FourierDecayAlt.P.B7.meas_mulM (Formalism.FourierDecayAlt.P.B7.measurable_invM.comp hf)
    (Formalism.FourierDecayAlt.P.B7.measurable_invM.comp hg)) ht

theorem sm_aM [FiniteDimensional ℂ Wp] {ε : Fin (2 * r + k + 1) → Bool} {lam : Fin (2 * r + k + 1) → ℝ}
    {σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)}
    (hσ : PI.UpqRep.IsDSHpk k r ε lam σ) {z : Fin (2 * r + k + 1) → ℂ} {u : Fin k → ℝ}
    {π : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (Wp →L[ℂ] Wp)}
    (hT : 0 < Tz k r z) (hπ : PI.UpqRep.IsHCTypeW k r z u π) (c : ℂ) (w0 v : H) (ξ : Wp)
    {α : Type*} [MeasurableSpace α] {t : α → Mt k r} {p1 : α → Mt k r × Mt k r} (ht : Measurable t)
    (hp1 : Measurable p1) :
    StronglyMeasurable fun a => aM z c π σ w0 v ξ (t a) (p1 a) := by
  have hps : Measurable fun a => psi k r z c (Matrix.of (p1 a).2) :=
    (Formalism.FourierDecayAlt.P.S3dx6.continuous_psi z c).measurable.comp (measurable_snd.comp hp1)
  have hc : Measurable fun a => cM σ v w0 (Formalism.FourierDecayAlt.P.B7.mulM (Formalism.FourierDecayAlt.P.B7.mulM
      (Formalism.FourierDecayAlt.P.B7.invM (p1 a).1) (Formalism.FourierDecayAlt.P.B7.invM (p1 a).2)) (t a)) :=
    (meas_cM hσ v w0).comp (measurable_mul_inv_inv (measurable_fst.comp hp1) (measurable_snd.comp hp1) ht)
  exact (hps.mul hc).stronglyMeasurable.smul ((sm_piV hT hπ ξ).comp_measurable (measurable_fst.comp hp1))

end Ext

def PsiM (L : LocBessel k r) (w0 v v' : L.Hs) (ξ : L.Wp) (ξ' : L.Wq)
    (γ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (q : PairSp k r × Mt k r) : L.Wq →L[ℂ] L.Wp :=
  (innerSL ℂ (aM L.z' L.c L.π' L.σ w0 v' ξ' q.2 q.1.2)).smulRight
    (aM L.z L.c L.π L.σ w0 v ξ (Formalism.FourierDecayAlt.P.B7.mulM (γ : Mt k r) q.2) q.1.1)

theorem continuous_rankOne {E F : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] :
    Continuous fun q : E × F => (innerSL ℂ q.1).smulRight q.2 :=
  (ContinuousLinearMap.smulRightL ℂ E F).continuous₂.comp
    (((innerSL ℂ (E := E)).continuous.comp continuous_fst).prodMk continuous_snd)

theorem sm_PsiM (L : LocBessel k r) (w0 v v' : L.Hs) (ξ : L.Wp) (ξ' : L.Wq)
    (γ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    StronglyMeasurable (PsiM L w0 v v' ξ ξ' γ) := by
  have hσ : PI.UpqRep.IsDSHpk k r L.ε L.lam L.σ := L.hσ
  have hb := sm_aM hσ L.hz'.2 L.hπ' L.c w0 v' ξ' (t := fun q : PairSp k r × Mt k r => q.2)
    (p1 := fun q : PairSp k r × Mt k r => q.1.2) measurable_snd (measurable_snd.comp measurable_fst)
  have ha := sm_aM hσ L.hz.2 L.hπ L.c w0 v ξ
    (t := fun q : PairSp k r × Mt k r => Formalism.FourierDecayAlt.P.B7.mulM (γ : Mt k r) q.2)
    (p1 := fun q : PairSp k r × Mt k r => q.1.1)
    (Formalism.FourierDecayAlt.P.B7.meas_mulM measurable_const measurable_snd) (measurable_fst.comp measurable_fst)
  exact continuous_rankOne.comp_stronglyMeasurable (hb.prodMk ha)

theorem PsiM_eq (L : LocBessel k r) (w0 v v' : L.Hs) (ξ : L.Wp) (ξ' : L.Wq)
    {γ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hγ : γ ∈ UH (Hpk k r))
    {p : PairSp k r} (hp : InPair L p) {x : Mt k r} (hx : Matrix.of x ∈ UH (Hpk k r)) :
    PsiM L w0 v v' ξ ξ' γ (p, x) = Psi L w0 v v' ξ ξ' γ p x := by
  obtain ⟨hh, hn, hh', hn'⟩ := hp
  have g1 : (Matrix.of p.1.1)⁻¹ * (Matrix.of p.1.2)⁻¹ * (γ * Matrix.of x) ∈ UH (Hpk k r) :=
    Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul (Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul (Formalism.QuantumDeterminants.WeylGroupFacts.uh_inv (uh_of_uw hh))
      (Formalism.QuantumDeterminants.WeylGroupFacts.uh_inv (uh_of_n hn))) (Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul hγ hx)
  have g2 : (Matrix.of p.2.1)⁻¹ * (Matrix.of p.2.2)⁻¹ * Matrix.of x ∈ UH (Hpk k r) :=
    Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul (Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul (Formalism.QuantumDeterminants.WeylGroupFacts.uh_inv (uh_of_uw hh'))
      (Formalism.QuantumDeterminants.WeylGroupFacts.uh_inv (uh_of_n hn'))) hx
  have e1 : cM L.σ v w0 (Formalism.FourierDecayAlt.P.B7.mulM (Formalism.FourierDecayAlt.P.B7.mulM (Formalism.FourierDecayAlt.P.B7.invM p.1.1)
      (Formalism.FourierDecayAlt.P.B7.invM p.1.2)) (Formalism.FourierDecayAlt.P.B7.mulM (γ : Mt k r) x)) =
      ⟪v, L.σ ((Matrix.of p.1.1)⁻¹ * (Matrix.of p.1.2)⁻¹ * (γ * Matrix.of x)) w0⟫_ℂ :=
    Set.indicator_of_mem (s := {g : Mt k r | Matrix.of g ∈ UH (Hpk k r)}) g1 _
  have e2 : cM L.σ v' w0 (Formalism.FourierDecayAlt.P.B7.mulM (Formalism.FourierDecayAlt.P.B7.mulM (Formalism.FourierDecayAlt.P.B7.invM p.2.1)
      (Formalism.FourierDecayAlt.P.B7.invM p.2.2)) x) =
      ⟪v', L.σ ((Matrix.of p.2.1)⁻¹ * (Matrix.of p.2.2)⁻¹ * Matrix.of x) w0⟫_ℂ :=
    Set.indicator_of_mem (s := {g : Mt k r | Matrix.of g ∈ UH (Hpk k r)}) g2 _
  have e3 : piV L.z L.π ξ p.1.1 = L.π (Matrix.of p.1.1) ξ :=
    Set.indicator_of_mem (s := {h : Mt k r | Matrix.of h ∈ UWset k r L.z}) hh _
  have e4 : piV L.z' L.π' ξ' p.2.1 = L.π' (Matrix.of p.2.1) ξ' :=
    Set.indicator_of_mem (s := {h : Mt k r | Matrix.of h ∈ UWset k r L.z'}) hh' _
  simp only [PsiM, aM, Psi, aVec]
  rw [e1, e2, e3, e4]

end Formalism.MainNotions.S.Pv.AmpDDPf
