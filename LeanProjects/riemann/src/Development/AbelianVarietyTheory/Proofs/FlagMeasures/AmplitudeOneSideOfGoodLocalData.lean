import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.NormalizedLocalScale
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsNormalFormStabilizerMeasure
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.DerivedActionDiscreteSeriesProperties
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.FrechetContinuousContinuousOnOrbitHasDerivAt
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FlagUnipotentLebesgueMeasureIsHaarOnStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HaarLieNilpotentEqLebesgueStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HcTypeWIrreducibleAndSchurAverage
open MeasureTheory Matrix Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.AmpSides

open Filter Topology GlobalTheory.CWDeriv

variable {k r : ℕ}

theorem cwCont_of {H Wp : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [NormedAddCommGroup Wp]
    {σ : Mat k r → (H →L[ℂ] H)} {Bm : H → Wp} (h : IsCWCont (k := k) (r := r) σ Bm) :
    PI.BesselMapUniq.IsCWCont (k := k) (r := r) σ Bm := by
  have e : ∀ (w : List (Mat k r)) (v : H),
      dsigW (k := k) (r := r) σ w v = PI.UpqRep.dsigW (k := k) (r := r) σ w v := by
    intro w v
    induction w with
    | nil => rfl
    | cons X w ih => show dsig σ X _ = PI.UpqRep.dsig σ X _; rw [ih]; rfl
  unfold IsCWCont at h
  simp only [e] at h
  exact h

theorem continuousOn_orbit {ε : Fin (2 * r + k + 1) → Bool} {mu : Fin (2 * r + k + 1) → ℝ} (R : BranchingSupport.Rep k r)
    (hR : R.IsDS ε mu) {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] (Bm : R.H → V)
    (ha : ∀ v ∈ R.sm, ∀ w ∈ R.sm, Bm (v + w) = Bm v + Bm w) (hs : ∀ (a : ℂ), ∀ v ∈ R.sm, Bm (a • v) = a • Bm v)
    (hB : PI.BesselMapUniq.IsCWCont (k := k) (r := r) R.σ Bm) {v : R.H} (hv : v ∈ R.sm) :
    ContinuousOn (fun g => Bm (R.σ g v)) (GG k r) := by
  have hD : DerFacts R := fun X hX =>
    ⟨fun _ hv => ⟨DerivedAction.dsig_smooth hR.2 hX hv, DerivedAction.hasDerivAt_dsig hX hv⟩,
      fun _ hv _ hw => DerivedAction.dsig_skew hR.2 hX hv hw⟩
  have hsm := PI.UnitaryGroupMassFormula.CapelliEig.smooth_right_action k r ε mu R.H R.σ hR.2 v hv
  have h0 : (0 : R.H) ∈ R.sm := R.smSub.zero_mem
  have hB0 : Bm 0 = 0 := by simpa using hs 0 0 h0
  intro g hg
  have h1 := cw_tendsto hB (l := 𝓝[GG k r] g) (u := fun x => (1 : ℂ) • (R.σ x v - R.σ g v) - 0)
    (by
      filter_upwards [self_mem_nhdsWithin] with x hx
      exact sm_comb 1 (hsm x hx) (hsm g hg) h0)
    (by
      intro W hW
      have h2 : Tendsto _ (𝓝[GG k r] g) _ :=
        (smoothOnH_continuousOn (dsigW_orbit_smooth hR hD hv W hW) g hg).tendsto
      have hW0 : PI.UpqRep.dsigW (k := k) (r := r) R.σ W 0 = 0 := by
        have h := dsigW_comb hD W hW 0 h0 h0 h0
        simp only [zero_smul, zero_sub, neg_zero] at h
        rw [eq_neg_iff_add_eq_zero, ← two_smul ℂ] at h
        simpa using h
      rw [← tendsto_sub_nhds_zero_iff] at h2
      refine h2.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with x hx
      rw [dsigW_comb hD W hW 1 (hsm x hx) (hsm g hg) h0, hW0, one_smul, sub_zero])
  refine tendsto_sub_nhds_zero_iff.mp (h1.congr' ?_)
  filter_upwards [self_mem_nhdsWithin] with x hx
  rw [lin_comb ha hs 1 (hsm x hx) (hsm g hg) h0, hB0, one_smul, sub_zero]

theorem isHaarOn_smul {S : Set (Mat k r)} {μ : Measure (Mt k r)} (h : IsHaarOn S μ) {x : ℝ} (hx : 0 < x) :
    IsHaarOn S (ENNReal.ofReal x • μ) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨?_, fun h0 => h2 ?_, by rw [Measure.smul_apply, h3, smul_zero], fun s hs => by
    rw [Measure.map_smul, h4 s hs]⟩
  · exact inferInstanceAs (SigmaFinite (x.toNNReal • μ))
  · have h1 := Measure.measure_univ_eq_zero.2 h0
    rw [Measure.smul_apply, smul_eq_mul] at h1
    exact Measure.measure_univ_eq_zero.1 ((mul_eq_zero.1 h1).resolve_left (ENNReal.ofReal_pos.2 hx).ne')

theorem haarLie_eq (x : ℝ) :
    haarLie (Nset k r) (ENNReal.ofReal x) =
      ENNReal.ofReal (x * 2 ^ (r * (k + 1) + r * (r - 1))) • lebN k r := by
  have h := GlobalTheory.T.haar_lie_nilpotent_eq_lebesgue k r
  unfold haarLie at h ⊢
  rw [one_smul] at h
  rw [h, smul_smul, mul_comm x, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by norm_num),
    mul_comm (ENNReal.ofReal x)]
  simp

theorem oneSide_of {H Wp : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    {ε : Fin (2 * r + k + 1) → Bool} {lam : Fin (2 * r + k + 1) → ℝ} {σ : Mat k r → (H →L[ℂ] H)}
    {z : Fin (2 * r + k + 1) → ℂ} {u : Fin k → ℝ} {π : Mat k r → (Wp →L[ℂ] Wp)} {c : ℂ}
    {μG μW νS : Measure (Mt k r)} {Bm : H → Wp} {v₀ : H} {cN x : ℝ} (hx : 0 < x)
    (hlam : IsHCParam lam) (hσ : IsDSHpk k r ε lam σ) (hz : inWb k r z) (hT : 0 < Tz k r z)
    (hπ : IsHCTypeW k r z u π) (hG : IsHaarOn (GG k r) μG) (hW : IsHaarOn (UWset k r z) μW) (hW1 : μW Set.univ = 1)
    (hq : IsQuotMeas μG (muS μW (haarLie (Nset k r) (ENNReal.ofReal x))) νS)
    (hB : IsBesselMapSm z (psi k r z c) σ π Bm) (hv : v₀ ∈ smoothVecs (k := k) (r := r) σ) (hc : 0 < cN)
    (hl : l2SG νS (fun g => Bm (σ g v₀)) = ENNReal.ofReal (cN * Module.finrank ℂ Wp)) :
    OneSide z π (psi k r z c) μG μW (ENNReal.ofReal (x * 2 ^ (r * (k + 1) + r * (r - 1))) • lebN k r) νS
      (fun g => Bm (σ g v₀)) cN := by
  let R : BranchingSupport.Rep k r := ⟨H, σ⟩
  have hR : R.IsDS ε lam := ⟨hlam, hσ⟩
  obtain ⟨e1, e2, e3⟩ := (GlobalTheory.Amp.Schur.type_irred_and_avg k r z π hz hT).1 u hπ
  rw [haarLie_eq] at hq
  refine ⟨hz, hT, e1, e2, e3, hG, hW, hW1, isHaarOn_smul (GlobalTheory.T.flagUnipotentLebesgueMeasure_isHaarOn k r) (by positivity), hq,
    fun n _ => by unfold psi; rw [mul_comm]; exact Complex.norm_exp_ofReal_mul_I _, fun a ha m hm g hg => ?_,
    continuousOn_orbit R hR Bm hB.1 hB.2.1 (cwCont_of hB.2.2.2) hv, hc, hl⟩
  have ham : a * m ∈ GG k r := (PI.UnitaryGroupMassFormula.CapelliEig.unitary_Hecke_group k r a ha.1).2.2 m hm.1
  have h1 := PI.UnitaryGroupMassFormula.CapelliEig.Hecke_multiplication k r ε lam H σ hσ _ ham g hg
  have h2 := PI.UnitaryGroupMassFormula.CapelliEig.smooth_right_action k r ε lam H σ hσ v₀ hv g hg
  show Bm (σ (a * m * g) v₀) = _
  rw [h1]
  exact hB.2.2.1 a ha m hm _ h2

theorem oneSide_of_good : ∀ (D : D7) (τ : D.what₂.Tau) (w w' : D.what₂.Word) (θ : ℝ) (W : LocW D.R.k D.R.rS) (lam : Fin (2 * D.R.rS + D.R.k + 1) → ℝ) (A : LocS W), 0 < D.host.v → 0 < θ → 0 < Tr D w → 0 < Tr D w' → GoodW D τ w w' θ W → GoodS D lam A → OneSide W.z W.π (psiS D W.z) W.μG W.μW (ENNReal.ofReal ((2 * D.host.v) ^ (-((D.R.rS : ℝ) * D.R.k)) * θ * 2 ^ (D.R.rS * (D.R.k + 1) + D.R.rS * (D.R.rS - 1))) • lebN D.R.k D.R.rS) W.νS A.Φ A.cN ∧ OneSide W.z' W.π' (psiS D W.z') W.μG W.μW' (ENNReal.ofReal ((2 * D.host.v) ^ (-((D.R.rS : ℝ) * D.R.k)) * θ * 2 ^ (D.R.rS * (D.R.k + 1) + D.R.rS * (D.R.rS - 1))) • lebN D.R.k D.R.rS) W.νS' A.Φ' A.cN := by
  intro D τ w w' θ W lam A hv hθ hT hT' hW hA
  obtain ⟨w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14⟩ := hW
  obtain ⟨a1, a2, a3, a4, a5, -, -, a8, a9, a10, -⟩ := hA
  rw [w12] at w13 w14
  have hx : 0 < (2 * D.host.v) ^ (-((D.R.rS : ℝ) * D.R.k)) * θ := by positivity
  exact ⟨oneSide_of hx a1 a2 w3 (w5 ▸ hT) w1 w7 w8 w9 w13 a3 a5 a8 a9,
    oneSide_of hx a1 a2 w4 (w6 ▸ hT') w2 w7 w10 w11 w14 a4 a5 a8 a10⟩

end GlobalTheory.AmpSides
