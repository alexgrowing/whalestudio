import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.OnePlaceKF
import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.CellDataExists
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CellDataSupport
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AmplitudesRelevantCellMonomialRep
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsUnipotentHaarMeasureRatioStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.SymmetricMeasureL2NormEqResolutionL2
import Formalism.HermitianCurvature.HermitianCurvatureProofs.IntegrableUnipotentNormRpowNeg
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SliceLastLevel
open BranchingSupport GlobalTheory.CellAmp Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

noncomputable section

namespace GlobalTheory.CellMaj

open Formalism.FourierDecayAlt in

theorem polyProper5 (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (γ : B.Mat k r) (hstd : C2.Std k r z z')
    (hpos : C2.PosPt k r z z' γ) (hmono : C2.IsMonomial (Zhat k r z z' γ)) :
    ∃ C : ℝ, ∀ σ ∈ C2.Sg k r z z' γ, ∀ s' ∈ Sset k r z',
      B.gN σ + B.gN s' ≤ C * B.gN (σ⁻¹ * γ * s') ^ (5 * (r + 1) ^ 2) := by
  open PI.PolynomialProperness in
  have hS := frameS_of Formalism.FourierDecayAlt.P.unipotent_map_frame gvGroup
  open PI.PolynomialProperness in
  have hSg := frameSg_of Formalism.FourierDecayAlt.P.unipotent_map_frame (tauMem_of mxFacts TauN.neFacts) gvGroup
  open PI.PolynomialProperness in
  have hA := unitriangular_inverse_bound second_order_norm_bound
  open PI.PolynomialProperness in
  have hC := coreInst_of isoCore hpkInvol gnFacts frameInd
  open PI.PolynomialProperness in
  have hG := gvGroup
  open PI.PolynomialProperness in
  have hN := normInv
  open PI.PolynomialProperness in
  have hNF := gnFacts
  open PI.PolynomialProperness in
  have hF := fmulBound
  open PI.PolynomialProperness in
  have hZ := zhatMove
  obtain ⟨CA, hA1, -⟩ := hA k r z z' γ hmono
  obtain ⟨Cc, hCc⟩ := hC k r z z' γ hstd hpos
  obtain ⟨Cf, hCf⟩ := hF k r z
  obtain ⟨Cf', hCf'⟩ := hF k r z'
  have hγ : γ ∈ B.GV k r := hpos.1
  obtain ⟨hmul, hinv⟩ := hG k r
  refine ⟨(1 + B.gN γ⁻¹) * (|Cc| * (1 + (|Cf| + |Cf'|) * CA ^ 2) ^ 2), ?_⟩
  intro σ hσ s' hs'
  obtain ⟨hσG, v, hv, hvL, hσf⟩ := hSg k r z z' γ hstd σ hσ
  obtain ⟨hs'G, u', hu, hsf⟩ := hS k r z' hstd.2.2 s' hs'
  have hg : σ⁻¹ * γ * s' ∈ B.GV k r := hmul _ (hmul _ (hinv σ hσG).2.1 _ hγ) _ hs'G
  have hg1 := (hN k r _ hg).2
  have hZg := hZ k r z z' γ σ s' v u' hσG hs'G hσf hsf
  obtain ⟨hbv, hbu⟩ := hA1 v hv hvL u' hu _ hg1 hZg
  exact PI.PolynomialProperness.bound_core hG hN hNF hγ hCf hCf' hCc σ s' v u' hσG hs'G hv hu hσf hsf hbv hbu

open Formalism.FourierDecayAlt in

theorem haar_stab {k r : ℕ} (L : LocBessel k r) (hk : 1 ≤ k) {γ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hγ : γ ∈ UH (Hpk k r)) (hpos : 0 < Gf k r L.z L.z' γ) (hmono : C2.IsMonomial (Zhat k r L.z L.z' γ))
    {μR : Measure (Mt k r)} (hR : IsHaarOn (RStab k r γ) μR) {M : ℝ} (hM : 2 * ((r : ℝ) + 1) ^ 2 < M) :
    B.IsHaarOn (C6.Rset γ) μR ∧ Integrable (fun x : Mt k r => B.gN (Matrix.of x) ^ (-M)) μR := by
  obtain ⟨Bs, hz, hz'⟩ := GlobalTheory.CellRed.exists_setting hk L.hz.1 L.hz'.1 L.hz.2 L.hz'.2
  rw [← hz, ← hz'] at hpos hmono
  obtain ⟨w, d, hd, hZ⟩ := hmono
  have hG : P.Dx2.Rad.Good Bs γ w d := ⟨P.Dx2.Rad.exists_rho Bs hγ hpos hd hZ, P.Dx2.Rad.u_inj Bs hγ hpos hd hZ,
    fun ρ hρ => P.Dx2.Rad.u_lstg Bs hγ hpos hd hZ hρ⟩
  have hRB := P.Dx2.Rad.haar_good Bs hγ hd hG
  have hu : IsUnit γ.det := P.Dx2.OrbJ.isUnit_of_G hγ
  obtain ⟨c, c0, ct, hc⟩ := GlobalTheory.BesselPeriodCompare.haar_unique (P.Dx2.OrbJ.closedR hu) (μ := μR)
    (ν := Formalism.FourierDecayAlt.D.muR Bs γ w) hR ⟨P.Dx2.OrbJ.sigmaF hRB, hRB.ne_zero, hRB.conc, hRB.left⟩
  rw [hc]
  exact ⟨GlobalTheory.ThA.OrbSq.haar_smul hRB c0 ct, (P.Dx3.intR Bs hγ hd hG hM).smul_measure ct⟩

open Formalism.FourierDecayAlt in

theorem intN_zero {k : ℕ} {μN : Measure (Mt k 0)} (hN : B.IsHaarOn (Nset k 0) μN) {a : ℝ} (ha : 0 ≤ a) :
    Integrable (fun x : Mt k 0 => B.gN (Matrix.of x) ^ (-a)) μN := by
  have hsub : (Nset k 0 : Set (B.Mat k 0)) ⊆ {(1 : B.Mat k 0)} := fun x hx => P.SliceLastLevel.sz_N_zero hx
  have hfin : IsFiniteMeasure μN := by
    refine ⟨?_⟩
    calc μN Set.univ ≤ μN (Nset k 0) + μN (Nset k 0)ᶜ := measure_univ_le_add_compl _
      _ = μN (Nset k 0) := by rw [hN.conc, add_zero]
      _ ≤ μN {(1 : B.Mat k 0)} := measure_mono hsub
      _ < ∞ := hN.finite_compact _ isCompact_singleton
  refine Integrable.mono' (integrable_const (1 : ℝ))
    (((P.HaarUniquenessConjugation.gN_meas k 0).pow_const _).aestronglyMeasurable) ?_
  filter_upwards [P.Dx2.OrbJ.ae_mem hN] with x hx
  have h1 : 1 ≤ B.gN (Matrix.of x : B.Mat k 0) := P.BetaSesquilinearity.gN_ge_one hx.1
  rw [Real.norm_of_nonneg (Real.rpow_nonneg (by linarith) _)]
  exact Real.rpow_le_one_of_one_le_of_nonpos h1 (by linarith)

open Formalism.FourierDecayAlt in

theorem maj_pair {k r : ℕ} (L : LocBessel k r) (hκ : L.κN ≠ ⊤) {α β : ℝ}
    (hα : Integrable (fun x : Mt k r => B.gN (Matrix.of x) ^ (-α)) (Formalism.FourierDecayAlt.D.muN k r))
    (hβ : Integrable (fun x : Mt k r => B.gN (Matrix.of x) ^ (-β)) (Formalism.FourierDecayAlt.D.muN k r)) :
    Integrable (fun p : PairSp k r => B.gN (Matrix.of p.1.2) ^ (-α) * B.gN (Matrix.of p.2.2) ^ (-β)) (pairMeas L) := by
  obtain ⟨cN, hN⟩ := GlobalTheory.T.exists_unipotentHaarMeasure_ratio k r
  have e : L.μN = (L.κN * ENNReal.ofReal cN) • Formalism.FourierDecayAlt.D.muN k r := by
    rw [← smul_smul, ← hN.2]
    unfold LocBessel.μN haarLie
    rw [one_smul]
  have hct : L.κN * ENNReal.ofReal cN ≠ ⊤ := ENNReal.mul_ne_top hκ ENNReal.ofReal_ne_top
  have := P.Dx2.OrbJ.sigmaF (P.nilpotent_measure_is_haar k r)
  have hsN : SigmaFinite L.μN := by
    rw [e, ← ENNReal.coe_toNNReal hct]
    first
    | exact inferInstance
    | exact (inferInstance : SigmaFinite ((L.κN * ENNReal.ofReal cN).toNNReal • Formalism.FourierDecayAlt.D.muN k r))
  have : IsFiniteMeasure L.μW := ⟨by rw [L.hμW.2]; exact ENNReal.one_lt_top⟩
  have : IsFiniteMeasure L.μW' := ⟨by rw [L.hμW'.2]; exact ENNReal.one_lt_top⟩
  have hα' : Integrable (fun x : Mt k r => B.gN (Matrix.of x) ^ (-α)) L.μN := by rw [e]; exact hα.smul_measure hct
  have hβ' : Integrable (fun x : Mt k r => B.gN (Matrix.of x) ^ (-β)) L.μN := by rw [e]; exact hβ.smul_measure hct
  have i1 : Integrable (fun q : Mt k r × Mt k r => (1 : ℝ) * B.gN (Matrix.of q.2) ^ (-α)) (L.μW.prod L.μN) :=
    (integrable_const (1 : ℝ)).mul_prod hα'
  have i2 : Integrable (fun q : Mt k r × Mt k r => (1 : ℝ) * B.gN (Matrix.of q.2) ^ (-β)) (L.μW'.prod L.μN) :=
    (integrable_const (1 : ℝ)).mul_prod hβ'
  have i3 := i1.mul_prod i2
  unfold pairMeas
  simpa only [one_mul] using i3

open Formalism.FourierDecayAlt in

theorem bound_pt {k r : ℕ} (Bs : B.RealPlaceData k r ℂ ℂ) {γ : B.Mat k r} (hγ : γ ∈ B.GV k r)
    (hpos : 0 < Gf k r Bs.z Bs.z' γ) (hmono : C2.IsMonomial (Zhat k r Bs.z Bs.z' γ))
    {μR : Measure (Mt k r)} (hR : B.IsHaarOn (C6.Rset γ) μR) {M : ℝ} (hM0 : 0 ≤ M)
    (hI : Integrable (fun x : Mt k r => B.gN (Matrix.of x) ^ (-M)) μR) {b bN : ℝ} (hbN : 0 ≤ bN)
    (hMdef : M = b / ((5 * (r + 1) ^ 2 : ℕ) : ℝ) - 2 * bN) (h4 : 4 * bN ≤ b / ((5 * (r + 1) ^ 2 : ℕ) : ℝ)) :
    ∃ K : ℝ, ∀ p : B.SS k r, Bs.inSS p → P.Dx3.cut μR M p * pairMaj γ b p ≤
      K * (B.gN (Matrix.of p.1.2) ^ (-(b / ((5 * (r + 1) ^ 2 : ℕ) : ℝ) - 3 * bN)) * B.gN (Matrix.of p.2.2) ^ (-bN)) := by
  set c : ℕ := 5 * (r + 1) ^ 2 with hc
  have hc1 : 1 ≤ c := Nat.one_le_iff_ne_zero.mpr (by positivity)
  obtain ⟨CP, hCP⟩ := polyProper5 k r Bs.z Bs.z' γ (P.Dx2.Rad.std Bs) ⟨hγ, hpos⟩ hmono
  have hone : Matrix.of (Matrix.of.symm (1 : B.Mat k r)) ∈ B.GV k r := by
    simpa using (P.unitary_group_closed k r).one_mem
  set cR : ℝ := ∫ x, B.gN (Matrix.of x) ^ (-M) ∂μR with hcRdef
  have hcR : 0 < cR := by
    have := P.Dx3.om_pos hR hM0 hI hone
    simpa [P.Dx3.Om] using this
  obtain ⟨KW, hKW1, hKW⟩ := P.Dx3.UW_bound Bs.z Bs.z_mem Bs.T_pos
  obtain ⟨KW', hKW1', hKW'⟩ := P.Dx3.UW_bound Bs.z' Bs.z'_mem Bs.T'_pos
  set K1 := KW * KW' with hK1
  set Kγ := B.gN γ⁻¹ * B.gN γ with hKγ
  have hγ1 : 1 ≤ B.gN γ := P.BetaSesquilinearity.gN_ge_one hγ
  have hγi : B.gN γ⁻¹ = B.gN γ := (P.norm_of_inverse k r γ hγ).1
  have hKγ0 : 0 < Kγ := by rw [hKγ, hγi]; nlinarith
  have hK10 : 0 < K1 := by rw [hK1]; positivity
  refine ⟨(1 : ℝ) * K1 ^ b * CP ^ (b / c) * Kγ ^ bN / cR, fun p hp => ?_⟩
  obtain ⟨h1, h2, h3, h4'⟩ := hp
  obtain ⟨ρ, σ, X, hρ, hσ, hnρσ, hσX, hXY, hn'le⟩ := P.Dx3.geom Bs hγ hpos hCP hmono h2 h4'
  have hN1 : 1 ≤ B.gN (Matrix.of p.1.2 : B.Mat k r) := P.BetaSesquilinearity.gN_ge_one h2.1
  have hN1' : 1 ≤ B.gN (Matrix.of p.2.2 : B.Mat k r) := P.BetaSesquilinearity.gN_ge_one h4'.1
  have hS1 : 1 ≤ B.gN σ := P.BetaSesquilinearity.gN_ge_one hσ
  have hg0 : (Matrix.of p.1.2 : B.Mat k r)⁻¹ * γ * Matrix.of p.2.2 ∈ B.GV k r :=
    Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul (Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul (Formalism.QuantumDeterminants.WeylGroupFacts.uh_inv h2.1) hγ) h4'.1
  have hY1 : 1 ≤ B.gN ((Matrix.of p.1.2 : B.Mat k r)⁻¹ * γ * Matrix.of p.2.2) := P.BetaSesquilinearity.gN_ge_one hg0
  have hsgs := P.B7.sgs_mem Bs ⟨h1, h2, h3, h4'⟩ hγ
  have hGg : 0 < B.gN (B.sgs p γ) := by linarith [P.BetaSesquilinearity.gN_ge_one hsgs]
  have hYG : B.gN ((Matrix.of p.1.2 : B.Mat k r)⁻¹ * γ * Matrix.of p.2.2) ≤ K1 * B.gN (B.sgs p γ) := by
    have hhu : IsUnit (Matrix.of p.1.1 : B.Mat k r).det := (P.unitary_group_closed k r).unit _ h1.1
    have hh'u : IsUnit (Matrix.of p.2.1 : B.Mat k r).det := (P.unitary_group_closed k r).unit _ h3.1
    have e : (Matrix.of p.1.2 : B.Mat k r)⁻¹ * γ * Matrix.of p.2.2 =
        (Matrix.of p.1.1 : B.Mat k r) * B.sgs p γ * (Matrix.of p.2.1 : B.Mat k r)⁻¹ := by
      simp only [B.sgs, Matrix.mul_assoc]
      rw [Matrix.mul_nonsing_inv_cancel_left _ _ hhu, Matrix.mul_nonsing_inv _ hh'u, Matrix.mul_one]
    rw [e]
    calc B.gN ((Matrix.of p.1.1 : B.Mat k r) * B.sgs p γ * (Matrix.of p.2.1 : B.Mat k r)⁻¹)
        ≤ B.gN (Matrix.of p.1.1 : B.Mat k r) * B.gN (B.sgs p γ) * B.gN (Matrix.of p.2.1 : B.Mat k r)⁻¹ :=
          (P.B6.gN_mul_le _ _).trans (mul_le_mul_of_nonneg_right (P.B6.gN_mul_le _ _) (P.B6.gN_nonneg _))
      _ ≤ KW * B.gN (B.sgs p γ) * KW' := by
          have a1 := hKW _ h1
          have a2 := hKW' _ (Formalism.QuantumDeterminants.WeylGroupFacts.uw_inv h3)
          have s0 := P.B6.gN_nonneg (B.sgs p γ)
          exact mul_le_mul (mul_le_mul_of_nonneg_right a1 s0) a2 (P.B6.gN_nonneg _)
            (mul_nonneg (by linarith) s0)
      _ = K1 * B.gN (B.sgs p γ) := by rw [hK1]; ring
  have hθ : P.Dx3.cut μR M p ≤ B.gN (Matrix.of p.1.2 : B.Mat k r) ^ (-M) * B.gN σ ^ M / cR := by
    have hlow := P.Dx3.om_lower hR hM0 hI hρ hσ
    have e : Matrix.of.symm (ρ * σ) = p.1.2 := by rw [← hnρσ]; exact Equiv.symm_apply_apply _ _
    rw [e] at hlow
    have hσp : 0 < B.gN σ ^ (-M) := Real.rpow_pos_of_pos (by linarith) _
    have hpos' : 0 < cR * B.gN σ ^ (-M) := mul_pos hcR hσp
    unfold P.Dx3.cut
    calc B.gN (Matrix.of p.1.2 : B.Mat k r) ^ (-M) / P.Dx3.Om μR M p.1.2
        ≤ B.gN (Matrix.of p.1.2 : B.Mat k r) ^ (-M) / (cR * B.gN σ ^ (-M)) :=
          div_le_div_of_nonneg_left (Real.rpow_nonneg (P.B6.gN_nonneg _) _) hpos' hlow
      _ = B.gN (Matrix.of p.1.2 : B.Mat k r) ^ (-M) * B.gN σ ^ M / cR := by
          rw [Real.rpow_neg (P.B6.gN_nonneg σ)]
          have : 0 < B.gN σ ^ M := Real.rpow_pos_of_pos (by linarith) _
          field_simp
  have hθ0 := P.Dx3.cut_nonneg μR M p
  have hFv : pairMaj γ b p ≤ 1 * B.gN (B.sgs p γ) ^ (-b) := by rw [one_mul]; exact le_of_eq rfl
  have hF0 : 0 ≤ pairMaj γ b p := Real.rpow_nonneg (P.B6.gN_nonneg _) _
  have hCP0 : 0 < CP := by
    by_contra hle'
    have hle := not_lt.mp hle'
    have := mul_nonpos_of_nonpos_of_nonneg hle
      (pow_nonneg (P.B6.gN_nonneg ((Matrix.of p.1.2 : B.Mat k r)⁻¹ * γ * Matrix.of p.2.2)) c)
    linarith
  exact P.Dx3.key_real hN1 hS1 hσX hY1 hGg hc1 hXY hn'le hN1' hYG hθ hθ0 hFv hF0 hcR
    zero_le_one hCP0 hK10 hKγ0 hMdef hbN h4

open Formalism.FourierDecayAlt in

theorem meas_inv (k r : ℕ) :
    Measurable (fun x : Mt k r => (Matrix.of.symm ((Matrix.of x : B.Mat k r)⁻¹) : Mt k r)) := by
  refine measurable_pi_iff.mpr fun i => measurable_pi_iff.mpr fun j => ?_
  have hdet : Continuous fun x : Mt k r => (Matrix.of x : B.Mat k r).det :=
    (continuous_id (X := B.Mat k r)).matrix_det
  have hadj : Continuous fun x : Mt k r => (Matrix.of x : B.Mat k r).adjugate i j :=
    ((continuous_id (X := B.Mat k r)).matrix_adjugate).matrix_elem i j
  have e : (fun x : Mt k r => (Matrix.of.symm ((Matrix.of x : B.Mat k r)⁻¹) : Mt k r) i j) =
      fun x => ((Matrix.of x : B.Mat k r).det)⁻¹ * (Matrix.of x : B.Mat k r).adjugate i j := by
    funext x
    show ((Matrix.of x : B.Mat k r)⁻¹) i j = _
    rw [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul]
  rw [e]
  exact hdet.measurable.inv.mul hadj.measurable

open Formalism.FourierDecayAlt in

theorem meas_pairMaj {k r : ℕ} (γ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (b : ℝ) :
    Measurable (pairMaj (k := k) (r := r) γ b) := by
  have hc : Continuous fun q : (Mt k r × Mt k r) × (Mt k r × Mt k r) =>
      (Matrix.of.symm ((Matrix.of q.1.1 : B.Mat k r) * Matrix.of q.1.2 * γ * Matrix.of q.2.2 * Matrix.of q.2.1) : Mt k r) := by
    have a1 : Continuous fun q : (Mt k r × Mt k r) × (Mt k r × Mt k r) => (Matrix.of q.1.1 : B.Mat k r) := continuous_fst.fst
    have a2 : Continuous fun q : (Mt k r × Mt k r) × (Mt k r × Mt k r) => (Matrix.of q.1.2 : B.Mat k r) := continuous_fst.snd
    have a3 : Continuous fun q : (Mt k r × Mt k r) × (Mt k r × Mt k r) => (Matrix.of q.2.1 : B.Mat k r) := continuous_snd.fst
    have a4 : Continuous fun q : (Mt k r × Mt k r) × (Mt k r × Mt k r) => (Matrix.of q.2.2 : B.Mat k r) := continuous_snd.snd
    exact (((a1.matrix_mul a2).matrix_mul continuous_const).matrix_mul a4).matrix_mul a3
  have hm : Measurable fun p : PairSp k r =>
      (((Matrix.of.symm ((Matrix.of p.1.1 : B.Mat k r)⁻¹) : Mt k r), (Matrix.of.symm ((Matrix.of p.1.2 : B.Mat k r)⁻¹) : Mt k r)),
        (p.2.1, p.2.2)) :=
    (((meas_inv k r).comp measurable_fst.fst).prodMk ((meas_inv k r).comp measurable_fst.snd)).prodMk
      (measurable_snd.fst.prodMk measurable_snd.snd)
  have h := hc.measurable.comp hm
  exact ((P.HaarUniquenessConjugation.gN_meas k r).comp h).pow_const _

open Formalism.FourierDecayAlt in

theorem core {k r : ℕ} (L : LocBessel k r) (hk : 1 ≤ k) (hκ : L.κN ≠ ⊤)
    {γ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hγ : γ ∈ UH (Hpk k r))
    (hpos : 0 < Gf k r L.z L.z' γ) (hmono : C2.IsMonomial (Zhat k r L.z L.z' γ))
    {μR : Measure (Mt k r)} {ν : Measure (PairSp k r)} (hR : IsHaarOn (RStab k r γ) μR) (hQ : IsOrbQuot L γ μR ν)
    {b bN : ℝ} (hbN : 0 ≤ bN)
    (hIN : ∀ a, bN ≤ a → Integrable (fun x : Mt k r => B.gN (Matrix.of x) ^ (-a)) (Formalism.FourierDecayAlt.D.muN k r))
    (h4 : 4 * bN ≤ b / ((5 * (r + 1) ^ 2 : ℕ) : ℝ))
    (hM : 2 * ((r : ℝ) + 1) ^ 2 < b / ((5 * (r + 1) ^ 2 : ℕ) : ℝ) - 2 * bN) :
    Integrable (pairMaj γ b) ν := by
  set M : ℝ := b / ((5 * (r + 1) ^ 2 : ℕ) : ℝ) - 2 * bN with hMdef
  have hM0 : 0 ≤ M := by nlinarith [sq_nonneg ((r : ℝ) + 1)]
  obtain ⟨hRB, hI⟩ := haar_stab L hk hγ hpos hmono hR hM
  have := P.Dx2.OrbJ.sigmaF hRB
  obtain ⟨Bs, hz, hz'⟩ := GlobalTheory.CellRed.exists_setting hk L.hz.1 L.hz'.1 L.hz.2 L.hz'.2
  have hpos' : 0 < Gf k r Bs.z Bs.z' γ := by rw [hz, hz']; exact hpos
  have hmono' : C2.IsMonomial (Zhat k r Bs.z Bs.z' γ) := by rw [hz, hz']; exact hmono
  obtain ⟨K, hK⟩ := bound_pt Bs hγ hpos' hmono' hRB hM0 hI hbN hMdef h4
  have hmaj := (maj_pair L hκ (hIN (b / ((5 * (r + 1) ^ 2 : ℕ) : ℝ) - 3 * bN) (by linarith)) (hIN bN le_rfl)).const_mul K
  set θ : PairSp k r → ℝ := P.Dx3.cut μR M with hθdef
  have hθm : Measurable θ := P.Dx3.cut_meas M
  have hu : IsUnit γ.det := P.Dx2.OrbJ.isUnit_of_G hγ
  have hPm := meas_pairMaj (k := k) (r := r) γ b
  have hP0 : ∀ p, 0 ≤ pairMaj γ b p := fun p => Real.rpow_nonneg (P.B6.gN_nonneg _) _

  have hW := hQ (fun p => ENNReal.ofReal (θ p * pairMaj γ b p)) (ENNReal.measurable_ofReal.comp (hθm.mul hPm))
  have hinner : ∀ᵐ x ∂ν, (∫⁻ a, ENNReal.ofReal (θ (stabAct γ (Matrix.of a) x) * pairMaj γ b (stabAct γ (Matrix.of a) x)) ∂μR)
      = ENNReal.ofReal (pairMaj γ b x) := by
    filter_upwards [GlobalTheory.CellOrbInt.ae_quot L hR hQ] with x hx
    have aR : ∀ᵐ a ∂μR, Matrix.of a ∈ RStab k r γ := by rw [ae_iff]; exact hR.2.2.1
    have e1 : ∀ᵐ a ∂μR, ENNReal.ofReal (θ (stabAct γ (Matrix.of a) x) * pairMaj γ b (stabAct γ (Matrix.of a) x)) =
        ENNReal.ofReal (θ (C6.actR γ (Matrix.of a) x)) * ENNReal.ofReal (pairMaj γ b x) := by
      filter_upwards [aR] with a ha
      rw [GlobalTheory.CellAmp.Model.pairMaj_stabAct γ (Matrix.of a) hu (P.Dx2.OrbJ.isUnit_of_N ha.1) b x,
        ENNReal.ofReal_mul (P.Dx3.cut_nonneg μR M _)]
      rfl
    rw [lintegral_congr_ae e1, lintegral_mul_const' _ _ ENNReal.ofReal_ne_top]
    have hn := P.Dx3.cut_norm hRB hM0 hI x hx.2.1
    have hint : Integrable (fun a : Mt k r => θ (C6.actR γ (Matrix.of a) x)) μR :=
      Integrable.of_integral_ne_zero (by rw [hn]; exact one_ne_zero)
    rw [← ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall fun a => P.Dx3.cut_nonneg μR M _), hn,
      ENNReal.ofReal_one, one_mul]
  rw [lintegral_congr_ae hinner] at hW

  have hfin : ∫⁻ p, ENNReal.ofReal (θ p * pairMaj γ b p) ∂(pairMeas L) < ⊤ := by
    refine lt_of_le_of_lt (lintegral_mono_ae ?_) hmaj.lintegral_lt_top
    filter_upwards [GlobalTheory.CellOrbInt.ae_pairMeas L] with p hp
    refine ENNReal.ofReal_le_ofReal (hK p ?_)
    obtain ⟨h1, h2, h3, h4'⟩ := hp
    refine ⟨?_, h2, ?_, h4'⟩
    · rw [hz]; exact h1
    · rw [hz']; exact h3
  refine ⟨hPm.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall hP0), ← hW]
  exact hfin

open Formalism.FourierDecayAlt in

theorem cellConv : CellConv := by
  intro k r L h μG γ μR νR ν hκ hok hgap hC hmono
  obtain ⟨hγ, hpos, -, -, hR, hQ, -⟩ := hC
  have hk : 1 ≤ k := hok.1
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  have hdN : ThreeDimData.dN k r = 2 * (r : ℝ) ^ 2 + 2 * r * k + r := by unfold ThreeDimData.dN; ring
  have hAS : ThreeDimData.AS k r = ((2 * r + k : ℕ) : ℝ) * (2 * (r : ℝ) ^ 2 + 2 * r * k + r) := by
    unfold ThreeDimData.AS; rw [hdN]
  have hAS0 : 0 ≤ ThreeDimData.AS k r := by rw [hAS]; positivity
  have hAG : ThreeDimData.AG k r = 4 * ((k : ℝ) + r) * ((r : ℝ) + 1) := rfl
  have hAG0 : 0 ≤ ThreeDimData.AG k r := by rw [hAG]; positivity
  have he : ((5 * (r + 1) ^ 2 : ℕ) : ℝ) = 5 * ((r : ℝ) + 1) ^ 2 := by push_cast; ring
  have hepos : 0 < ((5 * (r + 1) ^ 2 : ℕ) : ℝ) := by rw [he]; positivity
  unfold GapCell at hgap
  have hRA : 0 ≤ ((r : ℝ) + 1) ^ 2 * (ThreeDimData.AS k r + ThreeDimData.AG k r) := by positivity
  have hbe : 2 * (ThreeDimData.AS k r + ThreeDimData.AG k r) ≤
      (ThreeDimData.aOf r h - ThreeDimData.AG k r - 5 / 2) / ((5 * (r + 1) ^ 2 : ℕ) : ℝ) := by
    rw [le_div_iff₀ hepos, he]; nlinarith
  refine ⟨ThreeDimData.aOf r h - ThreeDimData.AG k r - 5 / 2, by nlinarith, by linarith, ?_⟩
  rcases Nat.eq_zero_or_pos r with hr | hr
  · subst hr
    have hAG' : ThreeDimData.AG k 0 = 4 * (k : ℝ) := by rw [hAG]; push_cast; ring
    refine core L hk hκ hγ hpos hmono hR hQ le_rfl
      (fun a ha => intN_zero (P.nilpotent_measure_is_haar k 0) ha) (by linarith) ?_
    push_cast; nlinarith
  · have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr
    have hAB : B.AB k r = ThreeDimData.AG k r / 2 + 1 := by unfold B.AB; rw [hAG]; ring
    have hA2 : 2 ≤ ThreeDimData.AS k r := by
      rw [hAS]
      have h3 : (3 : ℝ) ≤ ((2 * r + k : ℕ) : ℝ) := by push_cast; linarith
      have h5 : (5 : ℝ) ≤ 2 * (r : ℝ) ^ 2 + 2 * r * k + r := by nlinarith
      nlinarith
    have hGR : 4 * ((r : ℝ) + 1) ^ 2 ≤ ThreeDimData.AG k r := by rw [hAG]; nlinarith
    refine core L hk hκ hγ hpos hmono hR hQ (bN := B.AB k r) (by rw [hAB]; linarith)
      (fun a ha => P.SliceLastLevel.intN k r _ (P.nilpotent_measure_is_haar k r) a ha) (by rw [hAB]; linarith) ?_
    rw [hAB]; nlinarith

end GlobalTheory.CellMaj

end
