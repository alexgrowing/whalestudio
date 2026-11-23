import Formalism.HermitianCurvature.HermitianCurvatureProofs.GaXiSplit
import Formalism.HermitianCurvature.HermitianCurvatureProofs.JfBetaAdjCOfLemmaBNorm
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CoordinateSizesOfHypotheses
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PhiBoundPartsOfRadicalParametrisation
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OpApplyZeroNear
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RegularisedPairingViaPhase

open Matrix MeasureTheory Filter Topology
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.LeftFubiniLemmas

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

section bump

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k ρ : ℕ}

def sqN (y : B.Mat k ρ) : ℝ := ∑ i, ∑ j, ‖y i j‖ ^ 2

theorem sqN_eq (y : B.Mat k ρ) : sqN y = B.gN y ^ 2 := by
  have h0 : 0 ≤ ∑ i, ∑ j, Complex.normSq (y i j) :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => Complex.normSq_nonneg _
  have h1 := Real.sq_sqrt h0
  have h2 : B.gN y = Real.sqrt (∑ i, ∑ j, Complex.normSq (y i j)) := rfl
  rw [h2, h1]
  unfold sqN
  simp only [Complex.normSq_eq_norm_sq]

theorem contDiff_sqN : ContDiff ℝ ∞ (sqN (k := k) (ρ := ρ)) := by
  unfold sqN
  refine ContDiff.sum fun i _ => ContDiff.sum fun j _ => ?_
  have hl : ContDiff ℝ ∞ (fun y : B.Mat k ρ => y i j) := contDiff_apply_apply ℝ ℂ i j
  exact (contDiff_norm_sq ℝ).comp hl

def bumpG (R : ℝ) (y : B.Mat k ρ) : ℝ := Real.smoothTransition (R ^ 2 + 1 - sqN y)

theorem contDiff_bumpG (R : ℝ) : ContDiff ℝ ∞ (bumpG (k := k) (ρ := ρ) R) :=
  Real.smoothTransition.contDiff.comp (contDiff_const.sub contDiff_sqN)

theorem bumpG_nonneg (R : ℝ) (y : B.Mat k ρ) : 0 ≤ bumpG R y := Real.smoothTransition.nonneg _

theorem bumpG_le_one (R : ℝ) (y : B.Mat k ρ) : bumpG R y ≤ 1 := Real.smoothTransition.le_one _

theorem bumpG_eq_one {R : ℝ} {y : B.Mat k ρ} (hy : B.gN y ≤ R) : bumpG R y = 1 := by
  unfold bumpG
  apply Real.smoothTransition.one_of_one_le
  have h0 : 0 ≤ B.gN y := Real.sqrt_nonneg _
  have : B.gN y ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ h0 hy 2
  rw [sqN_eq]; linarith

theorem bumpG_supp (R : ℝ) {y : B.Mat k ρ} (hy : bumpG R y ≠ 0) : B.gN y ≤ Real.sqrt (R ^ 2 + 1) := by
  unfold bumpG at hy
  have h : 0 < R ^ 2 + 1 - sqN y := by
    by_contra hc
    exact hy (Real.smoothTransition.zero_of_nonpos (not_lt.mp hc))
  rw [sqN_eq] at h
  rw [show B.gN y = Real.sqrt (B.gN y ^ 2) from (Real.sqrt_sq (Real.sqrt_nonneg _)).symm]
  exact Real.sqrt_le_sqrt (by linarith)

end bump

section triv

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k ρ : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

def trivSet (Bj : B.RealPlaceData k ρ Wp Wq) : B.RealPlaceData k ρ ℂ ℂ where
  z := Bj.z
  z' := Bj.z'
  π := fun _ => 1
  π' := fun _ => 1
  μG := Bj.μG
  μW := Bj.μW
  μN := Bj.μN
  μW' := Bj.μW'
  μsec := Bj.μsec
  χ := Bj.χ
  k_pos := Bj.k_pos
  z_mem := Bj.z_mem
  z'_mem := Bj.z'_mem
  T_pos := Bj.T_pos
  T'_pos := Bj.T'_pos
  π_rep := ⟨rfl, fun _ _ _ _ => by ext; simp⟩
  π'_rep := ⟨rfl, fun _ _ _ _ => by ext; simp⟩
  π_unitary := fun _ _ v => by simp
  π'_unitary := fun _ _ v => by simp
  π_cont := continuousOn_const
  π'_cont := continuousOn_const
  haarG := Bj.haarG
  haarW := Bj.haarW
  haarN := Bj.haarN
  haarW' := Bj.haarW'
  sec := Bj.sec
  χ_smooth := Bj.χ_smooth
  χ_supp := Bj.χ_supp
  χ_int := Bj.χ_int

theorem norm_psi (z : Fin (2 * ρ + k + 1) → ℂ) (c : ℂ) (g : B.Mat k ρ) : ‖psi k ρ z c g‖ = 1 := by
  unfold psi
  rw [mul_comm]
  exact Complex.norm_exp_ofReal_mul_I _

theorem norm_xiP (Bs : B.RealPlaceData k ρ Wp Wq) (P : B.SS k ρ) : ‖JF.xiP Bs P‖ = 1 := by
  unfold JF.xiP
  rw [norm_mul, norm_star, norm_psi, norm_psi, one_mul]

theorem bump_int (Bj : B.RealPlaceData k ρ Wp Wq) {g : B.Mat k ρ} (hg : g ∈ JF.Om k ρ Bj.z Bj.z') (R : ℝ) :
    Integrable (fun P : B.SS k ρ => bumpG R (B.sgs P g)) Bj.μSS := by
  set F : B.Mat k ρ → (ℂ →L[ℂ] ℂ) := fun y => ((bumpG R y : ℝ) : ℂ) • (1 : ℂ →L[ℂ] ℂ) with hFdef
  have hFc : ContDiff ℝ ∞ F :=
    (Complex.ofRealCLM.contDiff.comp (contDiff_bumpG R)).smul contDiff_const
  have hCk : B.CkOn ⊤ (B.GV k ρ) F := fun g₀ _ =>
    ⟨Set.univ, F, isOpen_univ, Set.mem_univ _, hFc.contDiffOn, fun _ _ _ => rfl⟩
  set n : ℝ := ((2 * ρ + k + 1 : ℕ) : ℝ) with hn
  set A : ℝ := 9 * ((ρ : ℝ) + 1) * (n ^ 2 + 1) with hA
  have hthr : JF.TransportedAlt k ρ A 0 := by
    unfold JF.TransportedAlt
    have hpos : (0 : ℝ) < 9 * ((ρ : ℝ) + 1) := by positivity
    have e : (A - 6 * (ρ : ℝ) * ((0 : ℕ) : ℝ)) / (9 * ((ρ : ℝ) + 1)) = n ^ 2 + 1 := by
      rw [hA]; push_cast; field_simp; ring
    rw [← hn, e]; linarith
  have hcc : B.InCC A 0 F := Formalism.FourierDecayAlt.P.JFxG.cptInCC_G hCk (Formalism.FourierDecayAlt.P.PBE.isCompact_gN_le k ρ (Real.sqrt (R ^ 2 + 1)))
    (fun y _ hyC => by
      by_contra h0
      apply hyC
      refine bumpG_supp R (fun hb => h0 ?_)
      simp [hFdef, hb]) A 0
  have hInt := (Formalism.FourierDecayAlt.P.bessel_integral_converges k ρ ℂ ℂ (trivSet Bj) A F hthr hcc).1 g hg
  refine hInt.norm.congr (ae_of_all _ fun P => ?_)
  show ‖JF.xiP (trivSet Bj) P • B.rho (trivSet Bj) P F g‖ = bumpG R (B.sgs P g)
  rw [norm_smul, norm_xiP, one_mul]
  simp only [B.rho, trivSet, hFdef]
  rw [ContinuousLinearMap.one_def, ContinuousLinearMap.id_comp, ContinuousLinearMap.comp_id, norm_smul,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (bumpG_nonneg R _)]
  simp

end triv

section fmoc

variable {k p ρ : ℕ}

theorem fmoc_RC : MeasureTheory.IsFiniteMeasureOnCompacts (U.muRC k p ρ) := by
  have h1 : IsFiniteMeasureOnCompacts (volume : Measure (Fin (2 * ρ + k + 1) → Fin p → ℂ)) := inferInstance
  have h2 : IsFiniteMeasureOnCompacts (volume : Measure ((G.UT p → ℂ) × (Fin p → ℝ))) := inferInstance
  have h3 : SigmaFinite (volume : Measure ((G.UT p → ℂ) × (Fin p → ℝ))) := inferInstance
  unfold U.muRC
  rw [Measure.volume_eq_prod]
  exact Measure.prod.instIsFiniteMeasureOnCompacts _ _

theorem fmoc_Xi (σ : Equiv.Perm (Fin p)) : MeasureTheory.IsFiniteMeasureOnCompacts (U.muXi k p 0 ρ σ) := by
  have h1 : IsFiniteMeasureOnCompacts (U.muRC k p ρ) := fmoc_RC
  have h1' : SigmaFinite (U.muRC k p ρ) := Formalism.FourierDecayAlt.P.Dx2.SplitF.sf_RC p ρ
  have h2 : IsFiniteMeasureOnCompacts ((U.muRC k p ρ).prod (U.muRC k p ρ)) :=
    Measure.prod.instIsFiniteMeasureOnCompacts _ _
  have a1 : IsFiniteMeasureOnCompacts (volume : Measure (Fin 0 → Fin p → ℂ)) := inferInstance
  have a2 : IsFiniteMeasureOnCompacts (volume : Measure (Fin p → Fin 0 → ℂ)) := inferInstance
  have a2' : SigmaFinite (volume : Measure (Fin p → Fin 0 → ℂ)) := inferInstance
  have a3 : IsFiniteMeasureOnCompacts (volume : Measure (U.LW σ → ℂ)) := inferInstance
  have a4 : IsFiniteMeasureOnCompacts (volume : Measure (G.UT p → ℂ)) := inferInstance
  have a4' : SigmaFinite (volume : Measure (G.UT p → ℂ)) := inferInstance
  have b1 : IsFiniteMeasureOnCompacts (volume : Measure ((Fin 0 → Fin p → ℂ) × (Fin p → Fin 0 → ℂ))) := by
    rw [Measure.volume_eq_prod]; exact Measure.prod.instIsFiniteMeasureOnCompacts _ _
  have b2 : IsFiniteMeasureOnCompacts (volume : Measure ((U.LW σ → ℂ) × (G.UT p → ℂ))) := by
    rw [Measure.volume_eq_prod]; exact Measure.prod.instIsFiniteMeasureOnCompacts _ _
  have b2' : SigmaFinite (volume : Measure ((U.LW σ → ℂ) × (G.UT p → ℂ))) := by
    rw [Measure.volume_eq_prod]; infer_instance
  have b3 : IsFiniteMeasureOnCompacts (U.muXiH p 0 σ) := by
    unfold U.muXiH; rw [Measure.volume_eq_prod]; exact Measure.prod.instIsFiniteMeasureOnCompacts _ _
  have b3' : SigmaFinite (U.muXiH p 0 σ) := by
    unfold U.muXiH; rw [Measure.volume_eq_prod]; infer_instance
  unfold U.muXi
  exact Measure.prod.instIsFiniteMeasureOnCompacts _ _

end fmoc

section bound

variable {k p ρ : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem detM_zero (Z : G.Mat 0) : G.detM Z = 1 := by
  unfold G.detM
  exact Matrix.det_isEmpty

theorem slice_bound (hp : 1 ≤ p) (σ : Equiv.Perm (Fin p)) (d : Fin p → ℂ) (hd : ∀ i, d i ≠ 0)
    (H : B.Mat k (p + 0 + ρ) → E)
    (hHc : ContinuousOn H {x | x ∈ B.GV k (p + 0 + ρ) ∧ U.DjU k (p + 0) ρ x ≠ 0}) (R : ℝ)
    (hR : ∀ x ∈ B.GV k (p + 0 + ρ), H x ≠ 0 → B.gN x ≤ R) :
    ∃ M C R' : ℝ, 0 ≤ M ∧
      Integrable (fun ξ : U.Xi k p 0 ρ σ => M * (Metric.closedBall (0 : U.Xi k p 0 ρ σ) C).indicator (fun _ => (1 : ℝ)) ξ)
        (U.muXi k p 0 ρ σ) ∧ ∀ (ξ : U.Xi k p 0 ρ σ) (Z : G.Mat 0) (γ : B.Mat k ρ), γ ∈ B.GV k ρ →
      ‖H (U.gaXi k ρ σ d ξ Z γ)‖ ≤
        M * (Metric.closedBall (0 : U.Xi k p 0 ρ σ) C).indicator (fun _ => (1 : ℝ)) ξ * bumpG R' γ := by
  obtain ⟨C1, hC1⟩ := Formalism.FourierDecayAlt.P.block3_apply_embedding k (p + 0) ρ hp
  obtain ⟨C2, hC2⟩ := Formalism.FourierDecayAlt.P.aux_statement_17 p 0 σ d hd
  set δ0 : ℂ := (U.hMat σ d).det with hδ0
  have hδ0ne : δ0 ≠ 0 := Formalism.FourierDecayAlt.P.Ux10.det_hMat_ne σ d hd
  set m0 : ℝ := min 1 ‖δ0‖ with hm0
  have hm0pos : 0 < m0 := lt_min one_pos (norm_pos_iff.mpr hδ0ne)
  set K : Set (B.Mat k (p + 0 + ρ)) := B.GV k (p + 0 + ρ) ∩ {x | B.gN x ≤ R} ∩ {x | U.DjU k (p + 0) ρ x = δ0}
    with hKdef
  have hK : IsCompact K := by
    refine ((Formalism.FourierDecayAlt.P.PBE.isCompact_gN_le k (p + 0 + ρ) R).inter_left
      (Formalism.FourierDecayAlt.P.unitary_group_closed k (p + 0 + ρ)).closed).inter_right ?_
    exact isClosed_eq (Formalism.FourierDecayAlt.P.JCTx6.Pos.cont_DjU k (p + 0) ρ) continuous_const
  have hKsub : K ⊆ {x | x ∈ B.GV k (p + 0 + ρ) ∧ U.DjU k (p + 0) ρ x ≠ 0} := by
    rintro x ⟨⟨hx1, -⟩, hx3⟩
    exact ⟨hx1, by rw [Set.mem_setOf_eq.mp hx3]; exact hδ0ne⟩
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn (hHc.mono hKsub)
  set c1 : ℝ := max C1 0 with hc1
  set c2 : ℝ := max C2 0 with hc2
  have hc1n : 0 ≤ c1 := le_max_right _ _
  have hc2n : 0 ≤ c2 := le_max_right _ _
  set R0 : ℝ := max R 0 with hR0
  have hR0n : 0 ≤ R0 := le_max_right _ _
  set B1 : ℝ := c1 * R0 ^ (p + 0) / m0 with hB1
  set B2 : ℝ := c2 * (c1 * R0) ^ p with hB2
  refine ⟨max M 0, max B1 B2, c1 * R0 ^ (2 * (p + 0) + 1) / m0 ^ 2, le_max_right _ _, ?_, fun ξ Z γ hγ => ?_⟩
  · have : MeasureTheory.IsFiniteMeasureOnCompacts (U.muXi k p 0 ρ σ) := fmoc_Xi σ
    have : BorelSpace ((Fin 0 → Fin p → ℂ) × (Fin p → Fin 0 → ℂ)) := Prod.borelSpace
    have : BorelSpace ((U.LW σ → ℂ) × (G.UT p → ℂ)) := Prod.borelSpace
    have : BorelSpace (U.XiH p 0 σ) := Prod.borelSpace
    have : BorelSpace (U.RC k p ρ × U.RC k p ρ) := Prod.borelSpace
    have : BorelSpace (U.Xi k p 0 ρ σ) := Prod.borelSpace
    refine Integrable.const_mul ?_ _
    exact (integrableOn_const (measure_closedBall_lt_top).ne).integrable_indicator measurableSet_closedBall
  have hZ1 : G.detM Z = 1 := detM_zero Z
  by_cases h0 : H (U.gaXi k ρ σ d ξ Z γ) = 0
  · rw [h0, norm_zero]
    exact mul_nonneg (mul_nonneg (le_max_right _ _) (Set.indicator_nonneg (fun _ _ => zero_le_one) _))
      (bumpG_nonneg _ _)
  have hG := Formalism.FourierDecayAlt.P.Ux10.gaXi_mem Formalism.FourierDecayAlt.P.slice_membership Formalism.FourierDecayAlt.P.radical_parametrisation σ d hd ξ Z
    (by rw [hZ1]; exact one_ne_zero) hγ
  have hgR := hR _ hG h0
  have hgN0 : 0 ≤ B.gN (U.gaXi k ρ σ d ξ Z γ) := Real.sqrt_nonneg _
  have hgR0 : B.gN (U.gaXi k ρ σ d ξ Z γ) ≤ R0 := hgR.trans (le_max_left _ _)
  have hD : U.DjU k (p + 0) ρ (U.gaXi k ρ σ d ξ Z γ) = δ0 := by
    rw [Formalism.FourierDecayAlt.P.Ux10.DjU_gaXi Formalism.FourierDecayAlt.P.hat_z_on_slice, hZ1, mul_one]
  have hMb : ‖H (U.gaXi k ρ σ d ξ Z γ)‖ ≤ max M 0 := (hM _ ⟨⟨hG, hgR⟩, hD⟩).trans (le_max_left _ _)

  have hdetZ : (U.ZjH σ d ξ.2 Z).det ≠ 0 := by
    rw [Formalism.FourierDecayAlt.P.level_determinant_z, hZ1, mul_one]; exact hδ0ne
  have hdetZ' : ‖(U.ZjH σ d ξ.2 Z).det‖ = ‖δ0‖ := by
    rw [Formalism.FourierDecayAlt.P.level_determinant_z, hZ1, mul_one]
  obtain ⟨b1, b2, b3, -, b5⟩ := hC1 ξ.1.1 ξ.1.2 (U.ZjH σ d ξ.2 Z) γ hdetZ hγ
  have hgaXi : U.gaXi k ρ σ d ξ Z γ =
      (U.Rn k (p + 0) ρ ξ.1.1)⁻¹ * U.mMap k (p + 0) ρ (U.ZjH σ d ξ.2 Z) γ * U.Rn k (p + 0) ρ ξ.1.2 := rfl
  rw [← hgaXi, hdetZ', ← hm0] at b1 b2 b5
  rw [← hgaXi] at b3
  have hpow : ∀ n : ℕ, B.gN (U.gaXi k ρ σ d ξ Z γ) ^ n ≤ R0 ^ n := fun n => pow_le_pow_left₀ hgN0 hgR0 n
  have bx1 : ‖ξ.1.1‖ ≤ B1 := by
    refine (Formalism.FourierDecayAlt.P.Ux6.norm_le_gN_Rn ξ.1.1).trans (b1.trans ?_)
    rw [hB1]
    exact div_le_div_of_nonneg_right (mul_le_mul (le_max_left _ _) (hpow _) (pow_nonneg hgN0 _) hc1n) hm0pos.le
  have bx2 : ‖ξ.1.2‖ ≤ B1 := by
    refine (Formalism.FourierDecayAlt.P.Ux6.norm_le_gN_Rn ξ.1.2).trans (b2.trans ?_)
    rw [hB1]
    exact div_le_div_of_nonneg_right (mul_le_mul (le_max_left _ _) (hpow _) (pow_nonneg hgN0 _) hc1n) hm0pos.le
  have hmx : U.mx (U.ZjH σ d ξ.2 Z) ≤ c1 * R0 :=
    b3.trans (mul_le_mul (le_max_left _ _) hgR0 hgN0 hc1n)
  have hmx0 : 0 ≤ U.mx (U.ZjH σ d ξ.2 Z) := norm_nonneg _
  obtain ⟨e1, e2, e3, e4, -⟩ := hC2 ξ.2 Z
  have hη : ∀ t : ℝ, t ≤ C2 * U.mx (U.ZjH σ d ξ.2 Z) ^ p → t ≤ B2 := fun t ht =>
    ht.trans (mul_le_mul (le_max_left _ _) (pow_le_pow_left₀ hmx0 hmx p) (pow_nonneg hmx0 _) hc2n)
  have hξ : ‖ξ‖ ≤ max B1 B2 := by
    rw [norm_prod_le_iff]
    refine ⟨?_, ?_⟩
    · rw [norm_prod_le_iff]
      exact ⟨bx1.trans (le_max_left _ _), bx2.trans (le_max_left _ _)⟩
    · rw [norm_prod_le_iff, norm_prod_le_iff, norm_prod_le_iff]
      exact ⟨⟨(hη _ e1).trans (le_max_right _ _), (hη _ e2).trans (le_max_right _ _)⟩,
        ⟨(hη _ e3).trans (le_max_right _ _), (hη _ e4).trans (le_max_right _ _)⟩⟩
  have hind : (Metric.closedBall (0 : U.Xi k p 0 ρ σ) (max B1 B2)).indicator (fun _ => (1 : ℝ)) ξ = 1 := by
    rw [Set.indicator_of_mem (by rw [Metric.mem_closedBall, dist_zero_right]; exact hξ)]
  have hbump : bumpG (c1 * R0 ^ (2 * (p + 0) + 1) / m0 ^ 2) γ = 1 := by
    apply bumpG_eq_one
    refine b5.trans ?_
    exact div_le_div_of_nonneg_right (mul_le_mul (le_max_left _ _) (hpow _) (pow_nonneg hgN0 _) hc1n)
      (pow_nonneg hm0pos.le _)
  rw [hind, hbump, mul_one, mul_one]
  exact hMb

end bound

end Formalism.FourierDecayAlt.P.LeftFubiniLemmas
