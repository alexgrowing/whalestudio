import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsArchOne
import Development.AbelianVarietyTheory.BlockTheory.PoincareCuspForms.SmallUnipotentElements
import Development.AbelianVarietyTheory.Definitions.UpperBounds.FreeBallIffOfDimXEqZero
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.SumRangeBlocks
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.ContDiffAtLogMinorProd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBlockDetGe
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.ExistsPhlaBound
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.ExistsMixedProj
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.FirstMinimumInvariantContinuousPosOnFrames
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.DivisionWithBasisOfDivision
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.KaFrameOfDelta
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.OneLeMinorOfIsOrth
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.MulSgnMatMulConjTranspose
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.CuspStatementPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.ArakelovInstances.PointwiseNormInvarianceHolds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.KronHolPsiStatementHolds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.MeasInvStatementPf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniformBoundLintegralFlagDomainBallCaseStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrbitSumExpPotentialUniformBoundStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PoinConvBdd

open NumberField Module ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds GlobalTheory.ShareOn

section
open ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory.Up.OrbitInterpSmall

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem sum_bound {r : ℕ} (X : Data E r) (x0 : Frame X.Ψ r) (h0 : IsOrth X x0) (hPD : PropDisc X)
    (hp0 : 0 < X.p0) (hp1 : X.p0 < r) (hq : X.p0 * (r - X.p0) ≤ 3) {s : ℝ} (hs : 2 * ((r : ℝ) - 1) ≤ s) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ x, IsOrth X x →
      ∑' γ : X.Γ, ENNReal.ofReal (Real.exp (-(s * GlobalTheory.Up.rhX X x0 (lact γ.1 x)))) ≤ C := by
  have hr : (2 : ℝ) ≤ r := by exact_mod_cast (show 2 ≤ r by omega)
  exact GlobalTheory.T.orbitSum_exp_potential_uniform_bound E r X x0 h0 hPD s (by linarith) (GlobalTheory.T.exists_uniform_bound_lintegral_flagDomain_ball_case E r X hp0 hp1 hq s hs)

theorem kappa_exists {r : ℕ} (X : Data E r) (x0 : Frame X.Ψ r) (h0 : IsOrth X x0) (hPD : PropDisc X)
    (hp0 : 0 < X.p0) (hp1 : X.p0 < r) (hq : X.p0 * (r - X.p0) ≤ 3) {bb : ℝ}
    (hbb : 4 * ((r : ℝ) - 1) ≤ bb) (hb0 : 0 < bb) :
    ∃ κ : Frame X.Ψ r → ℝ, Measurable κ ∧ (∀ x ∈ X.dom, 0 < κ x ∧ κ x ≤ 1) ∧
      (∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, κ (rmul x b) = κ x) ∧
      (∀ z ∈ OmF X x0, κ (cpt X x0 z) = kaF X x0 bb z) ∧
      (∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ x ∈ X.dom,
        ∑' γ : X.Γ, ENNReal.ofReal (Real.sqrt (κ (lact γ.1 x))) ≤ C) ∧
      ∃ ρ C : ℝ, 0 < ρ ∧ ∀ x, IsOrth X x → ∀ z : V (nd X), ‖z‖ < ρ → κ (cpt X x z) ≤ C * κ x := by
  obtain ⟨hm, hpos, hinv, hch⟩ := GlobalTheory.FramePotential.frame_potential_basic r X x0 h0
  obtain ⟨C, hC, hS⟩ := sum_bound X x0 h0 hPD hp0 hp1 hq (s := bb / 2) (by linarith)
  refine GlobalTheory.kaFrame_of_delta X x0 bb hb0 _ (fun x => Finset.prod_nonneg fun τ _ => by positivity)
    hm hpos hinv hch (GlobalTheory.MinorRatioNear.minorRatio_near r X x0 h0) ⟨C, hC, fun x hx => ?_⟩
  refine le_trans (le_of_eq (tsum_congr fun γ => ?_)) (hS x hx)
  have hy : lact γ.1 x ∈ X.dom := MajInv.lact_mem_dom X (X.Γ_stab γ.1 γ.2) (IW.orth_mem_dom X x hx)
  congr 1
  rw [← GlobalTheory.Up.exp_neg_rhX h0 hy, ← Real.exp_mul]
  congr 1; ring

open GlobalTheory.Up.OrbitInterpolation in

theorem orbitInterp_small {r : ℕ} (X : Data E r) (G : Subgroup (GL (Fin r) E)) (x0 : Frame X.Ψ r)
    (la : Wt X.Ψ r) (ρ0 bb m : ℝ) (hPD : PropDisc X) (h0 : IsOrth X x0) (hd : 1 ≤ dimX X)
    (hp0 : 0 < X.p0) (hp1 : X.p0 < r) (hq : X.p0 * (r - X.p0) ≤ 3) (hρ0 : 0 < ρ0)
    (hG : FreeBall X G x0 ρ0) (hla : BlockConst X la)
    (hbb : 4 * ((r : ℝ) - 1) ≤ bb) (hb0 : 0 < bb) (hm : bb + dimX X / ρ0 < m)
    (hcurv : ∀ z ∈ OmF X x0, ∀ ξ : Fin (nd X) → ℂ,
      m * leviRh X x0 z ξ ≤ leviO X x0 (phla X la) z ξ - leviDens X x0 z ξ)
    (hSS : ∀ P, X.IsBddSec la P → P ∈ X.SS la) :
    ∃ u0 ∈ X.SS la, u0 x0 ≠ 0 ∧ ∀ γ ∈ G, γ ∉ X.Γ → u0 (lact γ x0) = 0 := by
  classical
  have hN : NfacRmulStatement (E := E) ∧ NfacLactStatement (E := E) ∧ PnormInvStatement (E := E) :=
    ⟨normFactor_rightBorel_holds, normFactor_leftAction_holds, pointwiseNorm_invariance_holds⟩
  have hbb0 : 0 ≤ bb := hb0.le
  obtain ⟨κ, hκm, hκ1, hκB, hκF, ⟨Cs, hCs, hsum⟩, hloc⟩ := kappa_exists X x0 h0 hPD hp0 hp1 hq hbb hb0
  have hsumE := sum_bound X x0 h0 hPD hp0 hp1 hq (s := bb / 2) (by linarith)
  obtain ⟨-, hW, hWl⟩ := KronMetric.kronMetric hN r X la (fun _ => 0) (fun _ _ _ _ _ _ => rfl)
    (fun _ _ => contDiffOn_const) ⟨0, fun _ _ => le_rfl⟩
  obtain ⟨⟨hz, hadd, hsmul⟩, -⟩ := siegelSpaceAlgebra_holds r X la la 0
  let S : Submodule ℂ (Frame X.Ψ r → ℂ) :=
    { carrier := X.SS la
      add_mem' := fun {P Q} hP hQ => hadd P hP Q hQ
      zero_mem' := hz
      smul_mem' := fun a P hP => hsmul a P hP }
  obtain ⟨T, hT⟩ := X.Γ_index
  have hx0 := IW.orth_mem_dom X x0 h0
  obtain ⟨u, hu, hu1, hu0⟩ := exists_of_approx S x0
    (fun s : {s : T // s.1⁻¹ ∈ G ∧ s.1⁻¹ ∉ X.Γ} => lact s.1.1⁻¹ x0) fun η hη => by
    have hη' : 0 < η / (Cs.toReal + 1) := by positivity
    obtain ⟨F, P, hF, hIn, hP, hPF, hP1, hP0⟩ := exists_approx hN extFStatement_holds measInv_holds
      GlobalTheory.PoleExistence.poleEx_holds (GlobalTheory.PoleDbar.poleSolve measInv_holds)
      GlobalTheory.Up.polePoint_holds h0 hd hρ0 hG hla hbb0 hm hcurv hκm hκ1 hκB hκF hloc hη'
    obtain ⟨hs, hbd⟩ := GlobalTheory.PoinSumBound.poin_conv_bdd E r X x0 h0 hPD la _ bb hW hWl hb0 hsumE F P hF hIn hP hPF
    have hn : ∀ (γ : X.Γ) (y : Frame X.Ψ r), ‖(X.χ la γ.1)⁻¹ * P (lact γ.1 y)‖ = ‖P (lact γ.1 y)‖ :=
      fun γ y => by rw [norm_mul, norm_inv, OntoE.chi_norm X la γ.2, inv_one, one_mul]
    have he : η / (Cs.toReal + 1) + η / (Cs.toReal + 1) * Cs.toReal = η := by field_simp; ring
    refine ⟨poin X la P, hSS _ hbd, ?_, fun s => ?_⟩
    · have hs0 := hs x0 hx0
      unfold poin
      rw [hs0.of_norm.tsum_eq_add_tsum_ite 1]
      simp only [OneMemClass.coe_one, chi_one, FundSetPf.lact_one, inv_one, one_mul]
      have hle : ∀ γ : X.Γ, ‖if γ = 1 then 0 else (X.χ la γ.1)⁻¹ * P (lact γ.1 x0)‖ ≤
          ‖(X.χ la γ.1)⁻¹ * P (lact γ.1 x0)‖ := fun γ => by
        split_ifs
        · rw [norm_zero]; exact norm_nonneg _
        · exact le_rfl
      have hs1 := Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hle hs0
      have h2 := (norm_tsum_le_tsum_norm hs1).trans (tsum_le_of_le hs1 (fun _ => norm_nonneg _) hη'.le
        (fun γ => by
          split_ifs with h
          · rw [norm_zero]; positivity
          · rw [hn]
            exact hP0 γ.1 (hG.1 γ.2) fun h' => h (Subtype.ext h')) hCs (hsum x0 hx0))
      rw [add_sub_right_comm, ← he]
      exact (norm_add_le _ _).trans (add_le_add hP1 h2)
    · have hy := MajInv.lact_mem_dom X (hG.isUStab s.2.1) hx0
      have h2 := (norm_tsum_le_tsum_norm (hs _ hy)).trans (tsum_le_of_le (hs _ hy)
        (fun _ => norm_nonneg _) hη'.le
        (fun γ => by
          rw [hn, ← FundSetPf.lact_mul]
          refine hP0 _ (G.mul_mem (hG.1 γ.2) s.2.1) fun h => s.2.2 ?_
          rw [eq_inv_of_mul_eq_one_right h]
          exact X.Γ.inv_mem γ.2) hCs (hsum _ hy))
      exact h2.trans (by linarith)
  refine ⟨u, hu, by rw [hu1]; exact one_ne_zero, fun γ hγ hγ' => ?_⟩
  obtain ⟨s, hsT, hs⟩ := hT γ⁻¹ (hG.isUStab (G.inv_mem hγ))
  have e : s⁻¹ = (s⁻¹ * γ⁻¹) * γ := by group
  have e' : γ = (s⁻¹ * γ⁻¹)⁻¹ * s⁻¹ := by group
  have h1 : s⁻¹ ∈ G := by rw [e]; exact G.mul_mem (hG.1 hs) hγ
  have h2 : s⁻¹ ∉ X.Γ := fun h => hγ' (by rw [e']; exact X.Γ.mul_mem (X.Γ.inv_mem hs) h)
  have h3 : u (lact s⁻¹ x0) = 0 := hu0 ⟨⟨s, hsT⟩, h1, h2⟩
  have hu' : u ∈ X.SS la := hu
  rw [e', FundSetPf.lact_mul, hu'.1.1.2.2 _ (X.Γ.inv_mem hs) _
    (MajInv.lact_mem_dom X (hG.isUStab h1) hx0), h3, mul_zero]

end GlobalTheory.Up.OrbitInterpSmall
end

namespace GlobalTheory.Up.OrbitInterpSmall

theorem gapsPairing_deMul' {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
    (h0 : 0 < X.p0) (h1 : X.p0 < r) {s : ℕ} (hs : Even s) :
    GlobalTheory.IndefiniteRowSideFullHecke.SpanSubtraction.GapsPairing X (deMul X.Ψ r X.p0 s - kapW X) ((s : ℝ) - 2 * r + 2) := by
  obtain ⟨k, rfl⟩ := hs
  have hk : (k + k) / 2 = k := by omega
  intro τ
  refine ⟨fun i j hj hp => ?_, fun i0 i1 h0' h1' => ?_⟩
  · have e : ((j : ℕ) < X.p0 ↔ (i : ℕ) < X.p0) := by omega
    have hj' : ((j : ℕ) : ℤ) = (i : ℕ) + 1 := by exact_mod_cast hj
    simp only [Pi.sub_apply, deMul, kapW, hj']
    by_cases hi : (i : ℕ) < X.p0
    · rw [if_pos (e.2 hi), if_pos hi]; omega
    · rw [if_neg (mt e.1 hi), if_neg hi]; omega
  · simp only [Pi.sub_apply, deMul, kapW, h0', h1', hk]
    rw [if_pos h0, if_neg (by omega)]
    have hr : ((r - 1 : ℕ) : ℤ) = (r : ℤ) - 1 := by omega
    rw [hr]
    push_cast
    linarith

theorem orbit_interp_small : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r),
    (∀ la, ∀ γ ∈ X.Γ, X.χ la γ = 1) → ∀ (G : Subgroup (GL (Fin r) E)) (x0 : Frame X.Ψ r), IsOrth X x0 →
    GlobalTheory.Up.FreeBall X G x0 (1 / (49 * (r : ℝ) ^ 2)) → 0 < X.p0 → X.p0 < r → X.p0 * (r - X.p0) ≤ 3 →
    ∀ s : ℕ, Even s → 2 * r + 50 * r ^ 2 * (X.Ψ.card * (X.p0 * (r - X.p0))) + 1 ≤ s →
    ∃ P ∈ X.SS (deMul X.Ψ r X.p0 s), P x0 ≠ 0 ∧ ∀ γ ∈ G, γ ∉ X.Γ → P (lact γ x0) = 0 := by
  intro E _ _ _ r X _ G x0 hx0 hFB h0 h1 hq s hs hsb
  have hd : 1 ≤ GlobalTheory.Up.dimX X := (GlobalTheory.Up.one_le_dimX_iff X).2 ⟨h0, h1⟩
  have hD : GlobalTheory.Up.dimX X = X.Ψ.card * (X.p0 * (r - X.p0)) := rfl
  have hc : 0 < X.Ψ.card := by
    rcases Nat.eq_zero_or_pos X.Ψ.card with h | h
    · rw [hD, h, zero_mul] at hd; omega
    · exact h
  obtain ⟨τ, hτ⟩ := Finset.card_pos.1 hc
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast (h0.trans h1)
  have hρ : (0 : ℝ) < 1 / (49 * (r : ℝ) ^ 2) := by positivity
  have hdR : (1 : ℝ) ≤ GlobalTheory.Up.dimX X := by exact_mod_cast hd
  have hsR : 2 * (r : ℝ) + 50 * (r : ℝ) ^ 2 * (GlobalTheory.Up.dimX X : ℝ) + 1 ≤ s := by
    rw [hD]; exact_mod_cast hsb
  have hq1 : (GlobalTheory.Up.dimX X : ℝ) / (1 / (49 * (r : ℝ) ^ 2)) = 49 * (r : ℝ) ^ 2 * GlobalTheory.Up.dimX X := by
    field_simp
  have hcurv := (GlobalTheory.DivisionVolume.margin_iff h0 h1 (deMul X.Ψ r X.p0 s) ((s : ℝ) - 2 * r + 2)).2
    (gapsPairing_deMul' X h0 h1 hs) x0 hx0
  refine orbitInterp_small X G x0 _ _ (4 * ((r : ℝ) - 1) + 1 / 2) ((s : ℝ) - 2 * r + 2)
    (GlobalTheory.ClosedDiscontinuity.propDisc_closed r X) hx0 hd h0 h1 hq hρ hFB
    (fun _ _ _ h => if_congr h rfl rfl) (by linarith) (by linarith)
    (by rw [hq1]; nlinarith [mul_le_mul_of_nonneg_left hdR (sq_nonneg (r : ℝ)), sq_nonneg ((r : ℝ) - 2)])
    hcurv ?_
  refine cuspStatement_holds r X _ ⟨τ, hτ⟩ h0 h1 (fun i j hj hp => ?_) (fun i0 i1 h0' h1' => ?_)
  · have e : ((j : ℕ) < X.p0 ↔ (i : ℕ) < X.p0) := by omega
    simp only [deMul]
    by_cases hi : (i : ℕ) < X.p0
    · rw [if_pos (e.2 hi), if_pos hi]
    · rw [if_neg (mt e.1 hi), if_neg hi]
  · simp only [deMul]
    rw [if_pos (by omega), if_neg (by omega)]
    omega

end GlobalTheory.Up.OrbitInterpSmall
