import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
import Formalism.LocalRingCardinality.DataParamsT
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
import Development.AbelianVarietyTheory.Definitions.Divisors.WellChosen
import Development.AbelianVarietyTheory.Definitions.Divisors.MeanLogLeOfBounds
import Development.AbelianVarietyTheory.Definitions.Divisors.WedgeNrmLeOfWedgeNormLe
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomWeightHomWeight
import Development.AbelianVarietyTheory.Definitions.Divisors.MemLevEigenIffTransl
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LogMeanShares.LogMeanStatements.HSClaim
import Development.AbelianVarietyTheory.Definitions.Divisors.GenRatios
import Development.AbelianVarietyTheory.Definitions.Divisors.BadElt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolSub0LeSpanRaw
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.AdaptedStandardBasis
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ExistsIsNabUncond
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThFamMono
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolynomialCoefficientEmbeddingNormLeOfL1Bound
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormPhiHatIndPhi
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmallScalarReflexIdealSelfDualLatticeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBoundedIntegerGoodCoverThetaSeriesIntegralStatement
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CovGmin

theorem petW_le_of_homN_le : ∀ (D : D7) (T : Core D) (j : ℕ) (Y : Deep T j) (G : WTZ D.host.E) (σ : Y.d.c₂.F →+* ℂ) (f : Rul Y.d.Xo₂ Y.d.c₂) (B : ℝ), 0 ≤ B → (∀ z : Σ k, ReciprocityTheory.ChartRestriction.G.FD.Frame ((Y.U (Formalism.L2.Pj.goodOf Y.d.c₂ σ)).X k).Ψ D.R.r, z.2 ∈ ((Y.U (Formalism.L2.Pj.goodOf Y.d.c₂ σ)).X z.1).dom → AllWt.homN (Y.U (Formalism.L2.Pj.goodOf Y.d.c₂ σ)) (xiR D) G f z ≤ B) → AllWt.petW Y.U (xiR D) (fun _ => D.sp.W j) Y.dict G σ f ≤ B ∧ ∀ Z, petOn Y.U (xiR D) (fun _ => D.sp.W j) Y.dict Z G σ f ≤ B := by
  intro D T j Y G σ f B hB h
  have key : ∀ μ : MeasureTheory.Measure (AutQ (D.sp.W j)), μ Set.univ ≤ 1 →
      AllWt.petAt (Y.U (Formalism.L2.Pj.goodOf Y.d.c₂ σ)) (xiR D) (D.sp.W j) (Y.dict (Formalism.L2.Pj.goodOf Y.d.c₂ σ)) μ G f ≤ B := by
    intro μ hμ
    rw [AllWt.petAt_eq]
    have hb : ∀ q : AutQ (D.sp.W j), ‖AllWt.homN (Y.U (Formalism.L2.Pj.goodOf Y.d.c₂ σ)) (xiR D) G f
        (Y.dict (Formalism.L2.Pj.goodOf Y.d.c₂ σ) q.out)‖ₑ ≤ ENNReal.ofReal B := by
      intro q
      rw [Real.enorm_eq_ofReal (AllWt.homN_nonneg _ _ _ _ _)]
      apply ENNReal.ofReal_le_ofReal
      by_cases hz : (Y.dict (Formalism.L2.Pj.goodOf Y.d.c₂ σ) q.out).2 ∈
          ((Y.U (Formalism.L2.Pj.goodOf Y.d.c₂ σ)).X (Y.dict (Formalism.L2.Pj.goodOf Y.d.c₂ σ) q.out).1).dom
      · exact h _ hz
      · have h0 : AllWt.homN (Y.U (Formalism.L2.Pj.goodOf Y.d.c₂ σ)) (xiR D) G f
            (Y.dict (Formalism.L2.Pj.goodOf Y.d.c₂ σ) q.out) = 0 := by
          simp [AllWt.homN, AllWt.ptN, rdU, hz, ReciprocityTheory.ChartRestriction.G.FD.Data.pnorm]
        rw [h0]; exact hB
    have h1 := MeasureTheory.eLpNorm_le_of_ae_enorm_bound (p := 2) (μ := μ) (Filter.Eventually.of_forall hb)
    have h2 : MeasureTheory.eLpNorm (fun q : AutQ (D.sp.W j) => AllWt.homN (Y.U (Formalism.L2.Pj.goodOf Y.d.c₂ σ)) (xiR D) G f
        (Y.dict (Formalism.L2.Pj.goodOf Y.d.c₂ σ) q.out)) 2 μ ≤ ENNReal.ofReal B := by
      refine h1.trans ?_
      rw [smul_eq_mul]
      exact (mul_le_mul_right (ENNReal.rpow_le_one hμ (by positivity)) _).trans (by simp)
    exact ENNReal.toReal_le_of_le_ofReal hB h2
  refine ⟨key _ ?_, fun Z => key _ (AllWt.muPart_univ_le _ _ _)⟩
  rw [← AllWt.muPart_univ (D.sp.W j) (Y.dict (Formalism.L2.Pj.goodOf Y.d.c₂ σ))]
  exact AllWt.muPart_univ_le _ _ _

set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 200000 in

theorem nrm_le_of_eq_smul (D : D7) (T : Core D) (j : ℕ) (Y : Deep T j) (G : WTZ D.host.E) (σ : Y.d.c₂.F →+* ℂ)
    (w : Y.V G) (f : Rul Y.d.Xo₂ Y.d.c₂) (Na : ℕ) (A B : ℝ) (hB : 0 ≤ B) (hA : (Na : ℝ) ≤ A)
    (hc : (w : Rul Y.d.Xo₂ Y.d.c₂) = (Na : Y.d.c₂.F) • f)
    (h : ∀ z : Σ k, ReciprocityTheory.ChartRestriction.G.FD.Frame ((Y.U (Formalism.L2.Pj.goodOf Y.d.c₂ σ)).X k).Ψ D.R.r,
      z.2 ∈ ((Y.U (Formalism.L2.Pj.goodOf Y.d.c₂ σ)).X z.1).dom →
        AllWt.homN (Y.U (Formalism.L2.Pj.goodOf Y.d.c₂ σ)) (xiR D) G f z ≤ B) :
    Y.nrm G σ w ≤ A * B ∧
      ∀ Z, petOn Y.U (xiR D) (fun _ => D.sp.W j) Y.dict Z G σ (w : Rul Y.d.Xo₂ Y.d.c₂) ≤ A * B := by
  obtain ⟨h1, h2⟩ := petW_le_of_homN_le D T j Y G σ f B hB h
  have hn1 : ‖σ (Na : Y.d.c₂.F)‖ = Na := by rw [map_natCast, Complex.norm_natCast]
  have hN0 : (0 : ℝ) ≤ Na := Nat.cast_nonneg _
  refine ⟨?_, fun Z => ?_⟩
  · show AllWt.petW Y.U (xiR D) (fun _ => D.sp.W j) Y.dict G σ (w : Rul Y.d.Xo₂ Y.d.c₂) ≤ _
    rw [hc, AllWt.petW_smul, hn1]
    exact (mul_le_mul_of_nonneg_left h1 hN0).trans (mul_le_mul_of_nonneg_right hA hB)
  · rw [hc, AllWt.petOn_smul, hn1]
    exact (mul_le_mul_of_nonneg_left (h2 Z) hN0).trans (mul_le_mul_of_nonneg_right hA hB)

theorem span_eq_top_of_multiples {F M : Type*} [Field F] [CharZero F] [AddCommGroup M] [Module F M] (W : Submodule F M)
    (S S' : Set W) (hS : Submodule.span F S = ⊤) (Na : ℕ) (hNa : 0 < Na)
    (h : ∀ y ∈ S, ∃ s : F, s ≠ 0 ∧ ∀ y₁ : W, (y₁ : M) = s • (y : M) →
      ((Na • y₁ : W) : M) = (Na : F) • (s • (y : M)) → Na • y₁ ∈ S') :
    Submodule.span F S' = ⊤ := by
  rw [eq_top_iff, ← hS, Submodule.span_le]
  intro y hy
  obtain ⟨s, hs, hm⟩ := h y hy
  have hm' := hm (s • y) rfl (by rw [Nat.cast_smul_eq_nsmul]; rfl)
  have hNa' : ((Na : F)) ≠ 0 := by exact_mod_cast hNa.ne'
  have e1 : y = (s⁻¹ * (Na : F)⁻¹) • (Na • (s • y)) := by
    rw [← Nat.cast_smul_eq_nsmul F, smul_smul, smul_smul, mul_assoc s⁻¹, inv_mul_cancel₀ hNa', mul_one,
      inv_mul_cancel₀ hs, one_smul]
  rw [SetLike.mem_coe, e1]
  exact Submodule.smul_mem _ _ (Submodule.subset_span hm')

theorem exp_consts (CA CB CC Q κ : ℝ) :
    Real.exp (CC * Q * κ) * (Real.exp (391 * Q * κ) * Real.exp (CA * Q * κ) * Real.exp (CB * Q * κ)) =
      Real.exp ((CA + CB + CC + 391) * Q * κ) := by
  simp only [← Real.exp_add]
  congr 1
  ring

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem gmin_good_cover : Hypotheses2 → ∃ C : ℝ, 0 ≤ C ∧ ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j : ℕ, 1 ≤ (T.Q.Dw j).p → 1 ≤ (T.Q.Dw j).q → 2 < Module.finrank ℚ D.host.E / 2 → InR D j → ∀ (Y : Deep T.toCore j) (e : ℕ) (o : ℝ), Y.Good e o → ∀ Lb : ℝ, 1 ≤ Lb → Real.log Y.d.l₂.M ≤ 30 * Lb → fieldSz D.host.E ≤ 3 * Lb → Real.log (D.R.f * D.R.r) ≤ Lb → o ≤ 391 * (D.R.f * D.R.r * Lb) ^ 2 → ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n → Even n → 8 * D.R.f * D.R.r + 4 ≤ n → (∀ (τ : Psi T.Q.H) (k : Fin ((T.Q.Dw j).p + (T.Q.Dw j).q)), (k : ℕ) < (T.Q.Dw j).p → ((n / 2 : ℕ) : ℤ) < laOf (T.Q.Dw j) a n τ k) → Real.log (sizeK (T.Q.Dw j) a n) ≤ 20 * Lb → ∃ s : Set (Y.V (wtZ a n)), s ⊆ (AllWt.latW Y.U (wtZ a n) : Set (Y.V (wtZ a n))) ∧ Submodule.span Y.d.c₂.F s = ⊤ ∧ ∀ y ∈ s, ∀ σ, Y.nrm (wtZ a n) σ y ≤ Real.exp (C * ((D.R.f : ℝ) * D.R.r * Lb) ^ 2 * sizeK (T.Q.Dw j) a n) ∧ ∀ Z, petOn Y.U (xiR D) (fun _ => D.sp.W j) Y.dict Z (wtZ a n) σ y ≤ Real.exp (C * ((D.R.f : ℝ) * D.R.r * Lb) ^ 2 * sizeK (T.Q.Dw j) a n) := by
  intro _
  obtain ⟨CA, hCA0, hA⟩ := GlobalTheory.CovGmin.span_thFam
  obtain ⟨CB, hCB0, hB⟩ := GlobalTheory.RawThetaSup.homN_smul_raw_le
  obtain ⟨CC, hCC0, hC⟩ := GlobalTheory.T.exists_bounded_integer_goodCover_thetaSeries_integral
  refine ⟨CA + CB + CC + 391, by linarith only [hCA0, hCB0, hCC0], ?_⟩
  intro D T hJ j hp hq hf hj Y e o hG Lb hL hM hE hfr ho a n hDom hev hn hpos hsz
  have hH : GlobalTheory.CovGmin.Hyp D T j Y e o Lb a n :=
    ⟨hJ, hp, hq, hf, hj, hG, hL, hM, hE, hfr, ho, hDom, hev, hn, hpos, hsz⟩
  obtain ⟨_, nab, hnab⟩ := GlobalTheory.CanonConn.exists_isNab_uncond D.host.E T.Q.H (T.Q.Dw j) Y.d.l₂ Y.d.Xo₂ Y.d.c₂
  obtain ⟨Na, hNa, hlog, hint⟩ := hC D T j Y e o Lb a n hH nab hnab
  have hspan := hA D T j Y e o Lb a n hH nab hnab
  have hB' := hB D T j Y e o Lb a n hH nab hnab
  clear hA hB hC
  have hκ : 1 ≤ sizeK (T.Q.Dw j) a n := by
    have h1 := GlobalTheory.RawThetaSup.two_mul_card_psi T.Q.H
    have h2 : 1 ≤ n / 2 * (Fintype.card (Psi T.Q.H) * ((T.Q.Dw j).p + (T.Q.Dw j).q)) :=
      Nat.mul_pos (by omega) (Nat.mul_pos (by omega) (by omega))
    have h3 : (1 : ℝ) ≤ ((n / 2 : ℕ) : ℝ) * (Fintype.card (Psi T.Q.H) * ((T.Q.Dw j).p + (T.Q.Dw j).q) : ℕ) := by
      exact_mod_cast h2
    rw [GlobalTheory.RawThetaSup.sizeK_eq]
    exact h3.trans (le_add_of_nonneg_left (Nat.cast_nonneg _))
  have hNaE : (Na : ℝ) ≤ Real.exp (CC * ((D.R.f : ℝ) * D.R.r * Lb) ^ 2 * sizeK (T.Q.Dw j) a n) :=
    (Real.log_le_iff_le_exp (Nat.cast_pos.2 hNa)).1 hlog
  have hFE : Real.exp (fieldSz Y.d.c₂.F) ≤ Real.exp (391 * ((D.R.f : ℝ) * D.R.r * Lb) ^ 2 * sizeK (T.Q.Dw j) a n) :=
    Real.exp_le_exp.2 ((hG.size.trans ho).trans
      (le_mul_of_one_le_right (mul_nonneg (by norm_num) (sq_nonneg _)) hκ))
  refine ⟨{w | w ∈ (AllWt.latW Y.U (wtZ a n) : Set (Y.V (wtZ a n))) ∧ ∀ σ, Y.nrm (wtZ a n) σ w ≤ Real.exp ((CA + CB + CC + 391) * ((D.R.f : ℝ) * D.R.r * Lb) ^ 2 * sizeK (T.Q.Dw j) a n) ∧ ∀ Z, petOn Y.U (xiR D) (fun _ => D.sp.W j) Y.dict Z (wtZ a n) σ w ≤ Real.exp ((CA + CB + CC + 391) * ((D.R.f : ℝ) * D.R.r * Lb) ^ 2 * sizeK (T.Q.Dw j) a n)}, fun _ h => h.1, ?_, fun _ h => h.2⟩
  refine span_eq_top_of_multiples (Y.V (wtZ a n)) _ _ hspan Na hNa ?_
  rintro y ⟨x0, La, N, P, -, hU, hTb, hTM, hO, hP, hρ, hy⟩
  obtain ⟨s, hs0, hs1, hs2⟩ := GlobalTheory.T.exists_small_scalar_reflexIdeal_selfDualLattice D.host.E T.Q.H (T.Q.Dw j) Y.d.l₂ Y.d.c₂ n La hU
  refine ⟨s, hs0, fun y₁ hy₁ hc => ⟨hint x0 La N P hU hTb hTM hO hP y hy s hs1 y₁ hy₁, fun σ => ?_⟩⟩
  have hsup := hB' _ x0 La N P hU hTM hO hP hρ y hy s _ (Real.exp_pos _).le
    (fun σ => (hs2 σ).trans (pow_le_pow_left₀ (Real.exp_pos _).le hFE 2)) σ
  have hfin := nrm_le_of_eq_smul D T.toCore j Y (wtZ a n) σ _ _ Na _ _
    (mul_nonneg (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le) (Real.exp_pos _).le) hNaE hc hsup
  rw [exp_consts] at hfin
  exact hfin

end GlobalTheory.CovGmin
