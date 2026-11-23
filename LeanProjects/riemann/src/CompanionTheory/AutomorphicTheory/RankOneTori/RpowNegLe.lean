import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CompactCellConvergence.CellConvergence
import Formalism.SharpRestriction.CuspSpanNormBounds.SLemOm
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryQuotientCompactness.UnipotentRadicalContracting
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LUFactorOrbitBounds
import Formalism.HermitianCurvature.HermitianCurvatureProofs.VectorVanishesBigCell
import Formalism.HermitianCurvature.HermitianCurvatureProofs.TwoByOneBlock
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BigCellHermitian
import Formalism.SharpRestriction.CuspSpanNormBounds.FrobeniusCoefficientMemLp.SigmaFiniteAmplitudes.FlipOneTwo

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.Pv.AmpDDPf Formalism.MainNotions.S.Pv.AmpDDPf.CC Formalism.FourierDecayAlt
open scoped ENNReal

noncomputable section

namespace Formalism.MainStatements.RankOne

variable {k r : ℕ}

theorem rpow_neg_le {x y C b : ℝ} (hx : 0 < x) (hy : 0 < y) (hC : 0 < C) (hb : 0 ≤ b) (h : y ≤ C * x) :
    x ^ (-b) ≤ C ^ b * y ^ (-b) := by
  rw [Real.rpow_neg hx.le, Real.rpow_neg hy.le, ← Real.inv_rpow hx.le, ← Real.inv_rpow hy.le,
    ← Real.mul_rpow hC.le (inv_nonneg.mpr hy.le)]
  apply Real.rpow_le_rpow (inv_nonneg.mpr hx.le) _ hb
  rw [← div_eq_mul_inv, inv_eq_one_div, div_le_div_iff₀ hx hy]
  linarith

theorem exists_pos (hk : 1 ≤ k) (L : LocBessel k r) (c : Fin r → ℂ) (hc : ∀ a, c a ≠ 0) :
    ∃ μ₁ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ, μ₁ᴴ * Hb k * μ₁ = Hb k ∧
      C2.PosPt k r L.z L.z' (bigCell k r c μ₁) ∧ C2.IsMonomial (Formalism.QuantumDeterminants.Zhat k r L.z L.z' (bigCell k r c μ₁)) := by
  obtain ⟨D, hz, hz'⟩ := bsetting_of k r hk L.z L.z' L.hz L.hz'
  set ζ : ℂ := ((Tz k r L.z * Tz k r L.z' + 1 : ℝ) : ℂ) with hζ
  have hTT : 0 < Tz k r L.z * Tz k r L.z' := mul_pos L.hz.2 L.hz'.2
  have hq : Tz k r D.z * Tz k r D.z' < Complex.normSq ζ := by
    rw [hz, hz', hζ, Complex.normSq_ofReal]; nlinarith
  have hsec := D.sec.2 ζ hq
  have hdom := P.big_cell_domain k r ℂ ℂ D (c, ζ) ⟨hc, hq⟩
  set d : Fin (r + 1) → ℂ := Fin.snoc c ζ with hd
  have hZ := P.PBM.zhat_bigCell_pt D d (by simpa [hd] using hq)
  rw [P.PBJ.Dens.ptMatN_bigPt, P.PBM.hMat_one] at hZ
  have e1 : (fun i => d i.castSucc) = c := by funext i; simp [hd]
  have e2 : d (Fin.last r) = ζ := by simp [hd]
  rw [e1, e2, hz, hz'] at hZ
  refine ⟨D.μsec ζ, hsec.1, ⟨bigCellMem k r c _ hc hsec.1, ?_⟩, 1, d, fun a => ?_, ?_⟩
  · have := hdom.2.2
    rw [hz, hz'] at this
    exact this
  · induction a using Fin.lastCases with
    | last => rw [e2, hζ]; exact Complex.ofReal_ne_zero.2 (by linarith)
    | cast i => simpa [hd] using hc i
  · rw [hZ]
    ext i j
    by_cases h : i = j
    · subst h; simp [C2.monoP]
    · simp [C2.monoP, h]

set_option maxHeartbeats 800000 in
theorem big_bound (hk : 1 ≤ k) (L : LocBessel k r) (c : Fin r → ℂ) (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ)
    (hc : ∀ a, c a ≠ 0) (hμ : μᴴ * Hb k * μ = Hb k) (b : ℝ) (hb : 0 ≤ b) :
    ∃ K : ℝ, 0 < K ∧ ∀ x : PairSp k r, Good L x →
      Pv.AmpDD.pairMaj (bigCell k r c μ) b x ≤
        K * (B.gN (Matrix.of x.1.2 * Matrix.of x.1.1) ^ (-(b / (2 * (5 * (r + 1) ^ 2 : ℕ)))) *
          B.gN (Matrix.of x.2.2 * Matrix.of x.2.1) ^ (-(b / (2 * (5 * (r + 1) ^ 2 : ℕ))))) := by
  obtain ⟨μ₁, hμ₁, hpos, hmono⟩ := exists_pos hk L c hc
  have hstd : C2.Std k r L.z L.z' := ⟨hk, L.hz, L.hz'⟩
  have hNI := P.norm_inverse_bound k r
  set γ₁ := bigCell k r c μ₁ with hγ₁
  set γ := bigCell k r c μ with hγ
  have hγU : γ ∈ UH (Hpk k r) := bigCellMem k r c μ hc hμ
  set T : ℝ := B.gN (1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) with hT
  have hT1 : 1 ≤ T := (hNI.2 1 WeylGroupFacts.uh_one).2
  obtain ⟨ρh, hρh⟩ := et_equiv L hstd hpos hmono T
  have hR : RStab k r γ₁ = {1} := Lem.orbRStabBig k r c μ₁ hc hμ₁
  have hET : ∀ n : Mt k r, Matrix.of n ∈ Nset k r → n ∈ ET (k := k) (r := r) L.z L.z' γ₁ T := by
    intro n hn
    obtain ⟨h1, h2⟩ := hρh n hn
    have h11 : (1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) ∈ RStab k r γ₁ := by rw [hR]; rfl
    have h3 := (h2 (1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) h11).2 (by
      rw [hR] at h1
      have h1' : ρh n = 1 := h1
      refine ⟨?_, ?_⟩
      · show (1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) * ρh n ∈ RStab k r γ₁
        rw [h1', Matrix.one_mul]; exact h11
      · show B.gN ((1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) * ρh n) ≤ T
        rw [h1', Matrix.one_mul])
    have e : (fun i j => (Matrix.of (1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) * Matrix.of n) i j : Mt k r) = n := by
      funext i j
      show ((1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) * Matrix.of n) i j = n i j
      rw [Matrix.one_mul]; rfl
    rwa [e] at h3
  obtain ⟨K, hK, hbd⟩ := pair_bound L hstd hpos hmono T hT1 b hb
  have m0 := P.TwoByOneBlock.emb_mem_UWb (r := r) hμ
  have m1 := P.TwoByOneBlock.emb_mem_UWb (r := r) hμ₁
  have w0 : B2.embWb k r μ ∈ UWset k r 0 := ⟨m0.1, m0.2, by simp⟩
  have w1 : B2.embWb k r μ₁ ∈ UWset k r 0 := ⟨m1.1, m1.2, by simp⟩
  have hW := P.weyl_subgroup_closed k r 0
  set ρ := (B2.embWb k r μ₁)⁻¹ * B2.embWb k r μ with hρ
  have hρW : ρ ∈ UWset k r 0 := hW.mul_mem _ (hW.inv_mem _ w1) _ w0
  have hρU : ρ ∈ UH (Hpk k r) := hρW.1
  have hρu := uh_isUnit hρU
  have hfac : γ = γ₁ * ρ := by
    rw [hγ, hγ₁, (P.bruhat_big_cell_factorization k r c μ).1, (P.bruhat_big_cell_factorization k r c μ₁).1, hρ, Matrix.mul_assoc,
      ← Matrix.mul_assoc (B2.embWb k r μ₁), Matrix.mul_nonsing_inv _ (uh_isUnit w1.1), Matrix.one_mul]
  obtain ⟨cW, hcW1, hcW⟩ := P.WeakDominationMajorants.Asm.uw_bound L.z' L.hz'.1 L.hz'.2
  set Γ := B.gN ρ with hΓ
  have hΓ1 : 1 ≤ Γ := (hNI.2 ρ hρU).2
  have hΓ0 : 0 < Γ := lt_of_lt_of_le one_pos hΓ1
  have hc0 : 0 < cW := lt_of_lt_of_le one_pos hcW1
  have hA0 : 0 < cW * Γ := mul_pos hc0 hΓ0
  have hB0 : 0 < Γ * Γ * cW := mul_pos (mul_pos hΓ0 hΓ0) hc0
  set β : ℝ := b / (2 * (5 * (r + 1) ^ 2 : ℕ)) with hβ
  have hβ0 : 0 ≤ β := by positivity
  refine ⟨(cW * Γ) ^ b * K * (Γ * Γ * cW) ^ β,
    mul_pos (mul_pos (Real.rpow_pos_of_pos hA0 _) hK) (Real.rpow_pos_of_pos hB0 _), fun x hx => ?_⟩
  obtain ⟨hn, hn', hh, hh'⟩ := hx
  set n := Matrix.of x.1.2
  set h := Matrix.of x.1.1
  set n' := Matrix.of x.2.2
  set h' := Matrix.of x.2.1
  set m := ρ * n' * ρ⁻¹ with hm
  have hmN : m ∈ Nset k r := PI.QuotSetU.UnitaryGroupMassFormula.SW.uw_conj_N hρW hn'
  have h1W : (1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) ∈ UWset k r L.z' := (P.weyl_subgroup_closed k r L.z').one_mem
  have hb1 := hbd (x.1, ((1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ), m)) ⟨hn, hmN, hh, h1W⟩ (hET _ hn)
  have hb2 : B.gN (h⁻¹ * n⁻¹ * γ₁ * m * 1) ^ (-b) ≤ K * (B.gN (n * h) ^ (-β) * B.gN (m * 1) ^ (-β)) := hb1
  rw [Matrix.mul_one, Matrix.mul_one] at hb2
  have hMU : h⁻¹ * n⁻¹ * γ * n' * h' ∈ UH (Hpk k r) :=
    WeylGroupFacts.uh_mul (WeylGroupFacts.uh_mul (WeylGroupFacts.uh_mul (WeylGroupFacts.uh_mul (WeylGroupFacts.uh_inv hh.1) (WeylGroupFacts.uh_inv hn.1)) hγU) hn'.1) hh'.1
  have hM1U : h⁻¹ * n⁻¹ * γ₁ * m ∈ UH (Hpk k r) :=
    WeylGroupFacts.uh_mul (WeylGroupFacts.uh_mul (WeylGroupFacts.uh_mul (WeylGroupFacts.uh_inv hh.1) (WeylGroupFacts.uh_inv hn.1)) hpos.1) hmN.1
  have e1 : h⁻¹ * n⁻¹ * γ₁ * m = h⁻¹ * n⁻¹ * γ * n' * h' * (h'⁻¹ * ρ⁻¹) := by
    rw [hfac, hm]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc h' h'⁻¹, Matrix.mul_nonsing_inv _ (uh_isUnit hh'.1), Matrix.one_mul]
  have e2 : n' * h' = ρ⁻¹ * m * ρ * h' := by
    rw [hm]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc ρ⁻¹ ρ h', Matrix.nonsing_inv_mul _ hρu, Matrix.one_mul, ← Matrix.mul_assoc ρ⁻¹ ρ,
      Matrix.nonsing_inv_mul _ hρu, Matrix.one_mul]
  have g0 : ∀ y : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ, 0 ≤ B.gN y := fun y => P.gN_nonneg_bessel_integrability y
  have hh'c : B.gN h' ≤ cW := hcW h' hh'
  have i1 : B.gN (h⁻¹ * n⁻¹ * γ₁ * m) ≤ (cW * Γ) * B.gN (h⁻¹ * n⁻¹ * γ * n' * h') := by
    rw [e1]
    refine (hNI.1 _ _).trans ?_
    rw [mul_comm]
    refine mul_le_mul_of_nonneg_right ((hNI.1 _ _).trans ?_) (g0 _)
    rw [(hNI.2 _ hh'.1).1, (hNI.2 _ hρU).1]
    exact mul_le_mul_of_nonneg_right hh'c (g0 _)
  have i2 : B.gN (n' * h') ≤ (Γ * Γ * cW) * B.gN m := by
    rw [e2]
    have j1 : B.gN (ρ⁻¹ * m) ≤ Γ * B.gN m := by
      have := hNI.1 ρ⁻¹ m
      rwa [(hNI.2 _ hρU).1] at this
    have j2 : B.gN (ρ⁻¹ * m * ρ) ≤ Γ * B.gN m * Γ := (hNI.1 _ _).trans (mul_le_mul_of_nonneg_right j1 (g0 _))
    calc _ ≤ B.gN (ρ⁻¹ * m * ρ) * B.gN h' := hNI.1 _ _
      _ ≤ Γ * B.gN m * Γ * cW := mul_le_mul j2 hh'c (g0 _) (mul_nonneg (mul_nonneg hΓ0.le (g0 m)) hΓ0.le)
      _ = _ := by ring
  have p1 := rpow_neg_le (lt_of_lt_of_le one_pos (hNI.2 _ hMU).2) (lt_of_lt_of_le one_pos (hNI.2 _ hM1U).2)
    hA0 hb i1
  have p2 := rpow_neg_le (lt_of_lt_of_le one_pos (hNI.2 _ hmN.1).2)
    (lt_of_lt_of_le one_pos (hNI.2 _ (WeylGroupFacts.uh_mul hn'.1 hh'.1)).2) hB0 hβ0 i2
  show B.gN (h⁻¹ * n⁻¹ * γ * n' * h') ^ (-b) ≤ _
  have q0 : 0 ≤ B.gN (n * h) ^ (-β) := Real.rpow_nonneg (g0 _) _
  calc _ ≤ (cW * Γ) ^ b * (K * (B.gN (n * h) ^ (-β) * B.gN m ^ (-β))) :=
        p1.trans (mul_le_mul_of_nonneg_left hb2 (Real.rpow_nonneg hA0.le _))
    _ ≤ (cW * Γ) ^ b * (K * (B.gN (n * h) ^ (-β) * ((Γ * Γ * cW) ^ β * B.gN (n' * h') ^ (-β)))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left p2 q0) hK.le)
          (Real.rpow_nonneg hA0.le _)
    _ = _ := by ring

theorem big_int (hk : 1 ≤ k) (L : LocBessel k r) (h0 : L.κN ≠ 0) (h1 : L.κN ≠ ⊤) (c : Fin r → ℂ)
    (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (hc : ∀ a, c a ≠ 0) (hμ : μᴴ * Hb k * μ = Hb k) {b : ℝ}
    (hb : 10 * ((r : ℝ) + 1) ^ 2 * ThreeDimData.AG k r < b) : Integrable (Pv.AmpDD.pairMaj (bigCell k r c μ) b) (pairMeas L) := by
  have hAG : 0 ≤ ThreeDimData.AG k r := by unfold ThreeDimData.AG; positivity
  have hb0 : 0 ≤ b := le_trans (by positivity) hb.le
  obtain ⟨K, hK, hbound⟩ := big_bound hk L c μ hc hμ b hb0
  set β : ℝ := b / (2 * ((5 * (r + 1) ^ 2 : ℕ) : ℝ)) with hβdef
  have hβ : ThreeDimData.AG k r < β := by
    rw [hβdef, lt_div_iff₀ (by positivity)]
    push_cast
    linarith
  have hI1 := growth_side L.hz.1 L.hz.2 L.hμW.1 L.hμW.2 h0 h1 hβ
  have hI2 := growth_side L.hz'.1 L.hz'.2 L.hμW'.1 L.hμW'.2 h0 h1 hβ
  have hPgood : ∀ᵐ x ∂(pairMeas L), Good L x := by rw [ae_iff]; exact pairMeas_bad L
  refine ⟨(measurable_pairMaj _ b).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall (pairMaj_nonneg _ b))]
  have hm1 : Measurable (fun p : Mt k r × Mt k r =>
      ENNReal.ofReal (B.gN (Matrix.of p.2 * Matrix.of p.1) ^ (-β))) :=
    ((P.s3dx1S_gNc.comp (PI.WUN.continuous_of.comp continuous_snd |>.matrix_mul
      (PI.WUN.continuous_of.comp continuous_fst))).measurable.pow_const _).ennreal_ofReal
  have hfm : Measurable (fun x : PairSp k r =>
      ENNReal.ofReal (B.gN (Matrix.of x.1.2 * Matrix.of x.1.1) ^ (-β)) *
      ENNReal.ofReal (B.gN (Matrix.of x.2.2 * Matrix.of x.2.1) ^ (-β))) :=
    (hm1.comp measurable_fst).mul (hm1.comp measurable_snd)
  have hpt : ∀ᵐ x ∂(pairMeas L), ENNReal.ofReal (Pv.AmpDD.pairMaj (bigCell k r c μ) b x) ≤
      ENNReal.ofReal K * (ENNReal.ofReal (B.gN (Matrix.of x.1.2 * Matrix.of x.1.1) ^ (-β)) *
        ENNReal.ofReal (B.gN (Matrix.of x.2.2 * Matrix.of x.2.1) ^ (-β))) := by
    refine hPgood.mono fun x hx => ?_
    rw [← ENNReal.ofReal_mul (Real.rpow_nonneg (P.gN_nonneg_bessel_integrability _) _), ← ENNReal.ofReal_mul hK.le]
    exact ENNReal.ofReal_le_ofReal (hbound x hx)
  refine (lintegral_mono_ae hpt).trans_lt ?_
  rw [lintegral_const_mul _ hfm]
  have : SFinite L.μN := sfin_muN L
  have : SigmaFinite L.μW := L.hμW.1.1
  have : SigmaFinite L.μW' := L.hμW'.1.1
  have hprod : ∫⁻ x, ENNReal.ofReal (B.gN (Matrix.of x.1.2 * Matrix.of x.1.1) ^ (-β)) *
      ENNReal.ofReal (B.gN (Matrix.of x.2.2 * Matrix.of x.2.1) ^ (-β)) ∂(pairMeas L) =
      (∫⁻ p, ENNReal.ofReal (B.gN (Matrix.of p.2 * Matrix.of p.1) ^ (-β)) ∂(L.μW.prod L.μN)) *
      ∫⁻ p, ENNReal.ofReal (B.gN (Matrix.of p.2 * Matrix.of p.1) ^ (-β)) ∂(L.μW'.prod L.μN) :=
    lintegral_prod_mul hm1.aemeasurable hm1.aemeasurable
  rw [hprod]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ENNReal.mul_lt_top hI1 hI2)

end Formalism.MainStatements.RankOne
