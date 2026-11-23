import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.OnePlaceKF
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.CellDataExists
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Formalism.SharpRestriction.CuspSpanNormBounds.LeadMinorK
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OrbitalIntegralAeConvergenceContinuity
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SettingConstruction
import Formalism.HermitianCurvature.HermitianCurvatureProofs.UnipotentUpperFacts
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BigCellHermitian
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ContinuousMulMt
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.DiscreteSeriesUnitarySmoothBasic
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.HaarEqSmul
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsHaarOnIffGroupsUnitaryUnipotent
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.BesselGapExistsFunctional
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.BesselDatumBothSidesAreSides
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.BesselSettingUniformConstant
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselTorusElementProperties
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LebesgueRootCoordinatesMapBesselTorusConj
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselFunctionEqScalarSqNormalisedBesselTorusCon
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsIsType
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HaarLieIsHaarOnUnipotentRadicalStatement

open BranchingSupport GlobalTheory.CellAmp Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.AmpNorm

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P

variable {k r : ℕ}

section stab

variable (c : Fin r → ℂ) (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ)

theorem mul_bigCell_low (M : B.Mat k r) (i j : Fin (2 * r + k + 1)) (hj : j.val < r) :
    (M * bigCell k r c μ) i j = M i (esI k r ⟨j.val, hj⟩) * c ⟨j.val, hj⟩ := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (esI k r ⟨j.val, hj⟩)]
  · unfold bigCell; rw [dif_pos hj, if_pos rfl]
  · intro l _ hl; unfold bigCell; rw [dif_pos hj, if_neg hl, mul_zero]
  · simp

theorem bigCell_row (i j : Fin (2 * r + k + 1)) (hi : i.val < r) (h : i.val + j.val ≠ 2 * r + k) :
    bigCell k r c μ i j = 0 := by
  unfold bigCell
  split_ifs with h1 h2 h3 h4 h5
  · have := congrArg Fin.val h2
    simp only [esI] at this
    omega
  · rfl
  · omega
  · rfl
  · omega
  · rfl

theorem bigCell_col (i j : Fin (2 * r + k + 1)) (hj : r + k < j.val) (h : i.val + j.val ≠ 2 * r + k) :
    bigCell k r c μ i j = 0 := by
  unfold bigCell
  rw [dif_neg (by omega), dif_neg (by omega), if_neg (by omega)]

theorem rStab_bigCell (hc : ∀ a, c a ≠ 0) (hg : bigCell k r c μ ∈ UH (Hpk k r)) :
    RStab k r (bigCell k r c μ) = {1} := by
  have hu := WeylGroupFacts.isUnit_of_uh hg
  set g := bigCell k r c μ with hgdef
  ext a
  rw [Set.mem_singleton_iff]
  refine ⟨fun ⟨ha, hb⟩ => ?_, ?_⟩
  swap
  · rintro rfl
    exact ⟨(nSubgroup k r).1, by rw [Matrix.mul_one, Matrix.nonsing_inv_mul _ hu]; exact (nSubgroup k r).1⟩
  set b := g⁻¹ * a * g with hbdef
  have e : a * g = g * b := by
    rw [hbdef, Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ hu]
  have ua := fun i j h => UnipotentUpperFacts.N_upper ha i j h
  have ub := fun i j h => UnipotentUpperFacts.N_upper hb i j h
  have hrow : ∀ i j : Fin (2 * r + k + 1), i.val < r → (a * g) i j = g i j := by
    intro i j hi
    rcases le_or_gt (i.val + j.val) (2 * r + k) with h | h
    · rw [e, Matrix.mul_apply, Finset.sum_eq_single (esI k r ⟨i.val, hi⟩)]
      · rw [ub _ _ (by rw [Fin.le_def]; simp only [esI]; omega)]
        split_ifs with h1
        · rw [h1, mul_one]
        · rw [mul_zero, hgdef, bigCell_row c μ i j hi]
          intro h2
          exact h1 (Fin.ext (by simp only [esI]; omega))
      · intro l _ hl
        rw [hgdef, bigCell_row c μ i l hi (fun h2 => hl (Fin.ext (by simp only [esI]; omega))), zero_mul]
      · simp
    · rw [Matrix.mul_apply, hgdef, bigCell_row c μ i j hi h.ne']
      refine Finset.sum_eq_zero fun l _ => ?_
      by_cases hl : l.val + j.val = 2 * r + k
      · rw [ua i l (by rw [Fin.le_def]; omega), if_neg (by rw [Fin.ext_iff]; omega), zero_mul]
      · rw [bigCell_col c μ l j (by omega) hl, mul_zero]
  ext i j
  rw [Matrix.one_apply]
  by_cases hi : i.val < r
  · have : a = a * g * g⁻¹ := (Matrix.mul_nonsing_inv_cancel_right _ _ hu).symm
    rw [this, Matrix.mul_apply, ← Matrix.one_apply, ← Matrix.mul_nonsing_inv _ hu, Matrix.mul_apply]
    exact Finset.sum_congr rfl fun l _ => by rw [hrow i l hi]
  rcases le_or_gt j i with hji | hji
  · exact ua i j hji
  rw [Fin.lt_def] at hji
  by_cases hj : j.val ≤ r + k
  · exact ha.2.2 i j (by omega) hj (by omega)
  have hjl := j.isLt
  have hm : 2 * r + k - j.val < r := by omega
  let m : Fin (2 * r + k + 1) := ⟨2 * r + k - j.val, by omega⟩
  have h1 := mul_bigCell_low c μ a i m hm
  have e1 : esI k r ⟨m.val, hm⟩ = j := Fin.ext (by simp only [esI, m]; omega)
  rw [e1, ← hgdef, e, Matrix.mul_apply, Finset.sum_eq_zero] at h1
  · rw [if_neg (by rw [Fin.ext_iff]; omega)]
    exact (mul_eq_zero.1 h1.symm).resolve_right (hc _)
  · intro l _
    rcases le_or_gt l m with hl | hl
    · rw [Fin.le_def] at hl
      have hl' : l.val < r := lt_of_le_of_lt hl hm
      have : g i l = 0 := by
        rw [hgdef]
        unfold bigCell
        rw [dif_pos hl', if_neg]
        rw [Fin.ext_iff]
        simp only [esI, m] at hl ⊢
        omega
      rw [this, zero_mul]
    · rw [ub l m hl.le, if_neg hl.ne', mul_zero]

end stab

theorem haar_smul {U : Set (B.Mat k r)} {μ : Measure (Mt k r)} (h : B.IsHaarOn U μ) {x : ℝ} (hx : 0 < x) :
    B.IsHaarOn U (ENNReal.ofReal x • μ) where
  conc := by rw [Measure.smul_apply, h.conc, smul_zero]
  left a ha := by rw [Measure.map_smul, h.left a ha]
  right a ha := by rw [Measure.map_smul, h.right a ha]
  finite_compact K hK := by
    rw [Measure.smul_apply, smul_eq_mul]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (h.finite_compact K hK)
  ne_zero h0 := h.ne_zero <| by
    have h1 := Measure.measure_univ_eq_zero.2 h0
    rw [Measure.smul_apply, smul_eq_mul] at h1
    exact Measure.measure_univ_eq_zero.1 ((mul_eq_zero.1 h1).resolve_left (ENNReal.ofReal_pos.2 hx).ne')

theorem lintegral_weight_scale (T T' s : ℝ) (hs : 0 < s) (F : (Fin r → ℂ) × ℂ → ℝ) :
    ∫⁻ q, ENNReal.ofReal (bcWeight k r T T' q * F (B7.d_S r s q)) =
      ENNReal.ofReal ((s ^ B.kap k r)⁻¹) * ∫⁻ q, ENNReal.ofReal (bcWeight k r T T' q * F q) := by
  set f : (Fin r → ℂ) × ℂ → ℝ≥0∞ := fun q => ENNReal.ofReal (bcWeight k r T T' q * F q) with hf
  have hpt : ∀ q, ENNReal.ofReal (bcWeight k r T T' q * F (B7.d_S r s q)) =
      ENNReal.ofReal ((s ^ B7.halfDimensionBlockSummand k r)⁻¹) * f (B7.d_S r s q) := by
    intro q
    simp only [hf]
    rw [B7.d_weight T T' s hs q, ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    field_simp
  simp_rw [hpt]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← (B7.d_emb_S s hs).lintegral_map, B7.d_map_S s hs,
    lintegral_smul_measure, smul_eq_mul, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity), B7.d_kap, pow_add,
    mul_inv]

section side

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

theorem hsNormSq_eq [FiniteDimensional ℂ Wq] (A : Wq →L[ℂ] Wp) : hsNormSq A = ‖B.hsVec A‖ ^ 2 := by
  unfold hsNormSq Formalism.MainNotions.S.hsInner B.hsVec
  rw [PiLp.norm_sq_eq_of_L2, Complex.re_sum]
  exact Finset.sum_congr rfl fun i _ => inner_self_eq_norm_sq (𝕜 := ℂ) _

theorem hsNormSq_smul [FiniteDimensional ℂ Wq] (t : ℂ) (A : Wq →L[ℂ] Wp) :
    hsNormSq (t • A) = ‖t‖ ^ 2 * hsNormSq A := by
  rw [hsNormSq_eq, hsNormSq_eq, show B.hsVec (t • A) = t • B.hsVec A from rfl, norm_smul, mul_pow]

theorem norm_inner_of_rankOne {x y : Wp} (h : (innerSL ℂ y).smulRight y = (innerSL ℂ x).smulRight x) :
    ‖⟪y, x⟫_ℂ‖ = ‖⟪x, x⟫_ℂ‖ := by
  have h1 := congrArg (fun A : Wp →L[ℂ] Wp => ‖⟪x, A x⟫_ℂ‖) h
  simp only [ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, inner_smul_right, norm_mul] at h1
  rw [norm_inner_symm x y] at h1
  exact (mul_self_inj (norm_nonneg _) (norm_nonneg _)).1 h1

theorem be_conj [CompleteSpace Wp] (R : Rep k r)
    (hmul : ∀ g ∈ GG k r, ∀ h ∈ GG k r, ∀ v, R.σ (g * h) v = R.σ g (R.σ h v)) (h1 : ∀ v, R.σ 1 v = v)
    (hun : ∀ g ∈ GG k r, ∀ v w, ⟪R.σ g v, R.σ g w⟫_ℂ = ⟪v, w⟫_ℂ)
    {z : Fin (2 * r + k + 1) → ℂ} {c c' : ℂ} (π : B.Mat k r → (Wp →L[ℂ] Wp)) {μW μN : Measure (Mt k r)}
    (hW : B.IsHaarOn (UWset k r z) μW) (hN : B.IsHaarOn (Nset k r) μN) {a : B.Mat k r} (ha : a ∈ GG k r)
    (hc : ∀ h ∈ UWset k r z, a * h = h * a)
    (hp : ∀ n ∈ Nset k r, psi k r z c (a * n * a⁻¹) = psi k r z c' n) (x v : R.H) :
    ThreeDimData.be z c π R.σ μW (μN.map (conjM a)) x v = ThreeDimData.be z c' π R.σ μW μN (R.σ a⁻¹ x) (R.σ a⁻¹ v) := by
  have := B7.sf hW
  have := B7.sf hN
  have hu := WeylGroupFacts.isUnit_of_uh ha
  have hai := WeylGroupFacts.uh_inv ha
  have hm : Measurable (conjM (k := k) (r := r) a) := (BesselUnitaryEquiv.conjE a hu).measurable
  have hΦe : MeasurableEmbedding (Prod.map id (conjM a) : Mt k r × Mt k r → Mt k r × Mt k r) :=
    ((MeasurableEquiv.refl _).prodCongr (BesselUnitaryEquiv.conjE a hu)).measurableEmbedding
  have hΦ : MeasurePreserving (Prod.map id (conjM a) : Mt k r × Mt k r → Mt k r × Mt k r)
      (μW.prod μN) (μW.prod (μN.map (conjM a))) := MeasurePreserving.prod (MeasurePreserving.id _) ⟨hm, rfl⟩
  have q1 := (Measure.quasiMeasurePreserving_fst (μ := μW) (ν := μN)).ae (B7.ae_mem hW)
  have q2 := (Measure.quasiMeasurePreserving_snd (μ := μW) (ν := μN)).ae (B7.ae_mem hN)
  unfold ThreeDimData.be
  rw [← hΦ.integral_comp hΦe]
  refine integral_congr_ae ?_
  filter_upwards [q1, q2] with p hK hM
  obtain ⟨y, b⟩ := p
  set K : B.Mat k r := Matrix.of y
  set M : B.Mat k r := Matrix.of b
  show (⟪v, R.σ (K * (a * M * a⁻¹)) x⟫_ℂ * star (psi k r z c (a * M * a⁻¹))) • π K⁻¹ =
    (⟪R.σ a⁻¹ v, R.σ (K * M) (R.σ a⁻¹ x)⟫_ℂ * star (psi k r z c' M)) • π K⁻¹
  have hKM : K * M ∈ GG k r := WeylGroupFacts.uh_mul hK.1 hM.1
  rw [hp M hM, ← hun a ha (R.σ a⁻¹ v), ← hmul _ ha _ hai, Matrix.mul_nonsing_inv _ hu, h1, ← hmul _ hKM _ hai,
    ← hmul _ ha _ (WeylGroupFacts.uh_mul hKM hai), ← Matrix.mul_assoc K, ← Matrix.mul_assoc K, ← hc K hK]
  simp only [Matrix.mul_assoc]

end side

theorem cellData_bigCell (L : LocBessel k r) (μG : Measure (Mt k r)) (D : B.RealPlaceData k r L.Wp L.Wq)
    (hz : D.z = L.z) (hz' : D.z' = L.z') {q : (Fin r → ℂ) × ℂ} (hq : q ∈ B7.Q0 D) :
    CellData L μG (B.gq D q) (Measure.dirac (fun i j => (1 : MatKR k r) i j)) μG (pairMeas L) := by
  have hOm := BigCellHermitian.gqDom D hq
  refine Model.cellData_open L μG _ hOm.1 (Matrix.nonsing_inv_mul _ (WeylGroupFacts.isUnit_of_uh hOm.1))
    (hz ▸ hz' ▸ hOm.2.2) ?_ (rStab_bigCell _ _ hq.1 hOm.1)
  rw [← hz, ← hz']
  have hZ := bigCellZhat k r D.z D.z' q.1 (D.μsec q.2) D.z_mem D.z'_mem
  rw [BigCellHermitian.herm_bigCell _ _ D.z_mem D.z'_mem, (D.sec.2 q.2 hq.2).2] at hZ
  refine ⟨1, fun a => if h : a.val < r then q.1 ⟨a.val, h⟩ else q.2, fun a => ?_, ?_⟩
  · dsimp only
    split_ifs
    · exact hq.1 _
    · intro h0
      have := hq.2
      rw [h0, map_zero] at this
      exact absurd (mul_pos D.T_pos D.T'_pos) this.not_gt
  · refine hZ.trans ?_
    ext i j
    rw [Matrix.diagonal_apply]
    show _ = if i = j then _ else _
    by_cases h : i = j
    · rw [if_pos h, if_pos h, h]
    · rw [if_neg h, if_neg h]

theorem lintegral_hsNormSq_amp : Hyps → AmpKF → CellConv → ∀ (k r : ℕ) (L : LocBessel k r) (μG : Measure (Mt k r)) (μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ), 2 ≤ k → L.c ≠ 0 → L.κN ≠ 0 → L.κN ≠ ⊤ → IsHaarOn (UH (Hpk k r)) μG → IsSection k r L.z L.z' μsec → ∃ c : ℝ, 0 < c ∧ ∀ (R : Rep k r) (mu : Fin (2 * r + k + 1) → ℝ) (h : ℝ) (l : R.H → L.Wp) (l' : R.H → L.Wq) (w : R.H), haveI := FiniteDimensional.complete ℂ L.Wp; haveI := FiniteDimensional.complete ℂ L.Wq; R.IsDS L.ε mu → GapAtLeast L.ε mu h → Formalism.FourierDecayAlt.ThreeDimData.GapOK k r h → GapCell k r h → (∀ x ∈ R.sm, ∀ v ∈ R.TK, Formalism.FourierDecayAlt.ThreeDimData.be L.z L.c L.π R.σ L.μW L.μN x v = (innerSL ℂ (l v)).smulRight (l x)) → (∀ x ∈ R.sm, ∀ v ∈ R.TK, Formalism.FourierDecayAlt.ThreeDimData.be L.z' L.c L.π' R.σ L.μW' L.μN x v = (innerSL ℂ (l' v)).smulRight (l' x)) → (∃ v, R.KFin v ∧ l v ≠ 0) → (∃ v, R.KFin v ∧ l' v ≠ 0) → PI.UpqRep.IsLowUnitH k r L.ε mu R.σ w → ∫⁻ q : (Fin r → ℂ) × ℂ, ENNReal.ofReal (bcWeight k r (Tz k r L.z) (Tz k r L.z') q * hsNormSq (amp R l l' w μG (bigCell k r q.1 (μsec q.2)))) = ENNReal.ofReal (c / PI.BesselPeriodGGP.fdegH μG R.σ w ^ 3) := by
  intro hH hAmp hConv k r L μG μsec hk hc hκ0 hκt hG hsec
  have := FiniteDimensional.complete ℂ L.Wp
  have := FiniteDimensional.complete ℂ L.Wq
  have hK : PI.KFinSmooth := hH.1.2.2.1
  have hk1 : 1 ≤ k := by omega
  have hstd : cStd ≠ 0 := by simp [cStd]
  have hα : cStd / L.c ≠ 0 := div_ne_zero hstd hc
  have hcα : L.c * (cStd / L.c) = cStd := mul_div_cancel₀ _ hc
  set α := cStd / L.c
  obtain ⟨ha, hT, -, hcell⟩ := ThA.TorusElt.torusElt k r α hα
  have hn : 0 < ‖α‖ := norm_pos_iff.2 hα
  have hGB := (HaarNotions.isHaarOn_iff_groups k r μG).1.1 hG
  have hNB : B.IsHaarOn (Nset k r) L.μN := (HaarNotions.isHaarOn_iff_groups k r L.μN).2.1.1
    (GlobalTheory.T.haarLie_isHaarOn_unipotentRadical k r L.κN (pos_iff_ne_zero.2 hκ0) hκt.lt_top)
  have hW := ((HaarNotions.isHaarOn_iff_groups k r L.μW).2.2 L.z L.hz.1 L.hz.2 hk1).1 L.hμW.1
  have hW' := ((HaarNotions.isHaarOn_iff_groups k r L.μW').2.2 L.z' L.hz'.1 L.hz'.2 hk1).1 L.hμW'.1
  have hδ : 0 < ‖α‖ ^ B.kap k r := by positivity
  have hN₁ := haar_smul hNB hδ
  set μ₁ := ENNReal.ofReal (‖α‖ ^ B.kap k r) • L.μN with hμ₁
  have hmap : μ₁.map (conjM (ThA.aT k r α)) = L.μN := by
    rw [ThA.TorusJac.haar_map_conj _ hN₁ α hα, hμ₁, smul_smul, ← ENNReal.ofReal_mul (by positivity),
      inv_mul_cancel₀ hδ.ne', ENNReal.ofReal_one, one_smul]
  set a := ThA.aT k r α
  have hu := WeylGroupFacts.isUnit_of_uh ha
  have hai := WeylGroupFacts.uh_inv ha
  have hp : ∀ z, inWb k r z → ∀ n ∈ Nset k r, psi k r z L.c (a * n * a⁻¹) = psi k r z cStd n := by
    intro z hz n hn
    unfold psi
    rw [((hT z hz).2 n hn).2.2, ← mul_assoc L.c, hcα]
  obtain ⟨u, hw⟩ := CapelliOfHC.exists_isType k r L.Wp L.z L.π L.u L.hz.1 L.hz.2 L.hπ
  obtain ⟨u', hw'⟩ := CapelliOfHC.exists_isType k r L.Wq L.z' L.π' L.u' L.hz'.1 L.hz'.2 L.hπ'
  obtain ⟨χ, hχ1, hχ2, hχ3⟩ := character_exists_alt
  let D : B.RealPlaceData k r L.Wp L.Wq :=
    ⟨L.z, L.z', L.π, L.π', μG, L.μW, μ₁, L.μW', μsec, χ, hk1, L.hz.1, L.hz'.1, L.hz.2, L.hz'.2,
      hw.2.1, hw'.2.1, hw.2.2.2.1, hw'.2.2.2.1, hw.2.2.1, hw'.2.2.1, hGB, hW, hN₁, hW', hsec, hχ1, hχ2, hχ3⟩
  obtain ⟨ν₁, ν₁', hS, hS'⟩ := exists_sideG_both_of_isType k r L.Wp L.Wq D u u' hw hw'
  obtain ⟨c₀, hc₀, hP⟩ := BesselNormSq.normSq_coef hH k r L.Wp L.Wq D
  obtain ⟨c₁, -, hdeg⟩ := BesselDegree.schur_fdeg hH k r L.ε μG hG
  refine ⟨((‖α‖ ^ 2) ^ B.kap k r)⁻¹ * c₀, by positivity, ?_⟩
  intro R mu h l l' w hR hgap hok hgc hl hl' ⟨v, hv, hv0⟩ ⟨v', hv', hv0'⟩ hlow
  obtain ⟨hmul, h1, hun, hsm, hTK, hTT, hKT, -⟩ := rep_basic_of_isDS hK k r L.ε mu R hR
  have hwK : R.KFin w := PI.UnitaryGroupMassFormula.LowSmooth.isKFinHpk_of_lowUnit hlow
  have hw0 : w ≠ 0 := by
    obtain ⟨P, -, hn1, -⟩ := hlow
    intro h0
    simp [h0] at hn1
  have hDD : ∀ x ∈ ThreeDimData.DDsp R.σ w, x ∈ R.TK := fun x hx =>
    (Submodule.span_le.2 (by rintro _ ⟨g, hg, rfl⟩; exact hTT g hg w (hKT w hwK)) : ThreeDimData.DDsp R.σ w ≤ R.TK) hx
  set d := PI.BesselPeriodGGP.fdegH μG R.σ w with hd
  have hdd : ∀ x, x ≠ 0 → PI.BesselPeriodGGP.fdegH μG R.σ x = d := fun x hx => by
    rw [hd, (hdeg mu R hR).1 x hx, (hdeg mu R hR).1 w hw0]
  have hd0 : 0 ≤ d := div_nonneg (by positivity) (integral_nonneg fun _ => by positivity)
  obtain ⟨l₁, hl₁⟩ := exists_normalised_bessel_map hH k r L.ε mu h R L.Wp _ _ _ _ _ _ _ hR hgap hok hS
  obtain ⟨l₁', hl₁'⟩ := exists_normalised_bessel_map hH k r L.ε mu h R L.Wq _ _ _ _ _ _ _ hR hgap hok hS'
  have hy := hTT _ hai _ (hKT v hv)
  have hy' := hTT _ hai _ (hKT v' hv')
  have e₁ : ‖⟪l₁ (R.σ a⁻¹ v), l v⟫_ℂ‖ = ‖⟪l v, l v⟫_ℂ‖ := by
    refine norm_inner_of_rankOne ?_
    rw [← (hl₁.2 _ (hTK _ hy) _ hy).2, ← hl v (hTK _ (hKT v hv)) v (hKT v hv), ← hmap]
    exact (be_conj R hmul h1 hun L.π hW hN₁ ha (hT _ L.hz.1).1 (hp _ L.hz.1) v v).symm
  have e₂ : ‖⟪l₁' (R.σ a⁻¹ v'), l' v'⟫_ℂ‖ = ‖⟪l' v', l' v'⟫_ℂ‖ := by
    refine norm_inner_of_rankOne ?_
    rw [← (hl₁'.2 _ (hTK _ hy') _ hy').2, ← hl' v' (hTK _ (hKT v' hv')) v' (hKT v' hv'), ← hmap]
    exact (be_conj R hmul h1 hun L.π' hW' hN₁ ha (hT _ L.hz'.1).1 (hp _ L.hz'.1) v' v').symm
  let LR : LocBessel k r :=
    { L with lam := mu, hlam := hR.1, Hs := R.H, hsN := R.nacg, hsI := R.ips, hsC := R.cs, σ := R.σ, hσ := hR.2 }
  have hone : OnePlaceKF LR h μG w l l' :=
    ⟨⟨hgap, hok, hc, hlow, hG, fun x hx y hy => hl x (hTK _ (hDD x hx)) y (hDD y hy),
      fun x hx y hy => hl' x (hTK _ (hDD x hx)) y (hDD y hy)⟩,
      fun x hx y hy => hl x (hTK _ (hDD x hx)) y (hKT y hy), fun x hx y hy => hl' x (hTK _ (hDD x hx)) y (hKT y hy)⟩
  let F : B.Mat k r → (L.Wq →L[ℂ] L.Wp) := fun x => coefF LR v v' (l v) (l' v') (a * x * a⁻¹)
  have hF : IsCoef R l₁ l₁' F (⟪l' v', l₁' (R.σ a⁻¹ v')⟫_ℂ * ⟪l₁ (R.σ a⁻¹ v), l v⟫_ℂ) := by
    refine ⟨1, fun _ => R.σ a⁻¹ v, fun _ => R.σ a⁻¹ v', fun _ => (innerSL ℂ (l' v')).smulRight (l v),
      fun _ => ⟨hy, hy'⟩, fun g hg => ?_, ?_⟩
    · rw [Fin.sum_univ_one, ← hun a ha (R.σ a⁻¹ v), ← hmul _ ha _ hai, Matrix.mul_nonsing_inv _ hu, h1,
        ← hmul _ hg _ hai, ← hmul _ ha _ (WeylGroupFacts.uh_mul hg hai), ← Matrix.mul_assoc]
      ext x
      show ⟪l' v', x⟫_ℂ • ⟪v, R.σ (a * g * a⁻¹) v'⟫_ℂ • l v = ⟪v, R.σ (a * g * a⁻¹) v'⟫_ℂ • ⟪l' v', x⟫_ℂ • l v
      exact smul_comm _ _ _
    · rw [Fin.sum_univ_one, ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, inner_smul_right]
  have hnorm := hP L.ε mu h R l₁ l₁' d hR hgap hok hl₁ hl₁' hdd F _ hF
  set S : ℂ := ⟪l v, l v⟫_ℂ * ⟪l' v', l' v'⟫_ℂ with hSdef
  have hS0 : 0 < ‖S‖ := norm_pos_iff.2 (mul_ne_zero (inner_self_ne_zero.2 hv0) (inner_self_ne_zero.2 hv0'))
  rw [norm_mul, norm_inner_symm, e₁, e₂, mul_comm ‖_‖, ← norm_mul, ← hSdef] at hnorm
  have := B7.sf hW
  have := B7.sf hW'
  have := B7.sf hN₁
  have hpt : ∀ q ∈ B7.Q0 D, hsNormSq (amp R l l' w μG (bigCell k r q.1 (μsec q.2))) =
      (d⁻¹ / ‖S‖) ^ 2 * ‖B.hsVec (B.JF D F (B.gq D (B7.d_S r (‖α‖ ^ 2) q)))‖ ^ 2 := by
    intro q hq
    have hcd := cellData_bigCell LR μG D rfl rfl hq
    obtain ⟨b, hb0, hb1, hb2⟩ := hConv k r LR h μG _ _ _ _ hκt hok hgc hcd hcd.2.2.1
    have hA : S • amp R l l' w μG (bigCell k r q.1 (μsec q.2)) = (d : ℂ)⁻¹ •
        besselJ k r L.z L.z' L.c L.π L.π' L.μW L.μN L.μW' (coefF LR v v' (l v) (l' v'))
          (bigCell k r q.1 (μsec q.2)) :=
      hAmp hH.1 k r LR h μG w l l' hone _ _ _ _ hcd b hb0 hb1 hb2 v v' hv hv' (l v) (l' v')
    rw [← hmap, ThA.besselJ_conj k r L.z L.z' L.c cStd L.π L.π' L.μW μ₁ L.μW' hW.conc hN₁.conc hW'.conc a hu
      (hT _ L.hz.1).1 (hT _ L.hz'.1).1 (hp _ L.hz.1) (hp _ L.hz'.1), hcell] at hA
    have h2 := congrArg hsNormSq hA
    rw [hsNormSq_smul, hsNormSq_smul, hsNormSq_eq (besselJ _ _ _ _ _ _ _ _ _ _ _ _), norm_inv, Complex.norm_real,
      Real.norm_of_nonneg hd0] at h2
    have e : B.gq D (B7.d_S r (‖α‖ ^ 2) q) =
        bigCell k r (fun i => ((‖α‖ ^ (2 * (r - i.val)) : ℝ) : ℂ) * q.1 i) (μsec q.2) := by
      simp only [pow_mul]
      rfl
    rw [e, div_pow, div_mul_eq_mul_div, eq_div_iff (by positivity), mul_comm]
    exact h2
  rw [lintegral_congr_ae (g := fun q : (Fin r → ℂ) × ℂ => ENNReal.ofReal ((d⁻¹ / ‖S‖) ^ 2) *
      ENNReal.ofReal (bcWeight k r (Tz k r L.z) (Tz k r L.z') q *
        (fun q => ‖B.hsVec (B.JF D F (B.gq D q))‖ ^ 2) (B7.d_S r (‖α‖ ^ 2) q))),
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_weight_scale (Tz k r L.z) (Tz k r L.z') (‖α‖ ^ 2) (by positivity)
      (fun q => ‖B.hsVec (B.JF D F (B.gq D q))‖ ^ 2)]
  · refine (congrArg (fun t => _ * (_ * t)) hnorm).trans ?_
    rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    rcases hd0.eq_or_lt with h0 | h0
    · simp [← h0]
    · field_simp
  · filter_upwards [B7.ae_mem_good_set_or_weight_zero D] with q hQ
    rw [← ENNReal.ofReal_mul (by positivity)]
    rcases hQ with hQ | hQ
    · rw [hpt q hQ, mul_left_comm]
    · have hQ' : bcWeight k r (Tz k r L.z) (Tz k r L.z') q = 0 := hQ
      simp only [hQ', zero_mul, mul_zero]

end GlobalTheory.AmpNorm
