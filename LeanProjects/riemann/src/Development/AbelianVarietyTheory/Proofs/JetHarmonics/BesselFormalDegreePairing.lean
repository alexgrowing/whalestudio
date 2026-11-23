import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.BesselFormalDegreeIdentityStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.BesselSubgroupParameterMeasurePreservingStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.BesselCharacterUnipotentRadicalPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsHaarOnIffGroupsUnitaryUnipotentStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.DiscreteSeriesUnitarySmoothBasic
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory

theorem besPhInt_bilin {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (X X' : Wq →L[ℂ] Wp) :
    ∃ T : (Wp →L[ℂ] Wp) →L[ℂ] (Wq →L[ℂ] Wq) →L[ℂ] ℂ, ∀ P Q, T P Q = B.hsInner (P.comp (X.comp Q)) X' := by
  refine ⟨∑ i, ((ContinuousLinearMap.compL ℂ (Wq →L[ℂ] Wq) Wp ℂ (innerSL ℂ (X' (stdOrthonormalBasis ℂ Wq i)))).comp
    ((ContinuousLinearMap.compL ℂ (Wq →L[ℂ] Wq) Wp Wp).flip
      (X.comp (ContinuousLinearMap.apply ℂ Wq (stdOrthonormalBasis ℂ Wq i))))), fun P Q => ?_⟩
  simp [B.hsInner, B.hsVec, PiLp.inner_apply]

theorem besPhInt_rank {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (X X' : Wq →L[ℂ] Wp)
    (a a' : Wp) (b b' : Wq) :
    B.hsInner (((innerSL ℂ a).smulRight a').comp (X.comp ((innerSL ℂ b').smulRight b))) X' =
      ⟪a, X b⟫_ℂ * star ⟪a', X' b'⟫_ℂ := by
  have hb : X' b' = ∑ i, ⟪stdOrthonormalBasis ℂ Wq i, b'⟫_ℂ • X' (stdOrthonormalBasis ℂ Wq i) := by
    conv_lhs => rw [← (stdOrthonormalBasis ℂ Wq).sum_repr' b']
    simp [map_sum]
  have h2 : star ⟪a', X' b'⟫_ℂ = ⟪X' b', a'⟫_ℂ := inner_conj_symm _ _
  rw [h2, hb, sum_inner, Finset.mul_sum]
  simp only [B.hsInner, B.hsVec, PiLp.inner_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, map_smul,
    inner_smul_right, inner_smul_left, inner_conj_symm]
  ring

theorem besPhInt_xi {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (D : B.RealPlaceData k r Wp Wq) (p : B.SS k r) :
    B.xiTau D (1, 1) p = Formalism.QuantumDeterminants.psi k r D.z Formalism.QuantumDeterminants.cStd (Matrix.of p.1.2) *
      star (Formalism.QuantumDeterminants.psi k r D.z' Formalism.QuantumDeterminants.cStd (Matrix.of p.2.2)) := by
  unfold B.xiTau Formalism.QuantumDeterminants.psi B.lam
  rw [show ∀ x : ℂ, star x = (starRingEnd ℂ) x from fun _ => rfl, ← Complex.exp_conj, ← Complex.exp_add]
  congr 1
  simp only [map_mul, Complex.conj_I, Complex.conj_ofReal]
  push_cast
  ring

theorem besPhInt_xi_cont {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (D : B.RealPlaceData k r Wp Wq) :
    Continuous (B.xiTau D (1, 1)) := by
  have h : ∀ z, Continuous (fun m : Formalism.QuantumDeterminants.Mt k r => Formalism.QuantumDeterminants.ell k r z (Matrix.of m)) := by
    intro z
    unfold Formalism.QuantumDeterminants.ell
    refine continuous_finset_sum _ fun a _ => ?_
    split_ifs
    · simp only [Matrix.of_apply]
      fun_prop
    · simp only [Matrix.mulVec, dotProduct, Matrix.of_apply]
      fun_prop
  have h1 := (h D.z).comp (continuous_snd.comp (continuous_fst (X := Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r) (Y := Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r)))
  have h2 := (h D.z').comp (continuous_snd.comp (continuous_snd (X := Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r) (Y := Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r)))
  unfold B.xiTau B.lam
  refine Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp ?_))
  exact (continuous_const.mul (Complex.continuous_re.comp (continuous_const.mul h1))).sub
    (continuous_const.mul (Complex.continuous_re.comp (continuous_const.mul h2)))

theorem integral_xi_mul_Ph : Hyps → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (h : ℝ) (R : Rep k r) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (Wq : Type) [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [CompleteSpace Wq] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq) (l : R.H → Wp) (l' : R.H → Wq) (dd : ℝ), R.IsDS ε mu → Formalism.QuantumDeterminants.GapAtLeast ε mu h → GapOK k r h → IsBeL R D.z D.π D.μW D.μN l → IsBeL R D.z' D.π' D.μW' D.μN l' → (∀ w, w ≠ 0 → PI.BesselPeriodGGP.fdegH D.μG R.σ w = dd) → ∀ x ∈ R.TK, ∀ y ∈ R.TK, ∀ x' ∈ R.TK, ∀ y' ∈ R.TK, ∀ X X' : Wq →L[ℂ] Wp, Integrable (B.Ph D (fun g => ⟪x, R.σ g y⟫_ℂ • X) (fun g => ⟪x', R.σ g y'⟫_ℂ • X')) D.μSS ∧ ∫ p, B.xiTau D (1, 1) p * B.Ph D (fun g => ⟪x, R.σ g y⟫_ℂ • X) (fun g => ⟪x', R.σ g y'⟫_ℂ • X') p ∂D.μSS = ⟪l x, X (l' y)⟫_ℂ * star ⟪l x', X' (l' y')⟫_ℂ / (dd : ℂ) := by
  intro hH k r ε mu h R Wp _ _ _ _ Wq _ _ _ _ D l l' dd hDS _ _ hl hl' hdd x hx y hy x' hx' y' hy' X X'
  obtain ⟨hmul, hone, hinn, -, hTK, -⟩ := GlobalTheory.rep_basic_of_isDS hH.1.2.2.1 k r ε mu R hDS
  have hsf : ∀ {U : Set (B.Mat k r)} {μ : Measure (Formalism.QuantumDeterminants.Mt k r)}, B.IsHaarOn U μ → SigmaFinite μ := by
    intro U μ h
    have : IsFiniteMeasureOnCompacts μ := ⟨fun K hK => h.finite_compact K hK⟩
    infer_instance
  haveI := hsf D.haarW
  haveI := hsf D.haarN
  haveI := hsf D.haarW'
  have hN := (GlobalTheory.T.isHaarOn_iff_groups_unitary_unipotent k r D.μN).2.1.2 D.haarN
  have hW := ((GlobalTheory.T.isHaarOn_iff_groups_unitary_unipotent k r D.μW).2.2 D.z D.z_mem D.T_pos D.k_pos).2 D.haarW
  have hW' := ((GlobalTheory.T.isHaarOn_iff_groups_unitary_unipotent k r D.μW').2.2 D.z' D.z'_mem D.T'_pos D.k_pos).2 D.haarW'
  obtain ⟨-, -, -, -, mA, aeA⟩ := GlobalTheory.T.besselSubgroup_parameter_measurePreserving k r D.z D.μW D.μN D.k_pos D.z_mem D.T_pos hW hN
  obtain ⟨-, -, -, mB, -, aeB⟩ := GlobalTheory.T.besselSubgroup_parameter_measurePreserving k r D.z' D.μW' D.μN D.k_pos D.z'_mem D.T'_pos hW' hN
  obtain ⟨psn, -, psinv, -, -, -⟩ := GlobalTheory.T.besselCharacter_unipotentRadical_properties k r D.z Formalism.QuantumDeterminants.cStd D.z_mem
  obtain ⟨psn', -, -, pscj, -, -⟩ := GlobalTheory.T.besselCharacter_unipotentRadical_properties k r D.z' Formalism.QuantumDeterminants.cStd D.z'_mem
  obtain ⟨iA, eA⟩ := hl.2 x' (hTK x' hx') x hx
  obtain ⟨iB, eB⟩ := hl'.2 y (hTK y hy) y' hy'
  have iA' := mA.integrable_comp_of_integrable iA
  have iB' := mB.integrable_comp_of_integrable iB
  have eA' := integral_map mA.measurable.aemeasurable (mA.map_eq.symm ▸ iA.aestronglyMeasurable)
  have eB' := integral_map mB.measurable.aemeasurable (mB.map_eq.symm ▸ iB.aestronglyMeasurable)
  rw [mA.map_eq] at eA'
  rw [mB.map_eq] at eB'
  unfold be at eA eB
  rw [eA] at eA'
  rw [eB] at eB'
  obtain ⟨T, hT⟩ := besPhInt_bilin X X'
  have hI := integral_prod_bilin T iA' iB'
  have hInt := iA'.op_fst_snd (op := fun P Q => T P Q) (by fun_prop) ⟨‖T‖, T.le_opNorm₂⟩ iB'
  simp only [Function.comp_apply] at hI hInt
  rw [← eA', ← eB', hT, besPhInt_rank] at hI
  have hae : ∀ᵐ p ∂D.μSS, D.inSS p := by
    filter_upwards [(Measure.quasiMeasurePreserving_fst (μ := D.μW.prod D.μN) (ν := D.μW'.prod D.μN)).ae aeA,
      (Measure.quasiMeasurePreserving_snd (μ := D.μW.prod D.μN) (ν := D.μW'.prod D.μN)).ae aeB] with p h1 h2
    exact ⟨h1.1, h1.2, h2.1, h2.2⟩
  have key : ∀ p : B.SS k r, D.inSS p →
      B.xiTau D (1, 1) p * B.Ph D (fun g => ⟪x, R.σ g y⟫_ℂ • X) (fun g => ⟪x', R.σ g y'⟫_ℂ • X') p =
      T (beInt D.z Formalism.QuantumDeterminants.cStd D.π R.σ x' x
          (((fun i j => ((Matrix.of p.1.1)⁻¹ : Mx k r) i j), (fun i j => ((Matrix.of p.1.2)⁻¹ : Mx k r) i j))))
        (beInt D.z' Formalism.QuantumDeterminants.cStd D.π' R.σ y y'
          (((fun i j => (Matrix.of p.2.1 : Mx k r) i j),
            (fun i j => ((Matrix.of p.2.1)⁻¹ * Matrix.of p.2.2 * Matrix.of p.2.1 : Mx k r) i j)))) / (dd : ℂ) := by
    intro p hp
    rw [(GlobalTheory.T.bessel_formal_degree_identity hH k r ε mu R Wp Wq D dd hDS hdd x y x' y' X X' p hp).2, besPhInt_xi, ← hT]
    obtain ⟨h1, h2, h3, h4⟩ := hp
    have hof : ∀ M : Mx k r, Matrix.of (fun i j => M i j) = M := fun M => rfl
    unfold beInt JF.sL JF.sR
    simp only [hof]
    generalize Matrix.of p.1.1 = a at *
    generalize Matrix.of p.1.2 = n at *
    generalize Matrix.of p.2.1 = a' at *
    generalize Matrix.of p.2.2 = n' at *
    obtain ⟨ai, aa, aa'⟩ := Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.uh_inv h1.1
    obtain ⟨ni, nn, nn'⟩ := Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.uh_inv h2.1
    obtain ⟨bi, bb, bb'⟩ := Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.uh_inv h3.1
    have e1 : a⁻¹⁻¹ = a := Matrix.inv_eq_right_inv aa'
    have e2 : a' * (a'⁻¹ * n' * a') = n' * a' := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, bb, Matrix.one_mul]
    have e3 : ⟪x, R.σ (a⁻¹ * n⁻¹) x'⟫_ℂ = ⟪R.σ (n * a) x, x'⟫_ℂ := by
      have hna := Formalism.FourierDecayAlt.P.TranslationBesselVanishing.uh_mul h2.1 h1.1
      have hna' := Formalism.FourierDecayAlt.P.TranslationBesselVanishing.uh_mul ai ni
      rw [← hinn _ hna, ← hmul _ hna _ hna']
      have : n * a * (a⁻¹ * n⁻¹) = 1 := by
        rw [Matrix.mul_assoc, ← Matrix.mul_assoc a, aa, Matrix.one_mul, nn]
      rw [this, hone]
    rw [e1, e2, e3, (psinv n h2).2, (pscj a' h3 n' h4).2.2.2, star_star]
    simp only [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
    ring
  have hae' := hae.mono key
  have hInt' : Integrable (fun p => B.xiTau D (1, 1) p *
      B.Ph D (fun g => ⟪x, R.σ g y⟫_ℂ • X) (fun g => ⟪x', R.σ g y'⟫_ℂ • X') p) D.μSS :=
    (hInt.div_const (dd : ℂ)).congr (hae'.mono fun p hp => hp.symm)
  have hn : ∀ p, ‖B.xiTau D (1, 1) p‖ = 1 := by
    intro p
    rw [besPhInt_xi, norm_mul, norm_star, psn, psn', one_mul]
  refine ⟨?_, ?_⟩
  · have := hInt'.bdd_mul (c := 1) (f := fun p => star (B.xiTau D (1, 1) p))
      (besPhInt_xi_cont D).star.aestronglyMeasurable (Filter.Eventually.of_forall fun p => by rw [norm_star, hn])
    refine this.congr (Filter.Eventually.of_forall fun p => ?_)
    have h1 : star (B.xiTau D (1, 1) p) * B.xiTau D (1, 1) p = 1 := by
      rw [Complex.star_def, Complex.conj_mul', hn]; simp
    simp only
    rw [← mul_assoc, h1, one_mul]
  · rw [integral_congr_ae hae', integral_div]
    exact congrArg (· / (dd : ℂ)) hI

end GlobalTheory
