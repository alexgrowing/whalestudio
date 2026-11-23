import Mathlib
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
import Development.AbelianVarietyTheory.Definitions.Foundations.IsFockIPOfFockData
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockActionPowAnalyticVectorNormLeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockDerivedActionsTensorMembersStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectorOfIntegrableDiscreteSeriesCoefficientStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryHarishChandraDiscreteSeriesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockPolynomialsLocallyFiniteRationalWeightsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockOperatorsLieRepresentationCommuteStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DiscreteSeriesIntegrableCoefficientProjectorStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockModelDualPairCasimirApplyStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LowestKTypesJointHarmonicShapeStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CasimirNumberIdentityDualPairStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EmbedsOfLowestTypeStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SameBlockOfPosC
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DerivedActionsAdjointCasimirSymmetricStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsUnitaryQuotientStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormProportionalOfIrreducibleStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DenseRangeFiniteVectorsDiscreteSeriesStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIsometryIntertwinerOfDerivedActionStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsTensorEmbeddingStatement

noncomputable section
namespace GlobalTheory.FockTensor
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible MeasureTheory

theorem exists_clm_of_selfAdjoint {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (f : H → H) (hsa : ∀ x y, inner ℂ (f x) y = inner ℂ x (f y)) (hid : ∀ x, f (f x) = f x) :
    ∃ P : H →L[ℂ] H, ∀ x, P x = f x := by
  let L : H →ₗ[ℂ] H :=
    { toFun := f
      map_add' := fun x y => ext_inner_right ℂ fun z => by simp [hsa, inner_add_left]
      map_smul' := fun c x => ext_inner_right ℂ fun z => by rw [hsa, inner_smul_left, RingHom.id_apply, inner_smul_left, hsa] }
  refine ⟨L.mkContinuous 1 fun x => ?_, fun x => rfl⟩
  show ‖f x‖ ≤ 1 * ‖x‖
  have h1 : ‖f x‖ ^ 2 ≤ ‖x‖ * ‖f x‖ := by
    have h2 : inner ℂ (f x) (f x) = inner ℂ x (f x) := by rw [hsa, hid]
    have h3 := norm_inner_le_norm (𝕜 := ℂ) x (f x)
    rw [← h2, inner_self_eq_norm_sq_to_K] at h3
    simpa using h3
  rcases (norm_nonneg (f x)).eq_or_lt with h | h
  · rw [← h]; positivity
  · nlinarith

theorem map_mem_hwSub {p q : ℕ} {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
    [Module ℂ W] {a : Mat p q →ₗ[ℂ] Module.End ℂ V} {b : Mat p q →ₗ[ℂ] Module.End ℂ W}
    (f : V →ₗ[ℂ] W) (hf : ∀ Z x, f (a Z x) = b Z (f x)) {μ : Ix p q → ℚ} {x : V}
    (hx : x ∈ hwSub a μ) : f x ∈ hwSub b μ := by
  simp only [hwSub, wtSub, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker,
    LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply] at hx ⊢
  refine ⟨fun c => ?_, fun c d h => ?_⟩
  · rw [← hf, ← map_smul, ← map_sub, hx.1 c, map_zero]
  · rw [← hf, hx.2 c d h, map_zero]

theorem map_casimir {p q : ℕ} {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
    [Module ℂ W] {a : Mat p q →ₗ[ℂ] Module.End ℂ V} {b : Mat p q →ₗ[ℂ] Module.End ℂ W}
    (f : V →ₗ[ℂ] W) (hf : ∀ Z x, f (a Z x) = b Z (f x)) (x : V) :
    f (casimir a x) = casimir b (f x) := by
  simp [casimir, LinearMap.sum_apply, map_sum, hf]

theorem exists_isHW {p q : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    {a : Mat p q →ₗ[ℂ] Module.End ℂ V} {μ : Ix p q → ℚ}
    (h : Module.finrank ℂ ↥(hwSub a μ) = 1) : ∃ v, IsHW a μ v := by
  obtain ⟨v, hv, -⟩ := finrank_eq_one_iff'.1 h
  exact ⟨v, fun h0 => hv (Subtype.ext h0), v.2⟩

theorem exists_unitHW {p q : ℕ} {T : GrpData p q} (D : DSRep T) {μ : Ix p q → ℚ}
    (h : Module.finrank ℂ ↥(hwSub D.HK.act μ) = 1) : ∃ v, UnitHW D μ v := by
  obtain ⟨v, hv, hv'⟩ := exists_isHW h
  have h0 : D.ι v ≠ 0 := fun h0 => hv (D.ι_inj (by simpa using h0))
  have h1 : ‖D.ι v‖ ≠ 0 := norm_ne_zero_iff.2 h0
  refine ⟨((‖D.ι v‖⁻¹ : ℝ) : ℂ) • v, ⟨smul_ne_zero (by simpa using h0) hv,
    Submodule.smul_mem _ _ hv'⟩, ?_⟩
  rw [map_smul, norm_smul]; simp [h1]

variable {p q r s : ℕ} {T0 : GrpData (p * r + q * s) (p * s + q * r)} {T1 : GrpData p q}
  {T2 : GrpData r s}

@[reducible] def fockU₁ (F : FockData T0 T1 T2) (hF : Continuous F.emb) : URep T1 where
  H := F.H
  π := F.π.comp (MonoidHom.inl _ _)
  isom _ x := F.isom _ x
  cont x := (F.cont x).comp (hF.comp (continuous_id.prodMk continuous_const))

@[reducible] def fockU₂ (F : FockData T0 T1 T2) (hF : Continuous F.emb) : URep T2 where
  H := F.H
  π := F.π.comp (MonoidHom.inr _ _)
  isom _ x := F.isom _ x
  cont x := (F.cont x).comp (hF.comp (continuous_const.prodMk continuous_id))

theorem fock_comm (F : FockData T0 T1 T2) (g : T1.G) (h : T2.G) (x : F.H) :
    F.π (1, h) (F.π (g, 1) x) = F.π (g, 1) (F.π (1, h) x) := by
  rw [← ContinuousLinearMap.mul_apply, ← ContinuousLinearMap.mul_apply, ← map_mul, ← map_mul]
  simp

theorem opE_comm (F : FockData T0 T1 T2) (e : T1.G → ℂ) (h : T2.G) (x : F.H) :
    F.π (1, h) (opE T1 (fun g => F.π (g, 1)) e x) = opE T1 (fun g => F.π (g, 1)) e (F.π (1, h) x) := by
  have := (LinearIsometry.mk (F.π (1, h)).toLinearMap (fun x => F.isom _ x)).integral_comp_comm
    (μ := T1.haar) (fun g => e g • F.π (g, 1) x)
  unfold opE
  refine this.symm.trans (integral_congr_ae (Filter.Eventually.of_forall fun g => ?_))
  show F.π (1, h) (e g • F.π (g, 1) x) = _
  rw [map_smul, fock_comm]

@[reducible] def polMod₂ (p q r s : ℕ) : GKMod r s where
  V := Pol p q r s
  act := fockAct2 p q r s
  lie := (GlobalTheory.T.fockOperators_lie_representation_commute p q r s).2.2.1
  kfin P := ((GlobalTheory.T.fock_polynomials_locallyFinite_rationalWeights p q r s).2 P).1
  wts P := ((GlobalTheory.T.fock_polynomials_locallyFinite_rationalWeights p q r s).2 P).2

theorem fock_bound₂ (F : FockData T0 T1 T2) (Y : Mat r s) (Q : Pol p q r s) :
    ∃ C ρ : ℝ, 0 ≤ C ∧ 0 < ρ ∧ ∀ k : ℕ,
      ‖F.ι ((fockAct2 p q r s Y ^ k) Q)‖ ≤ C * ρ ^ k * (k.factorial : ℝ) := by
  set Z : Matrix (Ln p q r s) (Ln p q r s) ℂ :=
    Matrix.kroneckerMapBilinear (LinearMap.mul ℂ ℂ) (1 : Mat p q) Y with hZ
  have hact : fockAct2 p q r s Y = omAct p q r s Z := rfl
  refine ⟨(2 : ℝ) ^ ((Q.totalDegree : ℝ) / 2 + 1) * ‖F.ι Q‖, 4 * (∑ l, ∑ l', ‖Z l l'‖) + 1,
    by positivity, by positivity, fun k => ?_⟩
  have h := (GlobalTheory.T.fockAction_pow_analyticVector_norm_le p q r s F.H F.ι (GlobalTheory.FockAlg.isFockIsometry_of_fockData F) Z Q.totalDegree k Q
    le_rfl).2
  rw [hact]
  refine h.trans ?_
  have h2 : (4 * ∑ l, ∑ l', ‖Z l l'‖) ^ k ≤ (4 * (∑ l, ∑ l', ‖Z l l'‖) + 1) ^ k :=
    pow_le_pow_left₀ (by positivity) (by linarith) k
  calc _ = (2 : ℝ) ^ ((Q.totalDegree : ℝ) / 2 + 1) * ‖F.ι Q‖ * (4 * ∑ l, ∑ l', ‖Z l l'‖) ^ k *
        (k.factorial : ℝ) := by ring
    _ ≤ _ := by gcongr

theorem proj_casimir₁ (F : FockData T0 T1 T2) (hF : Continuous F.emb) (D : DSRep T1) (v : D.HK.V)
    (χ : ℚ) (hχ : casimir D.HK.act v = (χ : ℂ) • v) (P : F.H →L[ℂ] F.H)
    (hsa : ∀ x y, inner ℂ (P x) y = inner ℂ x (P y))
    (hio : ∀ z, ∃ io : D.U.H →L[ℂ] F.H, IsHomG D (fockU₁ F hF) io ∧ io (D.ι v) = P z)
    (Q : Pol p q r s) : P (F.ι (casimir (fockAct1 p q r s) Q)) = (χ : ℂ) • P (F.ι Q) := by
  refine ext_inner_right ℂ fun z => ?_
  obtain ⟨io, hio1, hio2⟩ := hio z
  have hd : ∀ Y ∈ upq p q, ∀ y, HasDerivAt (fun t : ℝ => (fockU₁ F hF).π (T1.expt (t • Y))
      ((io.toLinearMap ∘ₗ D.ι) y)) ((io.toLinearMap ∘ₗ D.ι) (D.HK.act Y y)) 0 := by
    intro Y hY y
    have h2 := (io.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) (D.der Y hY y)
    refine HasDerivAt.congr_of_eventuallyEq h2 (Filter.Eventually.of_forall fun u => ?_)
    exact (congrArg (fun L => L (D.ι y)) (hio1 (T1.expt (u • Y)))).symm
  have h := (GlobalTheory.T.derived_actions_adjoint_casimir_symmetric p q T1 (fockU₁ F hF) _ _ (fockAct1 p q r s) D.HK.act F.ι _
    (GlobalTheory.T.fock_derived_actions_tensor_members p q r s T0 T1 T2 F).2.1 hd).2 Q v
  simp only [LinearMap.comp_apply, ContinuousLinearMap.coe_coe, hχ, map_smul, hio2] at h
  rw [hsa, inner_smul_left, hsa]
  refine h.trans ?_
  rw [inner_smul_right]; simp

theorem exists_embedding₂ (F : FockData T0 T1 T2) (hF : Continuous F.emb) (hrs : 1 ≤ r + s)
    (h7 : admQ7) (h8 : admQ8) (D' : DSRep T2) (lam' : Ix r s → ℚ) (hpar : IsParam lam')
    (hgap : GapGt lam' (((r + s : ℕ) : ℝ) ^ 3))
    (hone : Module.finrank ℂ ↥(hwSub D'.HK.act (blattner lam')) = 1)
    (hcas : ∀ y, casimir D'.HK.act y = (((normSq lam' - rhoSq (r + s) : ℚ)) : ℂ) • y)
    (hirr : IrrGK D'.HK) (P : F.H →L[ℂ] F.H)
    (hcomm : ∀ h x, F.π (1, h) (P x) = P (F.π (1, h) x)) (hPP : ∀ x, P (P x) = P x)
    (Φ : Pol p q r s) (hΦ : Φ ∈ hwSub (fockAct2 p q r s) (blattner lam')) (h0 : P (F.ι Φ) ≠ 0)
    (hcasΦ : P (F.ι (casimir (fockAct2 p q r s) Φ)) =
      (((normSq lam' - rhoSq (r + s) : ℚ)) : ℂ) • P (F.ι Φ)) :
    ∃ j : D'.U.H →ₗᵢ[ℂ] F.H, (∀ h y, j (D'.U.π h y) = F.π (1, h) (j y)) ∧ (∀ y, P (j y) = j y) ∧
      ∃ y, j y = P (F.ι Φ) := by
  let E : (polMod₂ p q r s).V →ₗ[ℂ] (fockU₂ F hF).H := P.toLinearMap ∘ₗ F.ι
  have hE : ∀ Y ∈ upq r s, ∀ Q, HasDerivAt (fun t : ℝ => (fockU₂ F hF).π (T2.expt (t • Y)) (E Q))
      (E (fockAct2 p q r s Y Q)) 0 := by
    intro Y hY Q
    have h2 := (P.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ)
      ((GlobalTheory.T.fock_derived_actions_tensor_members p q r s T0 T1 T2 F).2.2 Y hY Q)
    exact HasDerivAt.congr_of_eventuallyEq h2 (Filter.Eventually.of_forall fun u => hcomm _ _)
  have hadjE := (GlobalTheory.T.derived_actions_adjoint_casimir_symmetric r s T2 (fockU₂ F hF) _ _ _ _ E E hE hE).1
  obtain ⟨A, f, Eb, hfs, hEb, hEf, hf⟩ := GlobalTheory.T.exists_unitary_module_quotient_of_invariant_inner r s (polMod₂ p q r s) F.H E hadjE
  have hu : IsHW A.M.act (blattner lam') (f Φ) := by
    refine ⟨fun h => h0 ?_, map_mem_hwSub f hf hΦ⟩
    have := hEf Φ
    rw [h, map_zero] at this
    exact this.symm
  have hcu : casimir A.M.act (f Φ) = (((normSq lam' - rhoSq (r + s) : ℚ)) : ℂ) • f Φ := by
    apply hEb
    rw [← map_casimir f hf, map_smul, hEf, hEf]
    exact hcasΦ
  obtain ⟨v', hv'⟩ := exists_isHW hone
  obtain ⟨⟨M, ip, hi1, hi2, hi3⟩, hB⟩ := GlobalTheory.T.exists_unitary_harishChandra_discreteSeries r s T2 D'
  dsimp only at hB
  subst hB
  obtain ⟨e, -, hev, he⟩ := GlobalTheory.T.exists_injective_intertwiner_of_lowest_type h7 h8 r s lam' hpar hgap A ⟨D'.HK, ip, hi1, hi2, hi3⟩
    (f Φ) v' hu hv' hcu (hcas v') hirr
  let E₂ : D'.HK.V →ₗ[ℂ] (fockU₂ F hF).H := Eb ∘ₗ e
  have hE₂v : E₂ v' = P (F.ι Φ) := by
    show Eb (e v') = _
    rw [hev, hEf]; rfl
  have hpow : ∀ (Y : Mat r s) (y : D'.HK.V) (Q : Pol p q r s), e y = f Q → ∀ k : ℕ,
      e ((D'.HK.act Y ^ k) y) = f ((fockAct2 p q r s Y ^ k) Q) := by
    intro Y y Q h k
    induction k with
    | zero => simpa using h
    | succ k ih =>
      rw [pow_succ', pow_succ', Module.End.mul_apply, Module.End.mul_apply]
      exact (he _ _).trans ((congrArg _ ih).trans (hf _ _).symm)
  have hE₂ : ∀ Y ∈ upq r s, ∀ y, HasDerivAt
      (fun t : ℝ => (fockU₂ F hF).π (T2.expt (t • Y)) (E₂ y)) (E₂ (D'.HK.act Y y)) 0 := by
    intro Y hY y
    obtain ⟨Q, hQ⟩ := hfs (e y)
    have h1 : E₂ y = E Q := by
      show Eb (e y) = _
      rw [← hQ, hEf]
    have h2 : E₂ (D'.HK.act Y y) = E (fockAct2 p q r s Y Q) := by
      have := hpow Y y Q hQ.symm 1
      rw [pow_one, pow_one] at this
      exact (congrArg Eb this).trans (hEf _)
    rw [h1, h2]
    exact hE Y hY Q
  obtain ⟨c, hc⟩ := GlobalTheory.T.exists_norm_eq_mul_of_finrank_hwSub_eq_one r s D'.HK (blattner lam') D'.U.H F.H D'.ι E₂ hirr hone D'.ι_inj
    (GlobalTheory.T.derived_actions_adjoint_casimir_symmetric r s T2 D'.U _ _ _ _ D'.ι D'.ι D'.der D'.der).1
    (GlobalTheory.T.derived_actions_adjoint_casimir_symmetric r s T2 (fockU₂ F hF) _ _ _ _ E₂ E₂ hE₂ hE₂).1
  have hc0 : 0 < c := by
    have h1 := hc v'
    have h2 : 0 < ‖E₂ v'‖ := by rw [hE₂v]; exact norm_pos_iff.2 h0
    rw [h1] at h2
    by_contra hc0
    exact absurd h2 (not_lt.2 (mul_nonpos_of_nonpos_of_nonneg (not_lt.1 hc0) (norm_nonneg _)))
  have hbd : ∀ Y ∈ upq r s, ∀ y, ∃ C ρ : ℝ, 0 ≤ C ∧ 0 < ρ ∧ ∀ k : ℕ,
      ‖D'.ι ((D'.HK.act Y ^ k) y)‖ ≤ C * ρ ^ k * (k.factorial : ℝ) := by
    intro Y _ y
    obtain ⟨Q, hQ⟩ := hfs (e y)
    obtain ⟨C, ρ, hC, hρ, hb⟩ := fock_bound₂ F Y Q
    refine ⟨c⁻¹ * ‖P‖ * C, ρ, by positivity, hρ, fun k => ?_⟩
    have h2 : E₂ ((D'.HK.act Y ^ k) y) = P (F.ι ((fockAct2 p q r s Y ^ k) Q)) :=
      (congrArg Eb (hpow Y y Q hQ.symm k)).trans (hEf _)
    have h3 := hc ((D'.HK.act Y ^ k) y)
    rw [h2] at h3
    have h4 := (P.le_opNorm _).trans (mul_le_mul_of_nonneg_left (hb k) (norm_nonneg P))
    rw [h3] at h4
    calc _ = c⁻¹ * (c * ‖D'.ι ((D'.HK.act Y ^ k) y)‖) := by field_simp
      _ ≤ c⁻¹ * (‖P‖ * (C * ρ ^ k * (k.factorial : ℝ))) := by gcongr
      _ = _ := by ring
  have hden := GlobalTheory.T.dense_range_finite_vectors_discrete_series r s hrs T2 D' hirr.1 hbd
  obtain ⟨j, hj1, hj2⟩ := GlobalTheory.T.exists_isometry_intertwiner_of_derived_action r s hrs T2 D' (fockU₂ F hF) (((c⁻¹ : ℝ) : ℂ) • E₂) hden
    (fun y => by
      rw [LinearMap.smul_apply, norm_smul, hc, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (inv_pos.2 hc0)]
      field_simp)
    (fun Y hY y => by
      simp only [LinearMap.smul_apply, map_smul]
      exact (hE₂ Y hY y).const_smul ((c⁻¹ : ℝ) : ℂ))
    hbd
  refine ⟨j, hj2, fun y => ?_, D'.ι ((c : ℂ) • v'), ?_⟩
  · refine DenseRange.induction_on (p := fun y => P (j y) = j y) hden y
      (isClosed_eq (P.continuous.comp j.continuous) j.continuous) fun y => ?_
    obtain ⟨Q, hQ⟩ := hfs (e y)
    have h1 : E₂ y = P (F.ι Q) := by
      show Eb (e y) = _
      rw [← hQ, hEf]; rfl
    rw [hj1, LinearMap.smul_apply, h1, map_smul, hPP]
  · rw [hj1, LinearMap.smul_apply, map_smul, hE₂v, smul_smul, ← Complex.ofReal_mul,
      inv_mul_cancel₀ hc0.ne', Complex.ofReal_one, one_smul]

theorem arii_of (X : ProvA) (hD1 : DiscreteSeriesBlattner X) (hD3 : DiscreteSeriesHighestVector X) (h5 : admQ5 X) (h7 : admQ7)
    (h8 : admQ8) (lam : Ix p q → ℚ) (lam' : Ix r s → ℚ) (hrs : 1 ≤ r + s) (hpar : IsParam lam)
    (hpar' : IsParam lam') (hgap : GapGe lam (rangeOfSeventhSum p q))
    (hgap' : GapGt lam' (((r + s : ℕ) : ℝ) ^ 3))
    (hnum : normSq lam' - rhoSq (r + s) = normSq lam - rhoSq (p + q) -
      ((p + q : ℕ) : ℚ) * ((r + s : ℕ) : ℚ) * (((r + s : ℕ) : ℚ) - ((p + q : ℕ) : ℚ)) / 4)
    (h1 : ARi X lam lam') : ARii X lam lam' := by
  intro Φ hΦ
  set F := X.fock p q r s
  set D := X.ds p q lam
  set D' := X.ds r s lam'
  have hF := (GlobalTheory.T.fock_derived_actions_tensor_members p q r s _ _ _ F).1
  obtain ⟨hone, hcas, -⟩ := hD1 p q lam hpar
  obtain ⟨hone', hcas', -⟩ := hD1 r s lam' hpar'
  obtain ⟨v, hv⟩ := exists_unitHW D hone
  have hint := (hD3 p q lam hpar _ hgap le_rfl v hv).1
  obtain ⟨hsa, hPP, hio⟩ := (GlobalTheory.T.projector_of_integrable_discreteSeries_coefficient p q _ D v hv.2 hint).2 (fockU₁ F hF)
  have hm1 : mcoef D v 1 = 1 := by
    simp [mcoef, inner_self_eq_norm_sq_to_K, hv.2]
  have hid : ∀ x, opE (X.grp p q) (fockU₁ F hF).π (eFun D v)
      (opE (X.grp p q) (fockU₁ F hF).π (eFun D v) x) =
      opE (X.grp p q) (fockU₁ F hF).π (eFun D v) x := fun x => by
    have := hPP 1 x
    rwa [map_one, hm1, one_smul] at this
  obtain ⟨P, hP⟩ := exists_clm_of_selfAdjoint _ hsa hid
  simp only [← hP] at hsa hPP hio hid
  have h0 : P (F.ι Φ) ≠ 0 := by
    rw [hP]
    exact norm_pos_iff.1 (h1.2 Φ v hΦ hv).2.2.1
  have hio' : ∀ z, ∃ io : D.U.H →L[ℂ] F.H, IsHomG D (fockU₁ F hF) io ∧ io (D.ι v) = P z := fun z => by
    obtain ⟨io, h, h', -⟩ := hio (P z) (hid z)
    exact ⟨io, h, h'⟩
  have hirr : IrrGK D'.HK :=
    (((h5 r s hrs).1 D'.U ⟨D'.nontriv, D'.irred⟩).2.2 D'.HK D'.ι ⟨D'.ι_inj, D'.ι_range, D'.der⟩).2
  obtain ⟨j, hj1, hj2, y₀, hy₀⟩ := exists_embedding₂ F hF hrs h7 h8 D' lam' hpar' hgap' hone' hcas'
    hirr P (fun h x => by rw [hP, hP]; exact opE_comm F _ h x) hid Φ hΦ.2.2.1.2 h0 (by
      rw [GlobalTheory.T.fockModel_dualPair_casimir_apply, map_sub, map_sub, map_smul, map_smul,
        proj_casimir₁ F hF D v _ (hcas v) P hsa hio', ← sub_smul, hnum]
      push_cast
      rfl)
  obtain ⟨Tm, hT1, hT2, hT3, hT4⟩ := GlobalTheory.T.exists_isometric_tensor_embedding_intertwining p q _ D (fockU₁ F hF) v hv.2 D'.U.H j
    (fun g y y' => by
      have e1 := hsa (j y) ((fockU₁ F hF).π g (P (j y')))
      rw [hPP, inner_smul_right, hj2, hj2, j.inner_map_map] at e1
      exact e1)
    (fun y => by rw [← hj2]; exact hio' _)
  refine ⟨Tm, hT1, fun g h x y => ?_, D.ι v, y₀, ?_⟩
  · rw [← hT3, ← hT4 (F.π (1, h)) (D'.U.π h) (fun g z => fock_comm F g h z)
      (fun y => (hj1 h y).symm)]
    show _ = F.π (g, 1) (F.π (1, h) _)
    rw [← ContinuousLinearMap.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one, one_mul]
  · rw [hT2, hy₀, ← hid, hsa]
    exact inner_self_ne_zero.2 h0

theorem fock_contains_tensor : ∀ X : ProvA, admH1 X → admH2 X → DiscreteSeriesBlattner X → DiscreteSeriesPositivity X → admQ5 X →
    CoverHaarIntegration X → admQ7 → admQ8 → ArchimedeanRallisFirst X → ArchimedeanRallisSecond X := by
  intro X _ _ hD1 hD2 h5 h6 h7 h8 h1
  have hD3 := GlobalTheory.T.discreteSeries_integrableCoefficient_projector X hD2 h6
  refine ⟨fun t al be ga de h => ?_, fun t al be ga de h => ?_⟩
  · obtain ⟨hA, -, hG2, hG3⟩ := id h
    obtain ⟨⟨hp1, hp2, -⟩, -⟩ := GlobalTheory.T.lowestKTypes_jointHarmonicShape t al be ga de hA
    have hn : al.length + be.length + (ga.length + de.length) =
      al.length + be.length + ga.length + de.length := by omega
    have hM : al.length + de.length + t + (ga.length + be.length) =
      al.length + be.length + ga.length + de.length + t := by omega
    refine arii_of X hD1 hD3 h5 h7 h8 _ _ (by have := hA.1; omega) hp1 hp2 ?_ ?_ ?_
      (h1.1 t al be ga de h)
    · rw [rangeOfSeventhSum, hn]; exact hG3
    · rw [hM]; exact hG2
    · rw [hn, hM, (GlobalTheory.T.casimir_number_identity_dualPair t al be ga de hA).1]; push_cast; ring
  · obtain ⟨hA, -, hG2, hG3⟩ := id h
    obtain ⟨⟨hp1, -, hp2⟩, -⟩ := GlobalTheory.T.lowestKTypes_jointHarmonicShape t al be ga de hA
    have hn : al.length + be.length + (ga.length + de.length) =
      al.length + be.length + ga.length + de.length := by omega
    have hM : al.length + de.length + (ga.length + be.length + t) =
      al.length + be.length + ga.length + de.length + t := by omega
    refine arii_of X hD1 hD3 h5 h7 h8 _ _ (by have := hA.1; omega) hp1 hp2 ?_ ?_ ?_
      (h1.2 t al be ga de h)
    · rw [rangeOfSeventhSum, hn]; exact hG3
    · rw [hM]; exact hG2
    · rw [hn, hM, (GlobalTheory.T.casimir_number_identity_dualPair t al be ga de hA).2, (GlobalTheory.T.casimir_number_identity_dualPair t al be ga de hA).1]
      push_cast; ring

end GlobalTheory.FockTensor
