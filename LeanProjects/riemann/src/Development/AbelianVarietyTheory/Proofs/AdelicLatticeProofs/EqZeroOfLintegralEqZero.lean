import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ComplexEmbeddingHermitianQuadrupleSum

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.FockCompare
open scoped TensorProduct ContDiff Topology Pointwise

namespace GlobalTheory.OrientedHeis

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem taylor_bound {φ φ' φ'' : ℝ → ℂ} (h1 : ∀ s, HasDerivAt φ (φ' s) s) (h2 : ∀ s, HasDerivAt φ' (φ'' s) s) {C : ℝ}
    (hC : ∀ s, ‖φ'' s‖ ≤ C) {t : ℝ} (ht : 0 < t) : ‖(t : ℂ)⁻¹ * (φ t - φ 0) - φ' 0‖ ≤ C * t := by
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
  have a : ∀ s ∈ Set.Icc (0 : ℝ) t, ‖φ' s - φ' 0‖ ≤ C * (s - 0) :=
    norm_image_sub_le_of_norm_deriv_le_segment' (fun s _ => (h2 s).hasDerivWithinAt) fun s _ => hC s
  have d : ∀ s : ℝ, HasDerivAt (fun s : ℝ => φ s - (s : ℂ) * φ' 0) (φ' s - φ' 0) s := fun s => by
    have := (h1 s).sub ((Complex.ofRealCLM.hasDerivAt (x := s)).mul_const (φ' 0))
    rw [Complex.ofRealCLM_apply, Complex.ofReal_one, one_mul] at this
    exact this
  have b := norm_image_sub_le_of_norm_deriv_le_segment' (C := C * t) (a := 0) (b := t)
    (fun s _ => (d s).hasDerivWithinAt) (fun s hs => (a s ⟨hs.1, hs.2.le⟩).trans
      (mul_le_mul_of_nonneg_left (by linarith [hs.2]) hC0)) t ⟨ht.le, le_rfl⟩
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 ht.ne'
  have e : (t : ℂ)⁻¹ * (φ t - φ 0) - φ' 0 = (t : ℂ)⁻¹ * (φ t - t * φ' 0 - (φ 0 - ((0 : ℝ) : ℂ) * φ' 0)) := by
    field_simp
    simp
    ring
  rw [e, norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg ht.le, inv_mul_le_iff₀ ht]
  linarith

theorem eq_zero_of_lintegral_eq_zero {G : Type} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [MeasurableSpace G] [BorelSpace G] (Γ : AddSubgroup G) [Countable Γ] (μ : Measure G) [μ.IsAddHaarMeasure]
    (𝓕 : Set G) (h𝓕 : IsAddFundamentalDomain Γ 𝓕 μ) (f : G → ℂ) (hf : Continuous f)
    (hp : ∀ γ ∈ Γ, ∀ w, ‖f (γ + w)‖ = ‖f w‖) (h0 : ∫⁻ w in 𝓕, ‖f w‖ₑ ^ 2 ∂μ = 0) : f = 0 := by
  have ho : IsOpen {w | f w ≠ 0} := isOpen_ne_fun hf continuous_const
  have h1 := (lintegral_eq_zero_iff (hf.measurable.enorm.pow_const 2)).1 h0
  have h2 : μ ({w | f w ≠ 0} ∩ 𝓕) = 0 := by
    rw [← Measure.restrict_apply ho.measurableSet]
    refine measure_mono_null (fun w hw => ?_) h1
    simpa using hw
  have h3 := h𝓕.measure_zero_of_invariant _ (fun γ => by
    ext w
    rw [Set.mem_vadd_set_iff_neg_vadd_mem]
    show f (((-γ : Γ) : G) + w) ≠ 0 ↔ f w ≠ 0
    rw [← norm_ne_zero_iff, hp _ (-γ).2, norm_ne_zero_iff]) h2
  have h4 := (ho.measure_eq_zero_iff μ).1 h3
  funext w
  by_contra hw
  exact (Set.eq_empty_iff_forall_notMem.1 h4) w hw

theorem lintegral_eq_zero_of_approx {G : Type} [MeasurableSpace G] (ν : Measure G) (hν : ν Set.univ = 1) (δ : G → ℂ)
    (C C' : ℝ) (h : ∀ t : ℝ, 0 < t → ∃ a b r : G → ℂ, δ = a - b ∧ ∫⁻ w, ‖a w‖ₑ ^ 2 ∂ν = ∫⁻ w, ‖r w‖ₑ ^ 2 ∂ν ∧
      (∀ w, ‖r w‖ ≤ C * t) ∧ ∀ w, ‖b w‖ ≤ C' * t) : ∫⁻ w, ‖δ w‖ₑ ^ 2 ∂ν = 0 := by
  have en : ∀ z : ℂ, ‖z‖ₑ ^ 2 = ENNReal.ofReal (‖z‖ ^ 2) := fun z => by
    rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm_eq_enorm]
  have key : ∀ t : ℝ, 0 < t → ∫⁻ w, ‖δ w‖ₑ ^ 2 ∂ν ≤ ENNReal.ofReal (2 * (C * t) ^ 2 + 2 * (C' * t) ^ 2) := by
    intro t ht
    obtain ⟨a, b, r, e, h1, h2, h3⟩ := h t ht
    have h4 : ∫⁻ w, ‖r w‖ₑ ^ 2 ∂ν ≤ ENNReal.ofReal ((C * t) ^ 2) := by
      refine (lintegral_mono (g := fun _ => ENNReal.ofReal ((C * t) ^ 2)) fun w => ?_).trans ?_
      · show ‖r w‖ₑ ^ 2 ≤ _
        rw [en]
        exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (norm_nonneg _) (h2 w) 2)
      · rw [lintegral_const, hν, mul_one]
    calc ∫⁻ w, ‖δ w‖ₑ ^ 2 ∂ν ≤ ∫⁻ w, (2 * ‖a w‖ₑ ^ 2 + ENNReal.ofReal (2 * (C' * t) ^ 2)) ∂ν := by
          refine lintegral_mono fun w => ?_
          show ‖δ w‖ₑ ^ 2 ≤ 2 * ‖a w‖ₑ ^ 2 + ENNReal.ofReal (2 * (C' * t) ^ 2)
          rw [en, en, ← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num),
            ← ENNReal.ofReal_add (by positivity) (by positivity)]
          refine ENNReal.ofReal_le_ofReal ?_
          have h5 : ‖δ w‖ ≤ ‖a w‖ + ‖b w‖ := by rw [e]; exact norm_sub_le _ _
          have h6 := pow_le_pow_left₀ (norm_nonneg _) h5 2
          have h7 := pow_le_pow_left₀ (norm_nonneg _) (h3 w) 2
          nlinarith [sq_nonneg (‖a w‖ - ‖b w‖)]
      _ = 2 * ∫⁻ w, ‖a w‖ₑ ^ 2 ∂ν + ENNReal.ofReal (2 * (C' * t) ^ 2) := by
          rw [lintegral_add_right _ measurable_const, lintegral_const_mul' _ _ (by norm_num), lintegral_const, hν, mul_one]
      _ ≤ 2 * ENNReal.ofReal ((C * t) ^ 2) + ENNReal.ofReal (2 * (C' * t) ^ 2) := by
          rw [h1]; gcongr
      _ = _ := by
          rw [ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_mul (p := 2) (q := (C * t) ^ 2) (by norm_num),
            ENNReal.ofReal_ofNat]
  have hc : Continuous fun t : ℝ => ENNReal.ofReal (2 * (C * t) ^ 2 + 2 * (C' * t) ^ 2) :=
    ENNReal.continuous_ofReal.comp (by fun_prop)
  have ht := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))
  simp only [mul_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero, ENNReal.ofReal_zero] at ht
  exact le_antisymm (ge_of_tendsto ht (eventually_nhdsWithin_of_forall key)) bot_le

variable {D : D7} {θ : InfFam D} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D}

theorem theta_norm_periodic (hψ : IsStdChar D ψ (-1)) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) :
    ∀ γ ∈ ratL T S, ∀ w, ‖f (γ + w)‖ = ‖f w‖ := by
  rintro _ ⟨γ, rfl⟩ w
  have := congrArg norm (hf.quasi γ w)
  rw [norm_mul, hψ.1.2.1, one_mul] at this
  exact this

theorem theta_bounded (hψ : IsStdChar D ψ (-1)) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) :
    ∃ C : ℝ, ∀ w, ‖f w‖ ≤ C := by
  obtain ⟨-, -, -, -, -, K, hK, hc⟩ := GlobalTheory.AdelicMatrixLattice.lattice D T S
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hf.cont.continuousOn
  refine ⟨C, fun w => ?_⟩
  obtain ⟨γ, hγ, h⟩ := hc w
  rw [← theta_norm_periodic hψ hf γ hγ w]
  exact hC _ h

theorem heisO_zero (f : WO S T → ℂ) : heisO ψ S T 0 f = f := by
  funext w
  have h : symplOH S T w 0 = 0 := by
    have := symplOH_add_right w 0 0
    rw [add_zero] at this
    exact left_eq_add.1 this
  unfold heisO
  rw [h, AddChar.map_zero_eq_one, one_mul, add_zero]

theorem quotient_bound (hθ : IsInfFam θ) (hψ : IsStdChar D ψ (-1)) {L : ℝ →+ WO S T} (hL : IsRealDir T S L)
    {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) : ∃ C : ℝ, ∀ t : ℝ, 0 < t → ∀ w,
      ‖((t : ℂ)⁻¹ • (heisO ψ S T (L t) f - f) - dLine ψ S T L f) w‖ ≤ C * t := by
  have h1 := theta_dLine hθ hψ hL hf
  obtain ⟨C, hC⟩ := theta_bounded hψ (theta_dLine hθ hψ hL h1)
  refine ⟨C, fun t ht w => ?_⟩
  have := taylor_bound (hasDerivAt_heisO hθ hψ hL hf w) (hasDerivAt_heisO hθ hψ hL h1 w) (C := C) (fun s => by
    unfold heisO
    rw [norm_mul, hψ.1.2.1, one_mul]
    exact hC _) ht
  rw [L.map_zero, heisO_zero, heisO_zero] at this
  exact this

variable {χS χT : (Formalism.L2.Theta.AE D)ˣ →* Circle} {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)}

theorem om_dLine (hom : IsWeilDatumO ψ S T χS χT om) (hθ : IsInfFam θ) (g : GA D S) (h : GA D T)
    {L L' : ℝ →+ WO S T} (hL : IsRealDir T S L) (hL' : IsRealDir T S L') (hLL : ∀ t, L' t = actO S T g h (L t))
    {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) :
    om (g, h) (dLine ψ S T L f) = dLine ψ S T L' (om (g, h) f) := by
  have hψ := hom.std
  obtain ⟨i1, i2, i3, i4, i5, K, hK, hc⟩ := GlobalTheory.AdelicMatrixLattice.lattice D T S
  haveI : BorelSpace (WA T S) := ⟨rfl⟩
  obtain ⟨⟨μ, 𝓕, hμ, h𝓕, h1⟩, -⟩ := GlobalTheory.meanSquare_addFundamentalDomain_of_cocompact (WA T S) (ratL T S) K hK hc
  haveI : Countable (ratL T S) := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  have hf' := hom.om_pres (g, h) f hf
  have hδ := theta_sub (theta_dLine hθ hψ hL' hf') (hom.om_pres (g, h) _ (theta_dLine hθ hψ hL hf))
  obtain ⟨C, hC⟩ := quotient_bound hθ hψ hL hf
  obtain ⟨C', hC'⟩ := quotient_bound hθ hψ hL' hf'
  refine (sub_eq_zero.1 (eq_zero_of_lintegral_eq_zero (G := WA T S) (ratL T S) μ 𝓕 h𝓕 _ hδ.cont
    (theta_norm_periodic hψ hδ) ?_)).symm
  refine lintegral_eq_zero_of_approx (μ.restrict 𝓕) (by rw [Measure.restrict_apply_univ, h1]) _ C C' fun t ht => ?_
  have hr := theta_sub (theta_smul (t : ℂ)⁻¹ (theta_sub (theta_heisO_real hθ hψ (hL.2 t) hf) hf))
    (theta_dLine hθ hψ hL hf)
  refine ⟨_, _, _, ?_, hom.om_unit μ 𝓕 hμ h𝓕 (g, h) _ hr, hC t ht, hC' t ht⟩
  rw [map_sub, map_smul, map_sub, hom.om_heis g h _ f hf, hLL]
  abel

theorem isLineAt_lineAt (hθ : IsInfFam θ) {m n : ℕ} (τ : D.what₂.Tau) (z : Matrix (Fin m) (Fin n) ℂ) :
    IsLineAt θ τ z (lineAt θ τ z) :=
  Classical.epsilon_spec (GlobalTheory.RealLineAt.lineAt_exists D θ hθ m n τ z)

theorem isRealDir_lineAt (hθ : IsInfFam θ) (τ : D.what₂.Tau) (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) :
    IsRealDir T S (lineAt θ τ z) := ⟨(isLineAt_lineAt hθ τ z).1, (isLineAt_lineAt hθ τ z).2.1⟩

theorem compAt_mul (τ : D.what₂.Tau) {k m n : ℕ} (x : Mx D k m) (y : Mx D m n) :
    compAt θ τ (HMul.hMul x y : Mx D k n) = compAt θ τ x * compAt θ τ y :=
  Matrix.map_mul (f := (θ τ).comp (infPart D))

theorem compAt_mt_mul_inv (τ : D.what₂.Tau) (g : GA D S) : compAt θ τ (mt S g) * compAt θ τ (mt S g⁻¹) = 1 := by
  have e : mt S g * mt S g⁻¹ = 1 := by
    unfold Formalism.L2.Theta.mt
    rw [← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]
  rw [← compAt_mul]
  erw [e]
  exact Matrix.map_one _ (((θ τ).comp (infPart D)).map_zero) (((θ τ).comp (infPart D)).map_one)

theorem lineAt_move (hθ : IsInfFam θ) (g : GA D S) (h : GA D T) (τ : D.what₂.Tau)
    (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) (t : ℝ) :
    lineAt θ τ (compAt θ τ (mt T h) * z * compAt θ τ (mt S g⁻¹)) t = actO S T g h (lineAt θ τ z t) := by
  have hL := isLineAt_lineAt hθ τ z
  let L : ℝ →+ WO S T :=
    { toFun := fun t => actO S T g h (lineAt θ τ z t)
      map_zero' := by unfold actO; rw [AddMonoidHom.map_zero, Matrix.mul_zero, Matrix.zero_mul]
      map_add' := fun s t => by unfold actO; rw [AddMonoidHom.map_add, Matrix.mul_add, Matrix.add_mul] }
  have hL' : IsLineAt θ τ (compAt θ τ (mt T h) * z * compAt θ τ (mt S g⁻¹)) L := by
    refine ⟨(continuous_const.matrix_mul hL.1).matrix_mul continuous_const, fun t => ?_, fun t τ' => ?_⟩
    · show (actO S T g h (lineAt θ τ z t)).map (finPart D) = 0
      unfold actO
      rw [Matrix.map_mul, Matrix.map_mul, hL.2.1, Matrix.mul_zero, Matrix.zero_mul]
    · show compAt θ τ' (actO S T g h (lineAt θ τ z t)) = _
      unfold actO
      rw [compAt_mul, compAt_mul, hL.2.2]
      split_ifs with e
      · rw [e, Matrix.mul_smul, Matrix.smul_mul]
      · rw [Matrix.mul_zero, Matrix.zero_mul]
  rw [GlobalTheory.RealLineAt.lineAt_unique D θ hθ _ _ τ _ _ _ (isLineAt_lineAt hθ τ _) hL']
  rfl

theorem theta_dRho (hθ : IsInfFam θ) (hψ : IsStdChar D ψ (-1)) (τ : D.what₂.Tau)
    (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) :
    IsThetaFunO ψ S T (Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ z f) :=
  theta_dLine hθ hψ (isRealDir_lineAt hθ τ z) hf

theorem om_dRho (hom : IsWeilDatumO ψ S T χS χT om) (hθ : IsInfFam θ) (g : GA D S) (h : GA D T) (τ : D.what₂.Tau)
    (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) :
    om (g, h) (Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ z f) =
      Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ (compAt θ τ (mt T h) * z * compAt θ τ (mt S g⁻¹)) (om (g, h) f) :=
  om_dLine hom hθ g h (isRealDir_lineAt hθ τ z) (isRealDir_lineAt hθ τ _) (lineAt_move hθ g h τ z) hf

end GlobalTheory.OrientedHeis

end
