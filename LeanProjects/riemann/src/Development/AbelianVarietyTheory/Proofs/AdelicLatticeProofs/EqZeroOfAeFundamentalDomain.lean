import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HasDerivAtZeroAndIsTheta
import Development.AbelianVarietyTheory.Proofs.HeightProofs.CocompactTensor
import Development.AbelianVarietyTheory.Proofs.HeightProofs.MeanSquareAddFundamentalDomainOfCocompact

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ContDiff Topology ENNReal

namespace GlobalTheory.WeilVacMove

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Filter

section Abstract

theorem ae_zero_of_lintegral_eq {X : Type} [MeasurableSpace X] (ν : Measure X) [IsFiniteMeasure ν]
    (a b : ℕ → X → ℂ) (c : X → ℂ) (C : ℝ) (ha : ∀ n, Measurable (a n)) (hb : ∀ n, Measurable (b n))
    (hc : Measurable c) (hC : ∀ n x, ‖a n x‖ ≤ C) (ha0 : ∀ x, Tendsto (fun n => a n x) atTop (𝓝 0))
    (hbc : ∀ x, Tendsto (fun n => b n x) atTop (𝓝 (c x)))
    (he : ∀ n, ∫⁻ x, ‖b n x‖ₑ ^ 2 ∂ν = ∫⁻ x, ‖a n x‖ₑ ^ 2 ∂ν) : ∀ᵐ x ∂ν, c x = 0 := by
  have hq : Continuous fun z : ℂ => ‖z‖ₑ ^ 2 := (ENNReal.continuous_pow 2).comp continuous_enorm
  have h1 : Tendsto (fun n => ∫⁻ x, ‖a n x‖ₑ ^ 2 ∂ν) atTop (𝓝 (∫⁻ _, 0 ∂ν)) := by
    refine tendsto_lintegral_of_dominated_convergence (fun _ => ENNReal.ofReal C ^ 2)
      (fun n => hq.measurable.comp (ha n)) (fun n => Eventually.of_forall fun x => ?_) ?_
      (Eventually.of_forall fun x => ?_)
    · refine pow_le_pow_left' ?_ 2
      rw [← ofReal_norm_eq_enorm]
      exact ENNReal.ofReal_le_ofReal (hC n x)
    · rw [lintegral_const]
      exact ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top) (measure_ne_top _ _)
    · simpa [Function.comp_def] using (hq.tendsto 0).comp (ha0 x)
  rw [lintegral_zero] at h1
  have h2 : ∫⁻ x, ‖c x‖ₑ ^ 2 ∂ν ≤ 0 := by
    have e : ∀ x, ‖c x‖ₑ ^ 2 = liminf (fun n => ‖b n x‖ₑ ^ 2) atTop := fun x =>
      ((hq.tendsto _).comp (hbc x)).liminf_eq.symm
    simp_rw [e]
    refine (lintegral_liminf_le fun n => hq.measurable.comp (hb n)).trans ?_
    have e2 : (fun n => ∫⁻ x, ((fun z : ℂ => ‖z‖ₑ ^ 2) ∘ b n) x ∂ν) = fun n => ∫⁻ x, ‖a n x‖ₑ ^ 2 ∂ν := funext he
    rw [e2]
    exact h1.liminf_eq.le
  have h3 := (lintegral_eq_zero_iff (hq.measurable.comp hc)).1 (le_antisymm h2 zero_le')
  filter_upwards [h3] with x hx
  simpa using hx

theorem eq_zero_of_ae_fundamentalDomain {G : Type} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (Γ : AddSubgroup G) [DiscreteTopology Γ]
    (μ : Measure G) [μ.IsAddHaarMeasure] (𝓕 : Set G) (h𝓕 : IsAddFundamentalDomain Γ 𝓕 μ) (c : G → ℂ)
    (hc : Continuous c) (hp : ∀ γ ∈ Γ, ∀ w, ‖c (γ + w)‖ = ‖c w‖) (h0 : ∀ᵐ x ∂μ.restrict 𝓕, c x = 0) : c = 0 := by
  have : Countable Γ := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  have ho : IsOpen {x | c x ≠ 0} := isOpen_ne_fun hc continuous_const
  have h1 : μ {x | c x ≠ 0} = 0 := by
    refine h𝓕.measure_zero_of_invariant _ (fun g => ?_) ?_
    · ext x
      rw [Set.mem_vadd_set_iff_neg_vadd_mem]
      show c (((-g : Γ) : G) + x) ≠ 0 ↔ c x ≠ 0
      rw [← norm_ne_zero_iff, hp _ (-g).2, norm_ne_zero_iff]
    · rw [← Measure.restrict_apply ho.measurableSet]
      exact h0
  funext x
  by_contra hx
  exact (ho.measure_pos μ ⟨x, hx⟩).ne' h1

theorem tendsto_diffQuot {F : ℝ → ℂ} {d : ℂ} (h : HasDerivAt F d 0) :
    Tendsto (fun n : ℕ => ((1 / ((n : ℝ) + 1) : ℝ) : ℂ)⁻¹ * (F (1 / ((n : ℝ) + 1)) - F 0)) atTop (𝓝 d) := by
  have h1 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝[≠] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨tendsto_one_div_add_atTop_nhds_zero_nat, Eventually.of_forall fun n =>
      (Nat.one_div_pos_of_nat (n := n)).ne'⟩
  refine (h.tendsto_slope_zero.comp h1).congr fun n => ?_
  simp only [Function.comp_apply, zero_add, Complex.real_smul, Complex.ofReal_inv]

theorem norm_diffQuot_le {F F' : ℝ → ℂ} {C : ℝ} (h : ∀ s, HasDerivAt F (F' s) s) (hC : ∀ s, ‖F' s‖ ≤ C) (t : ℝ)
    (ht : t ≠ 0) : ‖(t : ℂ)⁻¹ * (F t - F 0)‖ ≤ C := by
  have h1 := convex_univ.norm_image_sub_le_of_norm_hasDerivWithin_le (f := F) (f' := F') (C := C)
    (fun s _ => (h s).hasDerivWithinAt) (fun s _ => hC s) (Set.mem_univ 0) (Set.mem_univ t)
  rw [sub_zero] at h1
  rw [norm_mul, norm_inv, Complex.norm_real, inv_mul_le_iff₀ (norm_pos_iff.2 ht), mul_comm]
  exact h1

end Abstract

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D}

theorem norm_periodic (hψ : IsStdChar D ψ (-1)) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) :
    ∀ γ ∈ ratL T S, ∀ w, ‖f (γ + w)‖ = ‖f w‖ := by
  rintro _ ⟨γ, rfl⟩ w
  have := hf.quasi γ w
  exact (congrArg norm this).trans (by rw [norm_mul, hψ.1.2.1, one_mul])

theorem exists_bound (hψ : IsStdChar D ψ (-1)) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) :
    ∃ C : ℝ, ∀ w, ‖f w‖ ≤ C := by
  obtain ⟨-, -, -, -, -, K, hK, hKc⟩ := GlobalTheory.AdelicMatrixLattice.lattice D T S
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hf.cont.continuousOn
  refine ⟨C, fun w => ?_⟩
  obtain ⟨γ, hγ, h⟩ := hKc w
  rw [← norm_periodic hψ hf γ hγ w]
  exact hC _ h

variable {χS χT : (AE D)ˣ →* Circle} {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)}

theorem om_dLine (hW : IsWeilDatumO ψ S T χS χT om) (g : GA D S) (h : GA D T) {L L' : ℝ →+ WO S T}
    (hL : Continuous L) (hL0 : ∀ t, (L t).map (finPart D) = 0) (hL' : Continuous L')
    (hL0' : ∀ t, (L' t).map (finPart D) = 0) (e : ∀ t, L' t = actO S T g h (L t)) {f : WO S T → ℂ}
    (hf : IsThetaFunO ψ S T f) : om (g, h) (dLine ψ S T L f) = dLine ψ S T L' (om (g, h) f) := by
  have hψ := hW.std
  obtain ⟨i1, i2, i3, i4, i5, K, hK, hKc⟩ := GlobalTheory.AdelicMatrixLattice.lattice D T S
  have i6 : BorelSpace (WO S T) := ⟨rfl⟩
  obtain ⟨μ, 𝓕, hμ, h𝓕, h1⟩ := (GlobalTheory.meanSquare_addFundamentalDomain_of_cocompact (WO S T) (ratL T S) K hK hKc).1
  have : IsFiniteMeasure (μ.restrict 𝓕) := ⟨by rw [Measure.restrict_apply_univ, h1]; exact ENNReal.one_lt_top⟩
  have hF := hW.om_pres (g, h) f hf
  obtain ⟨hd, hdt⟩ := hasDerivAt_zero_and_isTheta hψ hL hL0 hf
  obtain ⟨hd', hdt'⟩ := hasDerivAt_zero_and_isTheta hψ hL' hL0' hF
  obtain ⟨C, hC⟩ := exists_bound hψ hdt
  let a : ℕ → WO S T → ℂ := fun n => ((1 / ((n : ℝ) + 1) : ℝ) : ℂ)⁻¹ •
    (heisO ψ S T (L (1 / ((n : ℝ) + 1))) f - f) - dLine ψ S T L f
  have hat : ∀ n, IsThetaFunO ψ S T (a n) := fun n =>
    isTheta_sub (isTheta_smul _ (isTheta_sub (isTheta_heisO_real hψ (hL0 _) hf) hf)) hdt
  have hct : IsThetaFunO ψ S T (dLine ψ S T L' (om (g, h) f) - om (g, h) (dLine ψ S T L f)) :=
    isTheta_sub hdt' (hW.om_pres _ _ hdt)
  have ha : ∀ n x, a n x = ((1 / ((n : ℝ) + 1) : ℝ) : ℂ)⁻¹ *
      (heisO ψ S T (L (1 / ((n : ℝ) + 1))) f x - heisO ψ S T (L 0) f x) - dLine ψ S T L f x := by
    intro n x
    rw [map_zero L, heisO_zero]
    rfl
  have hb : ∀ n x, om (g, h) (a n) x = ((1 / ((n : ℝ) + 1) : ℝ) : ℂ)⁻¹ *
      (heisO ψ S T (L' (1 / ((n : ℝ) + 1))) (om (g, h) f) x - heisO ψ S T (L' 0) (om (g, h) f) x) -
        om (g, h) (dLine ψ S T L f) x := by
    intro n x
    rw [map_zero L', heisO_zero, e, ← hW.om_heis g h _ f hf, map_sub, map_smul, map_sub]
    rfl
  have key := ae_zero_of_lintegral_eq (μ.restrict 𝓕) a (fun n => om (g, h) (a n)) _ (C + C)
    (fun n => (hat n).cont.measurable) (fun n => (hW.om_pres _ _ (hat n)).cont.measurable) hct.cont.measurable
    (fun n x => by
      rw [ha]
      refine (norm_sub_le _ _).trans (add_le_add ?_ (hC x))
      refine norm_diffQuot_le (hasDerivAt_line hψ hL hL0 hf x) (fun s => ?_) _ (Nat.one_div_pos_of_nat (n := n)).ne'
      rw [heisO, norm_mul, hψ.1.2.1, one_mul]
      exact hC _)
    (fun x => by
      have := (tendsto_diffQuot (hd x)).sub_const (dLine ψ S T L f x)
      rw [sub_self] at this
      exact this.congr fun n => (ha n x).symm)
    (fun x => ((tendsto_diffQuot (hd' x)).sub_const (om (g, h) (dLine ψ S T L f) x)).congr fun n => (hb n x).symm)
    (fun n => hW.om_unit μ 𝓕 hμ h𝓕 _ _ (hat n))
  exact (sub_eq_zero.1 (eq_zero_of_ae_fundamentalDomain (ratL T S) μ 𝓕 h𝓕 _ hct.cont (norm_periodic hψ hct) key)).symm

variable {θ : InfFam D}

theorem compAt_mul (θ : InfFam D) (τ : D.what₂.Tau) {k m n : ℕ} (x : Mx D k m) (y : Mx D m n) :
    compAt θ τ (HMul.hMul x y : Mx D k n) = compAt θ τ x * compAt θ τ y :=
  Matrix.map_mul (f := (θ τ).comp (infPart D))

theorem compAt_one (θ : InfFam D) (τ : D.what₂.Tau) {k : ℕ} : compAt θ τ (1 : Mx D k k) = 1 :=
  Matrix.map_one _ (map_zero ((θ τ).comp (infPart D))) (map_one ((θ τ).comp (infPart D)))

theorem mt_mul (V : HSp D) (g g' : GA D V) : mt V (g * g') = mt V g * mt V g' := by simp [Formalism.L2.Theta.mt]

theorem mt_one (V : HSp D) : mt V 1 = 1 := by simp [Formalism.L2.Theta.mt]

theorem compAt_mt_mul_inv (θ : InfFam D) (τ : D.what₂.Tau) (V : HSp D) (g : GA D V) :
    compAt θ τ (mt V g) * compAt θ τ (mt V g⁻¹) = 1 := by
  rw [← compAt_mul, ← mt_mul, mul_inv_cancel, mt_one, compAt_one]

theorem compAt_mt_inv_mul (θ : InfFam D) (τ : D.what₂.Tau) (V : HSp D) (g : GA D V) :
    compAt θ τ (mt V g⁻¹) * compAt θ τ (mt V g) = 1 := by
  rw [← compAt_mul, ← mt_mul, inv_mul_cancel, mt_one, compAt_one]

theorem compAt_actO (θ : InfFam D) (τ : D.what₂.Tau) (g : GA D S) (h : GA D T) (x : WO S T) :
    compAt θ τ (actO S T g h x) = compAt θ τ (mt T h) * compAt θ τ x * compAt θ τ (mt S g⁻¹) := by
  unfold actO
  rw [compAt_mul, compAt_mul]

theorem actO_add (g : GA D S) (h : GA D T) (x y : WO S T) :
    actO S T g h (x + y) = actO S T g h x + actO S T g h y := by
  unfold actO
  rw [Matrix.mul_add, Matrix.add_mul]

theorem lineAt_actO (hθ : IsInfFam θ) (τ : D.what₂.Tau) (g : GA D S) (h : GA D T)
    (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) (t : ℝ) :
    lineAt θ τ (compAt θ τ (mt T h) * z * compAt θ τ (mt S g⁻¹)) t = actO S T g h (lineAt θ τ z t) := by
  obtain ⟨h1, h2, h3⟩ := isLineAt_lineAt hθ τ z
  let M : ℝ →+ WO S T := AddMonoidHom.mk' (fun t => actO S T g h (lineAt θ τ z t)) fun s t => by
    rw [map_add, actO_add]
  have hM : IsLineAt θ τ (compAt θ τ (mt T h) * z * compAt θ τ (mt S g⁻¹)) M := by
    refine ⟨(continuous_const.matrix_mul h1).matrix_mul continuous_const, fun t => ?_, fun t τ' => ?_⟩
    · show (actO S T g h (lineAt θ τ z t)).map (finPart D) = 0
      unfold actO
      rw [Matrix.map_mul, Matrix.map_mul, h2, Matrix.mul_zero, Matrix.zero_mul]
    · show compAt θ τ' (actO S T g h (lineAt θ τ z t)) = _
      rw [compAt_actO, h3]
      split_ifs with hτ
      · rw [hτ, Matrix.mul_smul, Matrix.smul_mul]
      · rw [Matrix.mul_zero, Matrix.zero_mul]
  rw [GlobalTheory.RealLineAt.lineAt_unique D θ hθ _ _ τ _ _ _ (isLineAt_lineAt hθ τ _) hM]
  rfl

theorem om_dRho (hW : IsWeilDatumO ψ S T χS χT om) (hθ : IsInfFam θ) (g : GA D S) (h : GA D T) (τ : D.what₂.Tau)
    (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) :
    om (g, h) (Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ z f) =
      Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ (compAt θ τ (mt T h) * z * compAt θ τ (mt S g⁻¹)) (om (g, h) f) :=
  om_dLine hW g h (isLineAt_lineAt hθ τ z).1 (isLineAt_lineAt hθ τ z).2.1 (isLineAt_lineAt hθ τ _).1
    (isLineAt_lineAt hθ τ _).2.1 (lineAt_actO hθ τ g h z) hf

theorem cplxO_move (θ : InfFam D) (τ : D.what₂.Tau) (g : GA D S) (h : GA D T)
    {sS sS' : Matrix (Fin S.rank) (Fin S.rank) ℂ} {sT sT' : Matrix (Fin T.rank) (Fin T.rank) ℂ}
    (hS : sS' * compAt θ τ (mt S g) = compAt θ τ (mt S g) * sS)
    (hT : sT' * compAt θ τ (mt T h) = compAt θ τ (mt T h) * sT) (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) :
    cplxO sS' sT' (compAt θ τ (mt T h) * z * compAt θ τ (mt S g⁻¹)) =
      compAt θ τ (mt T h) * cplxO sS sT z * compAt θ τ (mt S g⁻¹) := by
  have h1 : compAt θ τ (mt S g⁻¹) * sS' = sS * compAt θ τ (mt S g⁻¹) := by
    calc _ = compAt θ τ (mt S g⁻¹) * (sS' * compAt θ τ (mt S g)) * compAt θ τ (mt S g⁻¹) := by
          rw [Matrix.mul_assoc, Matrix.mul_assoc, compAt_mt_mul_inv, Matrix.mul_one]
      _ = _ := by rw [hS, ← Matrix.mul_assoc, compAt_mt_inv_mul, Matrix.one_mul]
  unfold cplxO
  rw [Matrix.mul_smul, Matrix.smul_mul]
  congr 1
  calc _ = (sT' * compAt θ τ (mt T h)) * z * (compAt θ τ (mt S g⁻¹) * sS') := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [hT, h1]; simp only [Matrix.mul_assoc]

end GlobalTheory.WeilVacMove

end
