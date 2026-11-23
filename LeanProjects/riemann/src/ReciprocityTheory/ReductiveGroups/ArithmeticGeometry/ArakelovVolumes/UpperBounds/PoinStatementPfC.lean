import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.PoinStatementPfB

namespace ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ENNReal Matrix

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

def Bset (X : Data E r) (x : Frame X.Ψ r) (ρ : ℝ) : Set (V (nd X)) :=
  {w | ‖w‖ < ρ ∧ cpt X x w ∈ X.dom}

def SubMeanStatement : Prop :=
  ∀ (r : ℕ) (X : Data E r) (la : Wt X.Ψ r) (ρ : ℝ), 0 < ρ → ρ ≤ 1 → ∃ C : ℝ≥0∞, C < ⊤ ∧
    ∀ P : Frame X.Ψ r → ℂ, DifferentiableOn ℂ P X.dom → ∀ x ∈ X.dom, IsOrth X x →
      ‖P x‖ₑ ^ 2 ≤ C * ∫⁻ w in Bset X x ρ,
        ‖P (cpt X x w)‖ₑ ^ 2 * ENNReal.ofReal (Real.exp (-phla X la (cpt X x w)))

def SubMeanLocStatement : Prop :=
  ∀ (r : ℕ) (X : Data E r) (la : Wt X.Ψ r) (ρ : ℝ), 0 < ρ → ρ ≤ 1 → ∀ x ∈ X.dom, IsOrth X x →
    ∃ ε > 0, ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ P : Frame X.Ψ r → ℂ, IsBEq X la P → ∀ y ∈ Metric.ball x ε,
      ‖P y‖ₑ ^ 2 ≤ C * ∫⁻ w in Bset X x ρ,
        ‖P (cpt X x w)‖ₑ ^ 2 * ENNReal.ofReal (Real.exp (-phla X la (cpt X x w)))

def SumBallStatement : Prop :=
  ∀ (r : ℕ) (X : Data E r) (x0 : Frame X.Ψ r) (la : Wt X.Ψ r) (W : Frame X.Ψ r → ℝ≥0∞) (bb : ℝ)
    (F : V (nd X) → ℂ) (P : Frame X.Ψ r → ℂ), Hyp X x0 la W bb F P →
    ∃ ρ0 : ℝ, 0 < ρ0 ∧ ρ0 ≤ 1 ∧ ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ x ∈ X.dom, IsOrth X x →
      ∑' γ : X.Γ, (∫⁻ w in Bset X x ρ0,
        ‖P (lact γ.1 (cpt X x w))‖ₑ ^ 2 * W (lact γ.1 (cpt X x w))) ^ (1 / 2 : ℝ) ≤ C

theorem cont_cpt' (X : Data E r) (x0 : Frame X.Ψ r) : Continuous (cpt X x0) := by
  unfold cpt
  refine continuous_pi fun τ => ?_
  have hn : Continuous fun z : V (nd X) => mat (nmat X z) τ := by
    refine continuous_pi fun a => continuous_pi fun b => ?_
    simp only [mat, nmat, Matrix.of_apply]
    split_ifs
    · first
        | fun_prop
        | exact (EuclideanSpace.proj _).continuous
        | exact PiLp.continuous_apply _ _ _
        | continuity
    · exact continuous_const
    · exact continuous_const
  exact continuous_const.matrix_mul hn

private theorem gram_continuous_comp {α : Type*} [TopologicalSpace α] (τ : E →+* ℂ)
    (G : Matrix (Fin r) (Fin r) E) {f : α → Matrix (Fin r) (Fin r) ℂ} (hf : Continuous f) :
    Continuous fun a => ReciprocityTheory.ChartRestriction.G.FD.gram τ G (f a) := by
  refine continuous_pi fun a => continuous_pi fun b => ?_
  simp only [ReciprocityTheory.ChartRestriction.G.FD.gram, ReciprocityTheory.ChartRestriction.G.FD.hermC, ReciprocityTheory.ChartRestriction.G.FD.col,
    Matrix.of_apply]
  refine continuous_finset_sum _ fun k _ => continuous_finset_sum _ fun l _ => ?_
  refine ((hf.matrix_elem k a).mul continuous_const).mul ?_
  first
    | exact Complex.continuous_conj.comp (hf.matrix_elem l b)
    | exact (hf.matrix_elem l b).star
    | fun_prop

theorem isOpen_Bset (X : Data E r) (x : Frame X.Ψ r) (ρ : ℝ) : IsOpen (Bset X x ρ) := by
  have hdom : IsOpen X.dom := by
    have he : X.dom = ⋂ τ : X.Ψ, ({y : Frame X.Ψ r | (mat y τ).det ≠ 0} ∩
        ⋂ i : Fin (r + 1), {y : Frame X.Ψ r | 0 < psgn X.p0 i * (dmin X.Gm y τ i).re}) := by
      ext y
      simp only [Data.dom, GG, Set.mem_setOf_eq, Set.mem_iInter, Set.mem_inter_iff]
    rw [he]
    refine isOpen_iInter_of_finite fun τ => IsOpen.inter ?_ (isOpen_iInter_of_finite fun i => ?_)
    · have hmat : Continuous fun y : Frame X.Ψ r => mat y τ := by
        first
          | exact continuous_apply τ
          | (unfold mat; exact continuous_apply τ)
          | fun_prop
      exact isOpen_ne_fun hmat.matrix_det continuous_const
    · have hmat : Continuous fun y : Frame X.Ψ r => mat y τ := by
        first
          | exact continuous_apply τ
          | (unfold mat; exact continuous_apply τ)
          | fun_prop
      have hdm : Continuous fun y : Frame X.Ψ r => dmin X.Gm y τ i := by
        unfold dmin lminor
        exact ((gram_continuous_comp τ.1 X.Gm hmat).matrix_submatrix _ _).matrix_det
      exact isOpen_lt continuous_const (continuous_const.mul (Complex.continuous_re.comp hdm))
  have hB : Bset X x ρ = {w : V (nd X) | ‖w‖ < ρ} ∩ cpt X x ⁻¹' X.dom := by
    ext w
    rfl
  rw [hB]
  exact (isOpen_lt continuous_norm continuous_const).inter (hdom.preimage (cont_cpt' X x))

theorem pow_half_sq (t : ℝ≥0∞) : (t ^ (1 / 2 : ℝ)) ^ 2 = t := by
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  norm_num

theorem sq_pow_half (t : ℝ≥0∞) : (t ^ 2) ^ (1 / 2 : ℝ) = t := by
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  norm_num

end

end ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf

namespace ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ENNReal Matrix

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem supR_ne_top (X : Data E r) (la : Wt X.Ψ r) (W : Frame X.Ψ r → ℝ≥0∞) {c : ℝ} (hc : 0 < c)
    (hcW : ∀ x ∈ X.dom, ENNReal.ofReal (c * Real.exp (-phla X la x)) ≤ W x) (ρ : ℝ) (x : Frame X.Ψ r) :
    supR X la W ρ x ≠ ⊤ := by
  unfold supR
  apply ne_top_of_le_ne_top (ENNReal.rpow_ne_top_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (ENNReal.inv_ne_top.mpr (ENNReal.ofReal_pos.mpr hc).ne'))
  refine iSup_le fun z => iSup_le fun _ => iSup_le fun hz => ?_
  refine ENNReal.rpow_le_rpow ?_ (by norm_num)
  have hW := hcW _ hz
  rw [ENNReal.ofReal_mul hc.le] at hW
  have he : ENNReal.ofReal (Real.exp (-phla X la (cpt X x z))) ≠ 0 :=
    (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne'
  have heT : ENNReal.ofReal (Real.exp (-phla X la (cpt X x z))) ≠ ⊤ := ENNReal.ofReal_ne_top
  set e := ENNReal.ofReal (Real.exp (-phla X la (cpt X x z)))
  calc e / W (cpt X x z) ≤ e / (ENNReal.ofReal c * e) := ENNReal.div_le_div_left hW _
    _ = 1 * e / (ENNReal.ofReal c * e) := by rw [one_mul]
    _ = 1 / ENNReal.ofReal c := ENNReal.mul_div_mul_right _ _ he heT
    _ = (ENNReal.ofReal c)⁻¹ := one_div _

private theorem apply_cc_eq_starRingEnd_apply (τ : E →+* ℂ) (z : E) : τ (cc z) = starRingEnd ℂ (τ z) := by
  unfold cc
  first
    | exact NumberField.IsCMField.complexEmbedding_complexConj τ z
    | exact NumberField.IsCMField.complexEmbedding_complexConj E τ z
    | exact NumberField.IsCMField.complexEmbedding_complexConj (K := E) τ z
    | simp

private theorem gram_eq_transpose_mul_mul_map_conj (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (M : Matrix (Fin r) (Fin r) ℂ) :
    ReciprocityTheory.ChartRestriction.G.FD.gram τ G M = M.transpose * G.map τ * M.map (starRingEnd ℂ) := by
  ext a b
  simp only [ReciprocityTheory.ChartRestriction.G.FD.gram, ReciprocityTheory.ChartRestriction.G.FD.hermC, ReciprocityTheory.ChartRestriction.G.FD.col, Matrix.of_apply,
    Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Finset.sum_mul]
  all_goals rw [Finset.sum_comm]

private theorem transpose_mul_mul_map_cc_eq_of_isUStab' {γ : GL (Fin r) E} {G : Matrix (Fin r) (Fin r) E}
    {Λ : Submodule (𝓞 E) (Fin r → E)} (h : IsUStab G Λ γ) :
    (γ : Matrix (Fin r) (Fin r) E).transpose * G * (γ : Matrix (Fin r) (Fin r) E).map cc = G := by
  ext p q
  have hcs : ∀ b, cc ((Pi.single q (1 : E) : Fin r → E) b) = (Pi.single q (1 : E) : Fin r → E) b := by
    intro b
    by_cases hb : b = q
    · subst hb
      simp [cc]
    · simp [cc, hb, Pi.single_apply]
  have hv : ∀ (j a : Fin r), ((γ : Matrix (Fin r) (Fin r) E) *ᵥ (Pi.single j (1 : E) : Fin r → E)) a =
      (γ : Matrix (Fin r) (Fin r) E) a j := by
    intro j a
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  have h2 : ∑ a, ∑ b, (Pi.single p (1 : E) : Fin r → E) a * G a b * (Pi.single q (1 : E) : Fin r → E) b =
      G p q := by
    simp [Pi.single_apply]
  have h1 := h.1 (Pi.single p (1 : E) : Fin r → E) (Pi.single q (1 : E) : Fin r → E)
  simp only [herm, hv, hcs] at h1
  rw [h2] at h1
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact h1

private theorem gram_mat_lact (X : Data E r) {γ : GL (Fin r) E} (hγ : γ ∈ X.Γ) (x : Frame X.Ψ r)
    (τ : X.Ψ) : ReciprocityTheory.ChartRestriction.G.FD.gram τ.1 X.Gm (mat (lact γ x) τ) = ReciprocityTheory.ChartRestriction.G.FD.gram τ.1 X.Gm (mat x τ) := by
  have hU := transpose_mul_mul_map_cc_eq_of_isUStab' (X.Γ_stab γ hγ)
  have hA : ((γ : Matrix (Fin r) (Fin r) E).map τ.1).map (starRingEnd ℂ) =
      ((γ : Matrix (Fin r) (Fin r) E).map cc).map τ.1 := by
    ext a b
    simp only [Matrix.map_apply]
    exact (apply_cc_eq_starRingEnd_apply τ.1 _).symm
  have hm : mat (lact γ x) τ = (γ : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ := rfl
  have hU' : ((γ : Matrix (Fin r) (Fin r) E).map τ.1).transpose * X.Gm.map τ.1 *
      ((γ : Matrix (Fin r) (Fin r) E).map cc).map τ.1 = X.Gm.map τ.1 := by
    rw [← Matrix.transpose_map, ← Matrix.map_mul, ← Matrix.map_mul, hU]
  have key : ∀ Y : Matrix (Fin r) (Fin r) ℂ, ((γ : Matrix (Fin r) (Fin r) E).map τ.1).transpose *
      (X.Gm.map τ.1 * (((γ : Matrix (Fin r) (Fin r) E).map cc).map τ.1 * Y)) = X.Gm.map τ.1 * Y := by
    intro Y
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hU']
  rw [gram_eq_transpose_mul_mul_map_conj, gram_eq_transpose_mul_mul_map_conj, hm, Matrix.transpose_mul, Matrix.map_mul, hA]
  simp only [Matrix.mul_assoc]
  rw [key]

private theorem lact_mem_dom_of_mem_Γ (X : Data E r) {γ : GL (Fin r) E} (hγ : γ ∈ X.Γ) {x : Frame X.Ψ r}
    (hx : x ∈ X.dom) : lact γ x ∈ X.dom := by
  simp only [Data.dom, GG, Set.mem_setOf_eq] at hx ⊢
  intro τ
  obtain ⟨h1, h2⟩ := hx τ
  refine ⟨?_, fun i => ?_⟩
  · show ((γ : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ).det ≠ 0
    rw [Matrix.det_mul]
    refine mul_ne_zero ?_ h1
    have hd : ((γ : Matrix (Fin r) (Fin r) E).map τ.1).det = τ.1 (γ : Matrix (Fin r) (Fin r) E).det :=
      (RingHom.map_det τ.1 _).symm
    rw [hd]
    exact (map_ne_zero τ.1).mpr ((Matrix.isUnit_iff_isUnit_det _).mp γ.isUnit).ne_zero
  · have hd : dmin X.Gm (lact γ x) τ i = dmin X.Gm x τ i := by
      unfold dmin
      rw [gram_mat_lact X hγ x τ]
    rw [hd]
    exact h2 i

private theorem differentiable_lact_upper_bounds (X : Data E r) (γ : GL (Fin r) E) :
    Differentiable ℂ (fun y : Frame X.Ψ r => lact γ y) := by
  refine differentiable_pi.mpr fun τ => differentiable_pi.mpr fun a =>
    differentiable_pi.mpr fun b => ?_
  simp only [lact, mat, Matrix.mul_apply, Matrix.of_apply]
  first
    | fun_prop
    | exact Differentiable.sum fun k _ => ((differentiable_apply b).comp
        ((differentiable_apply k).comp (differentiable_apply τ))).const_mul _

theorem key_int (X : Data E r) (la : Wt X.Ψ r) (W : Frame X.Ψ r → ℝ≥0∞) (hW : IsMetricW X la W)
    {c : ℝ} (hc : 0 < c) (hcW : ∀ x ∈ X.dom, ENNReal.ofReal (c * Real.exp (-phla X la x)) ≤ W x)
    (P : Frame X.Ψ r → ℂ) (hP : DifferentiableOn ℂ P X.dom) {x : Frame X.Ψ r} {ρ : ℝ}
    {γ : GL (Fin r) E} (hγ : γ ∈ X.Γ)
    (hI : ∫⁻ w in Bset X x ρ, ‖P (lact γ (cpt X x w))‖ₑ ^ 2 * W (lact γ (cpt X x w)) ≠ ⊤) :
    ∫⁻ w in Bset X x ρ, ‖P (lact γ (cpt X x w))‖ₑ ^ 2 *
        ENNReal.ofReal (Real.exp (-phla X la (cpt X x w))) ≤
      supR X la W ρ x ^ 2 * ∫⁻ w in Bset X x ρ, ‖P (lact γ (cpt X x w))‖ₑ ^ 2 * W (lact γ (cpt X x w)) := by
  unfold IsMetricW at hW
  have hS : supR X la W ρ x ≠ ⊤ := supR_ne_top X la W hc hcW ρ x
  rw [← lintegral_const_mul' _ _ (ENNReal.pow_ne_top hS)]
  have hBm : MeasurableSet (Bset X x ρ) := (isOpen_Bset X x ρ).measurableSet
  have hgc : Continuous fun w => lact γ (cpt X x w) :=
    (differentiable_lact_upper_bounds X γ).continuous.comp (cont_cpt' X x)
  have hmaps : ∀ w ∈ Bset X x ρ, lact γ (cpt X x w) ∈ X.dom := fun w hw =>
    lact_mem_dom_of_mem_Γ X hγ (show ‖w‖ < ρ ∧ cpt X x w ∈ X.dom from hw).2
  have hPc : ContinuousOn (fun w => P (lact γ (cpt X x w))) (Bset X x ρ) :=
    hP.continuousOn.comp hgc.continuousOn hmaps
  have hmeas : AEMeasurable (fun w => ‖P (lact γ (cpt X x w))‖ₑ ^ 2 * W (lact γ (cpt X x w)))
      (volume.restrict (Bset X x ρ)) :=
    ((hPc.aemeasurable hBm).enorm.pow_const 2).mul (hW.1.comp hgc.measurable).aemeasurable
  have hfin := ae_lt_top' hmeas hI
  refine lintegral_mono_ae ?_
  filter_upwards [hfin, ae_restrict_mem hBm] with w hw hwB
  have hwB' : ‖w‖ < ρ ∧ cpt X x w ∈ X.dom := hwB
  have hy : cpt X x w ∈ X.dom := hwB'.2
  have hWγ : W (lact γ (cpt X x w)) = W (cpt X x w) := hW.2.2 γ hγ _ hy
  rw [hWγ] at hw ⊢
  have hW0 : W (cpt X x w) ≠ 0 := by
    have h1 := hcW _ hy
    intro h0
    rw [h0] at h1
    have h2 : (0 : ℝ≥0∞) < ENNReal.ofReal (c * Real.exp (-phla X la (cpt X x w))) :=
      ENNReal.ofReal_pos.mpr (mul_pos hc (Real.exp_pos _))
    exact absurd h1 (not_le.mpr h2)
  have h1 : (ENNReal.ofReal (Real.exp (-phla X la (cpt X x w))) / W (cpt X x w)) ^ (1 / 2 : ℝ) ≤
      supR X la W ρ x := by
    unfold supR
    exact le_iSup_of_le w (le_iSup_of_le hwB'.1 (le_iSup_of_le hy le_rfl))
  set f := ‖P (lact γ (cpt X x w))‖ₑ ^ 2
  set e := ENNReal.ofReal (Real.exp (-phla X la (cpt X x w)))
  by_cases hf0 : f = 0
  · rw [hf0]
    simp
  · have hWT : W (cpt X x w) ≠ ⊤ := by
      intro hT
      rw [hT, ENNReal.mul_top hf0] at hw
      exact lt_irrefl _ hw
    have hle : e / W (cpt X x w) ≤ supR X la W ρ x ^ 2 := by
      calc e / W (cpt X x w) = ((e / W (cpt X x w)) ^ (1 / 2 : ℝ)) ^ 2 := (pow_half_sq _).symm
        _ ≤ supR X la W ρ x ^ 2 := by
          first
            | exact pow_le_pow_left' h1 2
            | exact pow_le_pow_left₀ (zero_le _) h1 2
            | gcongr
    have he : e ≤ supR X la W ρ x ^ 2 * W (cpt X x w) := by
      calc e = e / W (cpt X x w) * W (cpt X x w) := (ENNReal.div_mul_cancel hW0 hWT).symm
        _ ≤ supR X la W ρ x ^ 2 * W (cpt X x w) := by gcongr
    calc f * e ≤ f * (supR X la W ρ x ^ 2 * W (cpt X x w)) := by gcongr
      _ = supR X la W ρ x ^ 2 * (f * W (cpt X x w)) := by ring

theorem supR_mono (X : Data E r) (la : Wt X.Ψ r) (W : Frame X.Ψ r → ℝ≥0∞) {ρ ρ' : ℝ} (h : ρ' ≤ ρ)
    (x : Frame X.Ψ r) : supR X la W ρ' x ≤ supR X la W ρ x := by
  unfold supR
  refine iSup_mono fun z => ?_
  refine iSup_le fun hz => ?_
  exact le_iSup_of_le (lt_of_lt_of_le hz h) le_rfl

theorem Bset_mono (X : Data E r) (x : Frame X.Ψ r) {ρ ρ' : ℝ} (h : ρ' ≤ ρ) :
    Bset X x ρ' ⊆ Bset X x ρ := by
  intro w hw
  simp only [Bset, Set.mem_setOf_eq] at hw ⊢
  exact ⟨lt_of_lt_of_le hw.1 h, hw.2⟩

theorem ball_of (hA : SubMeanStatement (E := E)) (hS : SumBallStatement (E := E)) :
    BallStatement (E := E) := by
  intro r X x0 la W bb F P hH ρ hρ hρ1
  have hH' := hH
  unfold Hyp at hH'
  obtain ⟨_, _, hMW, hWL, _, _, _, hBE, _⟩ := hH'
  unfold WLower at hWL
  obtain ⟨c, hc, hcW⟩ := hWL
  have hBE2 := hBE
  unfold IsBEq at hBE2
  have hPd : DifferentiableOn ℂ P X.dom := hBE2.1
  obtain ⟨ρ0, hρ0, hρ01, CS, hCS, hsum⟩ := hS r X x0 la W bb F P hH
  obtain ⟨ρ', hρ'd⟩ : ∃ ρ' : ℝ, ρ' = min ρ ρ0 := ⟨_, rfl⟩
  have hρ'ρ : ρ' ≤ ρ := hρ'd ▸ min_le_left _ _
  have hρ'ρ0 : ρ' ≤ ρ0 := hρ'd ▸ min_le_right _ _
  have hρ'0 : 0 < ρ' := hρ'd ▸ lt_min hρ hρ0
  have hρ'1 : ρ' ≤ 1 := hρ'ρ.trans hρ1
  obtain ⟨CA, hCA, hsub⟩ := hA r X la ρ' hρ'0 hρ'1
  refine ⟨(CA ^ (1 / 2 : ℝ) * CS).toReal, fun x hx hxo => ?_⟩
  rw [ENNReal.ofReal_toReal (ENNReal.mul_ne_top
    (ENNReal.rpow_ne_top_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) hCA.ne) hCS.ne)]
  have hpt : ∀ γ : X.Γ, ‖P (lact γ.1 x)‖ₑ ≤ CA ^ (1 / 2 : ℝ) * supR X la W ρ x *
      (∫⁻ w in Bset X x ρ0, ‖P (lact γ.1 (cpt X x w))‖ₑ ^ 2 * W (lact γ.1 (cpt X x w))) ^ (1 / 2 : ℝ) := by
    intro γ
    have hdγ : DifferentiableOn ℂ (fun y => P (lact γ.1 y)) X.dom :=
      hPd.comp (differentiable_lact_upper_bounds X γ.1).differentiableOn (fun y hy => lact_mem_dom_of_mem_Γ X γ.2 hy)
    have h1 : ‖P (lact γ.1 x)‖ₑ ^ 2 ≤ CA * ∫⁻ w in Bset X x ρ', ‖P (lact γ.1 (cpt X x w))‖ₑ ^ 2 *
        ENNReal.ofReal (Real.exp (-phla X la (cpt X x w))) :=
      hsub (fun y => P (lact γ.1 y)) hdγ x hx hxo
    have hfin0 : ∫⁻ w in Bset X x ρ0, ‖P (lact γ.1 (cpt X x w))‖ₑ ^ 2 * W (lact γ.1 (cpt X x w)) ≠ ⊤ := by
      have ht : (∫⁻ w in Bset X x ρ0, ‖P (lact γ.1 (cpt X x w))‖ₑ ^ 2 * W (lact γ.1 (cpt X x w))) ^ (1 / 2 : ℝ) ≠ ⊤ :=
        ne_top_of_le_ne_top hCS.ne ((ENNReal.le_tsum γ).trans (hsum x hx hxo))
      intro hT
      apply ht
      rw [hT]
      exact ENNReal.top_rpow_of_pos (by norm_num)
    have hmonoI : ∫⁻ w in Bset X x ρ', ‖P (lact γ.1 (cpt X x w))‖ₑ ^ 2 * W (lact γ.1 (cpt X x w)) ≤ ∫⁻ w in Bset X x ρ0, ‖P (lact γ.1 (cpt X x w))‖ₑ ^ 2 * W (lact γ.1 (cpt X x w)) := lintegral_mono_set (Bset_mono X x hρ'ρ0)
    have hfin' : ∫⁻ w in Bset X x ρ', ‖P (lact γ.1 (cpt X x w))‖ₑ ^ 2 * W (lact γ.1 (cpt X x w)) ≠ ⊤ := ne_top_of_le_ne_top hfin0 hmonoI
    have h2 := key_int X la W hMW hc hcW P hPd γ.2 hfin'
    have hsm : supR X la W ρ' x ≤ supR X la W ρ x := supR_mono X la W hρ'ρ x
    set I0 := ∫⁻ w in Bset X x ρ0, ‖P (lact γ.1 (cpt X x w))‖ₑ ^ 2 * W (lact γ.1 (cpt X x w))
    set I1 := ∫⁻ w in Bset X x ρ', ‖P (lact γ.1 (cpt X x w))‖ₑ ^ 2 * W (lact γ.1 (cpt X x w))
    have h3 : ‖P (lact γ.1 x)‖ₑ ^ 2 ≤ CA * (supR X la W ρ x ^ 2 * I0) := by
      refine h1.trans ?_
      calc CA * ∫⁻ w in Bset X x ρ', ‖P (lact γ.1 (cpt X x w))‖ₑ ^ 2 *
            ENNReal.ofReal (Real.exp (-phla X la (cpt X x w)))
          ≤ CA * (supR X la W ρ' x ^ 2 * I1) := by gcongr
        _ ≤ CA * (supR X la W ρ x ^ 2 * I0) := by gcongr
    calc ‖P (lact γ.1 x)‖ₑ = (‖P (lact γ.1 x)‖ₑ ^ 2) ^ (1 / 2 : ℝ) := (sq_pow_half _).symm
      _ ≤ (CA * (supR X la W ρ x ^ 2 * I0)) ^ (1 / 2 : ℝ) := ENNReal.rpow_le_rpow h3 (by norm_num)
      _ = CA ^ (1 / 2 : ℝ) * supR X la W ρ x * I0 ^ (1 / 2 : ℝ) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ENNReal.mul_rpow_of_nonneg _ _ (by norm_num),
          sq_pow_half, mul_assoc]
  calc ∑' γ : X.Γ, ‖P (lact γ.1 x)‖ₑ
      ≤ ∑' γ : X.Γ, CA ^ (1 / 2 : ℝ) * supR X la W ρ x * (∫⁻ w in Bset X x ρ0, ‖P (lact γ.1 (cpt X x w))‖ₑ ^ 2 * W (lact γ.1 (cpt X x w))) ^ (1 / 2 : ℝ) := by
        first
          | exact ENNReal.tsum_le_tsum hpt
          | exact ENNReal.tsum_mono hpt
          | exact tsum_mono ENNReal.summable ENNReal.summable hpt
    _ = CA ^ (1 / 2 : ℝ) * supR X la W ρ x * ∑' γ : X.Γ, (∫⁻ w in Bset X x ρ0, ‖P (lact γ.1 (cpt X x w))‖ₑ ^ 2 * W (lact γ.1 (cpt X x w))) ^ (1 / 2 : ℝ) :=
        ENNReal.tsum_mul_left
    _ ≤ CA ^ (1 / 2 : ℝ) * supR X la W ρ x * CS := by
        gcongr
        exact hsum x hx hxo
    _ = CA ^ (1 / 2 : ℝ) * CS * supR X la W ρ x := by ring

end

end ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf

namespace ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ENNReal Matrix

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem bchar_ne (X : Data E r) (la : Wt X.Ψ r) {b : Frame X.Ψ r} (hb : b ∈ Bor X.Ψ r) :
    bchar la b ≠ 0 := by
  simp only [Bor, Set.mem_setOf_eq] at hb
  unfold bchar
  refine Finset.prod_ne_zero_iff.mpr fun τ _ => Finset.prod_ne_zero_iff.mpr fun i _ => zpow_ne_zero _ ?_
  obtain ⟨hd, ht⟩ := hb τ
  have hT : Matrix.BlockTriangular (mat b τ) id := by
    intro a c h
    exact ht a c h
  rw [Matrix.det_of_upperTriangular hT] at hd
  exact (Finset.prod_ne_zero_iff.mp hd) i (Finset.mem_univ _)

theorem isBEq_lact (X : Data E r) (la : Wt X.Ψ r) {P : Frame X.Ψ r → ℂ} (hP : IsBEq X la P)
    {γ : GL (Fin r) E} (hγ : γ ∈ X.Γ) : IsBEq X la (fun y => P (lact γ y)) := by
  unfold IsBEq at hP ⊢
  obtain ⟨hPd, hPe⟩ := hP
  refine ⟨?_, fun x hx b hb => ?_⟩
  · exact hPd.comp (differentiable_lact_upper_bounds X γ).differentiableOn (fun y hy => lact_mem_dom_of_mem_Γ X hγ hy)
  · have hl : lact γ (rmul x b) = rmul (lact γ x) b := by
      funext τ
      exact (Matrix.mul_assoc ((γ : Matrix (Fin r) (Fin r) E).map τ.1) (mat x τ) (mat b τ)).symm
    simp only [hl]
    exact hPe (lact γ x) (lact_mem_dom_of_mem_Γ X hγ hx) b hb

theorem loc_of (hA : SubMeanLocStatement (E := E)) (hS : SumBallStatement (E := E)) :
    LocStatement (E := E) := by
  intro r X x0 la W bb F P H x hx
  obtain ⟨ρ0, hρ0, hρ01, CB, hCB, hS'⟩ := hS r X x0 la W bb F P H
  obtain ⟨-, -, hW, ⟨c, hc, hcW⟩, -, -, -, hP, -⟩ := H
  set b0 := FrameDegreeData.bOf X x with hb0def
  have hb0 : b0 ∈ Bor X.Ψ r := FrameDegreeData.bOf_mem X hx
  have ho : IsOrth X (rmul x b0) := FrameDegreeData.ortho_bOf X hx
  have hx1 : rmul x b0 ∈ X.dom := rmulDom X hb0 hx
  obtain ⟨ε, hε, CA, hCA, hA'⟩ := hA r X la ρ0 hρ0 hρ01 _ hx1 ho
  have hcont : Continuous fun y : Frame X.Ψ r => rmul y b0 := by
    refine continuous_pi fun τ => continuous_pi fun a => continuous_pi fun b => ?_
    simp only [rmul, mat, Matrix.mul_apply, Matrix.of_apply]
    fun_prop
  obtain ⟨ε1, hε1, h1⟩ := Metric.continuousAt_iff.1 hcont.continuousAt ε hε
  obtain ⟨ε2, hε2, h2⟩ := Metric.isOpen_iff.1 (isOpenDom X) x hx
  set x1 := rmul x b0 with hx1def
  set I : X.Γ → ℝ≥0∞ := fun γ => ∫⁻ w in Bset X x1 ρ0,
    ‖P (lact γ.1 (cpt X x1 w))‖ₑ ^ 2 * W (lact γ.1 (cpt X x1 w)) with hIdef
  set K : ℝ≥0∞ := (CA * ENNReal.ofReal (1 / c)) ^ (1 / 2 : ℝ) with hKdef
  have hK : K ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg (by norm_num) (ENNReal.mul_ne_top hCA.ne ENNReal.ofReal_ne_top)
  have hsumfin : ∑' γ, K * I γ ^ (1 / 2 : ℝ) ≠ ⊤ := by
    rw [ENNReal.tsum_mul_left]
    exact ENNReal.mul_ne_top hK (ne_top_of_le_ne_top hCB.ne (hS' _ hx1 ho))
  refine ⟨min ε1 ε2, lt_min hε1 hε2, fun γ => (K * I γ ^ (1 / 2 : ℝ)).toReal / ‖bchar la b0‖,
    (ENNReal.summable_toReal hsumfin).div_const _, fun γ y hy => ?_⟩
  have hyd : y ∈ X.dom := h2 (Metric.ball_subset_ball (min_le_right _ _) hy)
  have hyb : rmul y b0 ∈ Metric.ball x1 ε := h1 (Metric.ball_subset_ball (min_le_left _ _) hy)
  have hA1 := hA' _ (isBEq_lact X la hP γ.2) _ hyb
  have hint : ∫⁻ w in Bset X x1 ρ0, ‖P (lact γ.1 (cpt X x1 w))‖ₑ ^ 2 *
      ENNReal.ofReal (Real.exp (-phla X la (cpt X x1 w))) ≤ ENNReal.ofReal (1 / c) * I γ := by
    rw [hIdef, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine setLIntegral_mono' (isOpen_Bset X _ ρ0).measurableSet fun w hw => ?_
    rw [hW.2.2 γ.1 γ.2 _ hw.2]
    have he : ENNReal.ofReal (Real.exp (-phla X la (cpt X x1 w))) ≤
        ENNReal.ofReal (1 / c) * W (cpt X x1 w) := by
      calc ENNReal.ofReal (Real.exp (-phla X la (cpt X x1 w)))
          = ENNReal.ofReal (1 / c) * ENNReal.ofReal (c * Real.exp (-phla X la (cpt X x1 w))) := by
            rw [← ENNReal.ofReal_mul (by positivity)]; congr 1; field_simp
        _ ≤ _ := mul_le_mul_of_nonneg_left (hcW _ hw.2) zero_le
    calc ‖P (lact γ.1 (cpt X x1 w))‖ₑ ^ 2 * ENNReal.ofReal (Real.exp (-phla X la (cpt X x1 w)))
        ≤ ‖P (lact γ.1 (cpt X x1 w))‖ₑ ^ 2 * (ENNReal.ofReal (1 / c) * W (cpt X x1 w)) :=
          mul_le_mul_of_nonneg_left he zero_le
      _ = _ := by ring
  have hB : ‖P (lact γ.1 (rmul y b0))‖ₑ ≤ K * I γ ^ (1 / 2 : ℝ) := by
    have h3 : ‖P (lact γ.1 (rmul y b0))‖ₑ ^ 2 ≤ CA * (ENNReal.ofReal (1 / c) * I γ) :=
      hA1.trans (mul_le_mul_of_nonneg_left hint zero_le)
    calc ‖P (lact γ.1 (rmul y b0))‖ₑ = (‖P (lact γ.1 (rmul y b0))‖ₑ ^ 2) ^ (1 / 2 : ℝ) :=
          (sq_pow_half _).symm
      _ ≤ (CA * (ENNReal.ofReal (1 / c) * I γ)) ^ (1 / 2 : ℝ) := ENNReal.rpow_le_rpow h3 (by norm_num)
      _ = _ := by rw [← mul_assoc, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
  have heq : P (lact γ.1 (rmul y b0)) = bchar la b0 * P (lact γ.1 y) := by
    rw [lact_rmul', hP.2 _ (lactDom X γ.2 hyd) b0 hb0]
  have hbn : 0 < ‖bchar la b0‖ := norm_pos_iff.2 (bchar_ne X la hb0)
  rw [le_div_iff₀ hbn, mul_comm, ← norm_mul, ← heq]
  have hfin : K * I γ ^ (1 / 2 : ℝ) ≠ ⊤ := ne_top_of_le_ne_top hsumfin (ENNReal.le_tsum γ)
  exact (ENNReal.ofReal_le_iff_le_toReal hfin).1 (by rw [ofReal_norm]; exact hB)

end

end ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf
