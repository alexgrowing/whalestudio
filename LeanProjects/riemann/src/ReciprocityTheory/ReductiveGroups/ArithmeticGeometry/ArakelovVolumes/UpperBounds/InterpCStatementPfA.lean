import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.ExhaustFStatementPfE
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.SiegelSpaceAlgebraHolds

namespace ReciprocityTheory.ChartRestriction.G.AR.Up

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix ComplexOrder

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

namespace IC

theorem chi_ne_zero {r : ℕ} (X : Data E r) (la : Wt X.Ψ r) {γ : GL (Fin r) E} (hγ : γ ∈ X.Γ) :
    X.χ la γ ≠ 0 := by
  obtain ⟨k, hk, h⟩ := X.χ_fin la
  intro h0
  have h1 := h γ hγ
  rw [h0, zero_pow hk.ne'] at h1
  exact zero_ne_one h1

theorem poin_single {r : ℕ} (X : Data E r) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) (x : Frame X.Ψ r)
    {γ0 : GL (Fin r) E} (h0 : γ0 ∈ X.Γ) (hz : ∀ γ ∈ X.Γ, γ ≠ γ0 → P (lact γ x) = 0) :
    poin X la P x = (X.χ la γ0)⁻¹ * P (lact γ0 x) := by
  unfold poin
  refine (tsum_eq_single ⟨γ0, h0⟩ fun γ hγ => ?_).trans rfl
  rw [hz γ.1 γ.2 (fun h => hγ (Subtype.ext h)), mul_zero]

theorem poin_zero {r : ℕ} (X : Data E r) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) (x : Frame X.Ψ r)
    (hz : ∀ γ ∈ X.Γ, P (lact γ x) = 0) : poin X la P x = 0 := by
  unfold poin
  have h1 : ∀ γ : X.Γ, (X.χ la γ.1)⁻¹ * P (lact γ.1 x) = 0 := fun γ => by
    rw [hz γ.1 γ.2, mul_zero]
  simp only [h1, tsum_zero]

theorem norm_sgn (p0 a : ℕ) : ‖((sgn p0 a : ℝ) : ℂ)‖ = 1 := by
  unfold sgn
  split_ifs <;> simp

theorem norm_dmin_orth {r : ℕ} (X : Data E r) {x : Frame X.Ψ r} (hx : IsOrth X x) (τ : X.Ψ)
    (i : Fin (r + 1)) : ‖dmin X.Gm x τ i‖ = 1 := by
  unfold dmin lminor
  rw [hx τ, Matrix.submatrix_diagonal _ _ (Fin.castLE_injective _), Matrix.det_diagonal, norm_prod]
  exact Finset.prod_eq_one fun a _ => norm_sgn _ _

theorem pnorm_orth {r : ℕ} (X : Data E r) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) {x : Frame X.Ψ r}
    (hx : IsOrth X x) : X.pnorm la P x = ‖P x‖ := by
  simp [Data.pnorm, norm_div, norm_dmin_orth X hx]

theorem cfwM_smul {r : ℕ} (X : Data E r) {ps : Frame X.Ψ r → ℝ} {a : ℝ} (h : cfwM X ps a) {t : ℝ}
    (ht : 0 < t) : cfwM X (fun x => t * ps x) (t * a) := by
  obtain ⟨⟨C, A', h1⟩, h2⟩ := h
  refine ⟨⟨t * C, t * A', fun x hx => ?_⟩, fun η hη hη' => ?_⟩
  · show t * ps x ≤ _
    exact (mul_le_mul_of_nonneg_left (h1 x hx) ht.le).trans_eq (by ring)
  · obtain ⟨C, A', h3⟩ := h2 η hη hη'
    refine ⟨t * C, t * A', fun x hx ξ hξ hτ => ?_⟩
    show t * ps x ≤ _
    exact (mul_le_mul_of_nonneg_left (h3 x hx ξ hξ hτ) ht.le).trans_eq (by ring)

theorem half_le {w : ℝ≥0∞} {p ψ : ℝ} (hw : ENNReal.ofReal (Real.exp (-(p + ψ))) ≤ w) :
    (ENNReal.ofReal (Real.exp (-p)) / w) ^ (1 / 2 : ℝ) ≤ ENNReal.ofReal (Real.exp (ψ / 2)) := by
  have h1 : ENNReal.ofReal (Real.exp (-p)) / w ≤ ENNReal.ofReal (Real.exp ψ) := by
    calc ENNReal.ofReal (Real.exp (-p)) / w
        ≤ ENNReal.ofReal (Real.exp (-p)) / ENNReal.ofReal (Real.exp (-(p + ψ))) :=
          ENNReal.div_le_div_left hw _
      _ = ENNReal.ofReal (Real.exp (-p) / Real.exp (-(p + ψ))) :=
          (ENNReal.ofReal_div_of_pos (Real.exp_pos _)).symm
      _ = ENNReal.ofReal (Real.exp ψ) := by
          rw [← Real.exp_sub, show -p - -(p + ψ) = ψ by ring]
  calc (ENNReal.ofReal (Real.exp (-p)) / w) ^ (1 / 2 : ℝ)
      ≤ (ENNReal.ofReal (Real.exp ψ)) ^ (1 / 2 : ℝ) := ENNReal.rpow_le_rpow h1 (by norm_num)
    _ = ENNReal.ofReal (Real.exp ψ ^ (1 / 2 : ℝ)) :=
        ENNReal.ofReal_rpow_of_nonneg (Real.exp_pos _).le (by norm_num)
    _ = ENNReal.ofReal (Real.exp (ψ / 2)) := by
        rw [← Real.exp_mul, mul_one_div]

theorem orth_mem_dom {r : ℕ} (X : Data E r) {x0 : Frame X.Ψ r} (ho : IsOrth X x0) : x0 ∈ X.dom := by
  simp only [Data.dom, GG, Set.mem_setOf_eq]
  intro τ
  have hs : ∀ a : Fin r, ((sgn X.p0 (a : ℕ) : ℝ) : ℂ) ≠ 0 := by
    intro a
    unfold sgn
    split_ifs <;> norm_num
  refine ⟨?_, fun i => ?_⟩
  · intro h0
    have hg : gram τ.1 X.Gm (mat x0 τ) =
        (mat x0 τ)ᵀ * X.Gm.map τ.1 * (mat x0 τ).map (starRingEnd ℂ) := by
      ext a b
      simp only [gram, hermC, col, mat, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply,
        Matrix.map_apply, Finset.sum_mul]
      exact Finset.sum_comm
    have h1 := congrArg Matrix.det hg
    rw [ho τ, Matrix.det_diagonal, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, h0,
      zero_mul, zero_mul] at h1
    exact (Finset.prod_ne_zero_iff.mpr fun a _ => hs a) h1
  · have hd : dmin X.Gm x0 τ i = ((psgn X.p0 i : ℝ) : ℂ) := by
      unfold dmin lminor
      rw [ho τ, Matrix.submatrix_diagonal _ _ (Fin.castLE_injective _), Matrix.det_diagonal]
      simp [psgn, ← Fin.prod_univ_eq_prod_range]
    have hne : psgn X.p0 i ≠ 0 := by
      unfold psgn
      refine Finset.prod_ne_zero_iff.mpr fun a _ => ?_
      unfold sgn
      split_ifs <;> norm_num
    rw [hd, Complex.ofReal_re]
    exact mul_self_pos.mpr hne

private lemma leviO_fderiv_lemma {m : ℕ} (c : ℝ) (f : V m → ℂ) (y : V m) :
    fderiv ℝ (fun w => (c : ℂ) * f w) y = (c : ℂ) • fderiv ℝ f y := by
  by_cases hf : DifferentiableAt ℝ f y
  · exact fderiv_const_mul hf _
  · by_cases hc : c = 0
    · subst hc
      simp
    · have hc' : (c : ℂ) ≠ 0 := by exact_mod_cast hc
      have h2 : ¬ DifferentiableAt ℝ (fun w => (c : ℂ) * f w) y := by
        intro h
        apply hf
        refine (h.const_mul ((c : ℂ)⁻¹)).congr_of_eventuallyEq (Filter.Eventually.of_forall fun w => ?_)
        show f w = (c : ℂ)⁻¹ * ((c : ℂ) * f w)
        rw [← mul_assoc, inv_mul_cancel₀ hc', one_mul]
      rw [fderiv_zero_of_not_differentiableAt hf, fderiv_zero_of_not_differentiableAt h2, smul_zero]

theorem leviO_smul {r : ℕ} (X : Data E r) (x0 : Frame X.Ψ r) (g : Frame X.Ψ r → ℝ) (t : ℝ)
    {z : V (nd X)} (hg : ContDiffAt ℝ 2 (fun w => g (cpt X x0 w)) z) (ξ : Fin (nd X) → ℂ) :
    leviO X x0 (fun x => t * g x) z ξ = t * leviO X x0 g z ξ := by
  show (leviV (nd X) (fun w => (((t * g (cpt X x0 w)) : ℝ) : ℂ)) z ξ).re =
    t * (leviV (nd X) (fun w => ((g (cpt X x0 w) : ℝ) : ℂ)) z ξ).re
  have hf : (fun w => (((t * g (cpt X x0 w)) : ℝ) : ℂ)) =
      fun w => (t : ℂ) * ((g (cpt X x0 w) : ℝ) : ℂ) := funext fun w => Complex.ofReal_mul _ _
  have hwdb : ∀ (k : Fin (nd X)) (f : V (nd X) → ℂ),
      wdb (nd X) k (fun w => (t : ℂ) * f w) = fun y => (t : ℂ) * wdb (nd X) k f y := by
    intro k f
    funext y
    simp only [wdb, leviO_fderiv_lemma, ContinuousLinearMap.smul_apply, smul_eq_mul]
    ring
  have hwd : ∀ (j : Fin (nd X)) (f : V (nd X) → ℂ) (y : V (nd X)),
      wd (nd X) j (fun w => (t : ℂ) * f w) y = (t : ℂ) * wd (nd X) j f y := by
    intro j f y
    simp only [wd, leviO_fderiv_lemma, ContinuousLinearMap.smul_apply, smul_eq_mul]
    ring
  rw [hf]
  simp only [leviV, hwdb, hwd, mul_assoc, ← Finset.mul_sum, Complex.re_ofReal_mul]

end IC

theorem interpC_of (hP : PoinStatement (E := E)) (hK : KronHolPsiStatement (E := E))
    (hη : ∀ (r : ℕ) (X : Data E r) (Xa : ArchInM X), ∃ η : ℝ, 0 < η ∧ ∀ x0, IsOrth X x0 →
      ∀ z ∈ OmF X x0, ∀ ξ : Fin (nd X) → ℂ,
        2 * η * leviO X x0 (phla X Xa.L) z ξ ≤ leviO X x0 (phla X Xa.Fp) z ξ - leviDens X x0 z ξ -
          (nd X : ℝ) * leviO X x0 (phla X Xa.L) z ξ +
          leviO X x0 (fun x => (1 + Xa.c1 / Xa.a1) * Xa.ps0 x) z ξ) :
    InterpCStatement (E := E) := by
  intro r X Xa Fl hPD hmar hL hps hcusp hMH v
  obtain ⟨bb, m, hbb, hbm, hm⟩ := hmar
  obtain ⟨Cp, hCp⟩ := hps
  set t : ℝ := 1 + Xa.c1 / Xa.a1 with ht_def
  have ht : 0 < t := by have := Xa.frame_theta_const_pos; have := Xa.frame_theta_weight_pos; positivity
  have hta : Xa.c1 < t * Xa.a1 := by
    have ha := Xa.frame_theta_weight_pos
    rw [ht_def, add_mul, one_mul, div_mul_cancel₀ _ ha.ne']
    linarith
  set ψ : Frame X.Ψ r → ℝ := fun x => t * Xa.ps0 x with hψ
  have hψinv : IsInvFn X ψ := fun γ hγ x hx b hb => by simp only [hψ, Xa.potential_invariant γ hγ x hx b hb]
  have hsm : ∀ x0, IsOrth X x0 → ContDiffOn ℝ ∞ (fun z => Xa.ps0 (cpt X x0 z)) (OmF X x0) :=
    fun x0 ho => Xa.potential_smooth x0 (IC.orth_mem_dom X ho)
  have hψsm : ∀ x0, IsOrth X x0 → ContDiffOn ℝ ∞ (fun z => ψ (cpt X x0 z)) (OmF X x0) :=
    fun x0 ho => contDiffOn_const.mul (hsm x0 ho)
  have hψb : ∃ C : ℝ, ∀ x ∈ X.dom, ψ x ≤ C :=
    ⟨t * Cp, fun x hx => mul_le_mul_of_nonneg_left (hCp x hx) ht.le⟩
  have hmψ : ∃ bb m : ℝ, 4 * (X.Ψ.card : ℝ) * (r : ℝ) ^ 2 < bb ∧ bb < m ∧
      ∀ x0, IsOrth X x0 → ∀ z ∈ OmF X x0, ∀ ξ : Fin (nd X) → ℂ,
        m * leviRh X x0 z ξ ≤ leviO X x0 (phla X Xa.Fp) z ξ - leviDens X x0 z ξ -
          (nd X : ℝ) * leviO X x0 (phla X Xa.L) z ξ + leviO X x0 ψ z ξ := by
    refine ⟨bb, m, hbb, hbm, fun x0 ho z hz ξ => ?_⟩
    have hca : ContDiffAt ℝ 2 (fun w => Xa.ps0 (cpt X x0 w)) z :=
      ((hsm x0 ho).contDiffAt ((ExF.isOpen_OmF X x0).mem_nhds hz)).of_le (show (2 : WithTop ℕ∞) ≤ (⊤ : ℕ∞) from WithTop.coe_le_coe.2 le_top)
    rw [show leviO X x0 ψ z ξ = t * leviO X x0 Xa.ps0 z ξ from IC.leviO_smul X x0 Xa.ps0 t hca ξ]
    exact hm x0 ho z hz ξ
  have hQ : ∀ j, ∃ Q ∈ X.SSgt Xa.Fp Xa.c1, Q (Fl.xs j) ≠ 0 ∧ ∀ j', j' ≠ j → Q (Fl.xs j') = 0 := by
    intro j
    obtain ⟨x0, W, bb', F, P, γ0, ho, hW, hWl, hWψ, hbb', hF, hA, hBE, hPF, h0, hne, hz⟩ :=
      hK r X Xa Fl hPD ψ hψinv hψsm hψb hmψ (hη r X Xa) hL j
    obtain ⟨-, hbdd, -, hball, -⟩ := hP r X x0 ho hPD Xa.Fp W bb' hW hWl hbb' F P hF hA hBE hPF
    have hmode := hMH Xa.Fp (poin X Xa.Fp P) ψ (t * Xa.a1) hbdd.1 (IC.cfwM_smul X Xa.base_psi_weighted_cf ht)
      (by have := Xa.frame_theta_weight_pos; positivity) (fun ρ hρ hρ1 => by
        obtain ⟨C', hC'⟩ := hball ρ hρ hρ1
        refine ⟨C', fun x hx hox => ?_⟩
        rw [IC.pnorm_orth X Xa.Fp _ hox]
        refine (hC' x hx hox).trans (mul_le_mul' le_rfl ?_)
        exact iSup_mono fun z => iSup_mono fun _ => iSup_mono fun hzd => IC.half_le (hWψ _ hzd))
    refine ⟨poin X Xa.Fp P, ⟨⟨hbdd, fun ξ hξ x hx => hmode ξ hξ 0 ?_ x hx⟩,
      fun ξ hξ ν hν x hx => hmode ξ hξ ν (lt_of_le_of_lt hν hta) x hx⟩, ?_, fun j' hj' => ?_⟩
    · simp only [Pi.zero_apply, Finset.sum_const_zero]
      have := Xa.frame_theta_weight_pos; positivity
    · rw [IC.poin_single X Xa.Fp P _ h0 fun γ hγ hne' => hz γ hγ j (Or.inl hne')]
      exact mul_ne_zero (inv_ne_zero (IC.chi_ne_zero X Xa.Fp h0)) hne
    · exact IC.poin_zero X Xa.Fp P _ fun γ hγ => hz γ hγ j' (Or.inr hj')
  classical
  choose Q hQs hQne hQz using hQ
  obtain ⟨-, -, ⟨h0, hadd, hsmul⟩, -⟩ := siegelSpaceAlgebra_holds (E := E) r X Xa.Fp Xa.Fp Xa.c1
  set G : Fin Fl.δ → Frame X.Ψ r → ℂ := fun j => (Q j (Fl.xs j))⁻¹ • Q j with hG
  have hGs : ∀ j, G j ∈ X.SSgt Xa.Fp Xa.c1 := fun j => hsmul _ _ (hQs j)
  have hGv : ∀ j j', G j (Fl.xs j') = if j' = j then 1 else 0 := by
    intro j j'
    by_cases h : j' = j
    · subst h; simp [hG, hQne]
    · simp [hG, h, hQz j j' h]
  have hmem : ∀ s : Finset (Fin Fl.δ), ∑ j ∈ s, v j • G j ∈ X.SSgt Xa.Fp Xa.c1 := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using h0
    | insert a s ha ih =>
      rw [Finset.sum_insert ha]
      exact hadd _ (hsmul _ _ (hGs a)) _ ih
  refine ⟨∑ j, v j • G j, hmem _, fun j => ?_⟩
  simp [Finset.sum_apply, hGv]

end

end ReciprocityTheory.ChartRestriction.G.AR.Up
