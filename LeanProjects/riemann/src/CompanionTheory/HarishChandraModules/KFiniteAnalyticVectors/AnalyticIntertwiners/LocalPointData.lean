import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AnalyticIntertwiners.LogNormEstimates
import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AnalyticIntertwiners.HarishChandraThirdIndefiniteUnitary
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.RigidityTheorems.SopNegComm

open Matrix WithLp
open scoped InnerProductSpace

noncomputable section

namespace CompanionTheory.D.gk.HC

open ReciprocityTheory.ChartRestriction.DS
open Formalism.BasicNotions.TH (GrpData URep GKMod Mat upq IsKC Eab wtSub hwSub posC KFin sameBlock)
open Formalism.MainNotions.SchurIrreducible (IsHCMod IrrU)

section Graph

open USum

variable {n : ℕ} {ε : Fin n → Bool} {H₁ H₂ : Type} [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁]
  [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂]
  {σ₁ : Matrix (Fin n) (Fin n) ℂ → (H₁ →L[ℂ] H₁)} {σ₂ : Matrix (Fin n) (Fin n) ℂ → (H₂ →L[ℂ] H₂)}
  {D₁ : Submodule ℂ H₁} {D₂ : Submodule ℂ H₂}
  {E₁ : Fin n → Fin n → Module.End ℂ D₁} {E₂ : Fin n → Fin n → Module.End ℂ D₂}

theorem graphD [CompleteSpace H₁] [CompleteSpace H₂] (h₁ : IsURepOn (UJset ε) σ₁) (h₂ : IsURepOn (UJset ε) σ₂)
    (hD₁ : IsDerivedOn ε σ₁ D₁ E₁) (hD₂ : IsDerivedOn ε σ₂ D₂ E₂) {N : Type} [AddCommGroup N] [Module ℂ N]
    (F : Fin n → Fin n → Module.End ℂ N) (κ₁ : N →ₗ[ℂ] D₁) (κ₂ : N →ₗ[ℂ] D₂) (hi : Function.Injective κ₁)
    (e₁ : ∀ a b w, E₁ a b (κ₁ w) = κ₁ (F a b w)) (e₂ : ∀ a b w, E₂ a b (κ₂ w) = κ₂ (F a b w))
    {c : ℝ} (hc : ∀ v, casimir E₁ v = (c : ℂ) • v) (U : H₁ →L[ℂ] H₂) (hU : ∀ w, U (κ₁ w) = κ₂ w)
    {W : Submodule ℂ N} (hW : FiniteDimensional ℂ W) (hWK : IsKStableSub ε F W) {w : N} (hw : w ∈ W)
    {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ UJset ε) : U (σ₁ g (κ₁ w)) = σ₂ g (κ₂ w) := by
  let κ : N →ₗ[ℂ] sD D₁ D₂ := ofP ∘ₗ κ₁.prod κ₂
  have hκ : ∀ a b w, sE E₁ E₂ a b (κ w) = κ (F a b w) := fun a b w => by
    show ofP (E₁ a b (κ₁ w), E₂ a b (κ₂ w)) = ofP (κ₁ (F a b w), κ₂ (F a b w))
    rw [e₁, e₂]
  have c₁ : ∀ w, casimir E₁ (κ₁ w) = κ₁ (casimir F w) := fun w => by
    simp only [casimir, LinearMap.sum_apply, Module.End.mul_apply, map_sum, e₁]
  have cF : ∀ w, casimir F w = (c : ℂ) • w := fun w => hi (by rw [← c₁, hc, map_smul])
  have cκ : ∀ w, casimir (sE E₁ E₂) (κ w) = (c : ℂ) • κ w := fun w => by
    rw [← map_smul, ← cF]
    simp only [casimir, LinearMap.sum_apply, Module.End.mul_apply, map_sum, hκ]
  let Γ : Submodule ℂ (WithLp 2 (H₁ × H₂)) :=
    { carrier := {x | U (ofLp x).1 = (ofLp x).2}
      add_mem' := fun {a b} ha hb => by
        show U ((ofLp a).1 + (ofLp b).1) = (ofLp a).2 + (ofLp b).2
        rw [map_add, show U (ofLp a).1 = (ofLp a).2 from ha, show U (ofLp b).1 = (ofLp b).2 from hb]
      zero_mem' := map_zero U
      smul_mem' := fun r a ha => by
        show U (r • (ofLp a).1) = r • (ofLp a).2
        rw [map_smul, show U (ofLp a).1 = (ofLp a).2 from ha] }
  have hL : Continuous (ofLp : WithLp 2 (H₁ × H₂) → H₁ × H₂) :=
    (WithLp.prodContinuousLinearEquiv 2 ℂ H₁ H₂).continuous
  have hΓ : IsClosed (Γ : Set (WithLp 2 (H₁ × H₂))) :=
    isClosed_eq (U.continuous.comp (continuous_fst.comp hL)) (continuous_snd.comp hL)
  have hle : genSub (sE E₁ E₂) (W.map κ) ≤ LinearMap.range κ :=
    sInf_le ⟨LinearMap.map_le_range, by rintro a b _ ⟨u, rfl⟩; exact ⟨_, (hκ a b u).symm⟩⟩
  have hle' : ((genSub (sE E₁ E₂) (W.map κ)).map (sD D₁ D₂).subtype).topologicalClosure ≤ Γ := by
    refine Submodule.topologicalClosure_minimal _ ?_ hΓ
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨u, rfl⟩ := hle hx
    exact hU u
  have := closure_genSub_stable (isURepOn_sσ h₁ h₂) (isDerivedOn_sσ hD₁ hD₂) (V := W.map κ) (c := c) inferInstance
    (by rintro a b hab _ ⟨u, hu, rfl⟩; exact ⟨_, hWK a b hab u hu, (hκ a b u).symm⟩)
    (by rintro _ ⟨u, -, rfl⟩; exact cκ u) g hg (κ w : WithLp 2 (H₁ × H₂))
    (Submodule.le_topologicalClosure _ ⟨κ w, (le_sInf fun _ hT => hT.1 : W.map κ ≤ genSub (sE E₁ E₂) (W.map κ))
      ⟨w, hw, rfl⟩, rfl⟩)
  exact hle' this

end Graph

section Twist

variable {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

theorem norm_detD {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ Formalism.MainNotions.S.UJset ε) : ‖g.det‖ = 1 := by
  have hm : gᴴ * Formalism.REAL.Jm ε * g = Formalism.REAL.Jm ε := hg
  have hd := congrArg (fun A => ‖Matrix.det A‖) hm
  have hJ : ‖(Formalism.REAL.Jm ε).det‖ ≠ 0 := norm_ne_zero_iff.2
    ((Matrix.isUnit_iff_isUnit_det _).1 (IsUnit.of_mul_eq_one _ (Formalism.REAL.Jm_mul_self ε))).ne_zero
  simp only [Matrix.det_mul, Matrix.det_conjTranspose, norm_mul, norm_star] at hd
  have h2 : ‖g.det‖ ^ 2 = 1 := mul_right_cancel₀ hJ (by nlinarith)
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) (by norm_num)).1 h2

def twD (m : ℕ) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H) :=
  fun g => g.det ^ m • σ g

theorem twD_rep (m : ℕ) (h : Formalism.MainNotions.S.IsURepOn (Formalism.MainNotions.S.UJset ε) σ) :
    Formalism.MainNotions.S.IsURepOn (Formalism.MainNotions.S.UJset ε) (twD m σ) := by
  refine ⟨⟨by simp [twD, h.1.1], fun a ha b hb => ?_⟩, fun g hg v => ?_, fun v => ?_⟩
  · simp only [twD]
    rw [h.1.2 a ha b hb, det_mul, mul_pow, ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul, smul_smul]
  · simp only [twD, ContinuousLinearMap.smul_apply, norm_smul, norm_pow, norm_detD hg, one_pow, one_mul, h.2.1 g hg]
  · exact ((continuous_id.matrix_det).pow m).continuousOn.smul (h.2.2 v)

theorem twD_irr (m : ℕ) (h : Formalism.MainNotions.S.IsIrredOn (Formalism.MainNotions.S.UJset ε) σ) :
    Formalism.MainNotions.S.IsIrredOn (Formalism.MainNotions.S.UJset ε) (twD m σ) := fun S hS hinv => h S hS fun g hg v hv => by
  have h0 : g.det ^ m ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.1 (by rw [norm_detD hg]; exact one_ne_zero))
  exact (S.smul_mem_iff h0).1 (hinv g hg v hv)

theorem twD_kfin (m : ℕ) {v : H} (h : Formalism.MainNotions.S.IsKFin ε σ v) : Formalism.MainNotions.S.IsKFin ε (twD m σ) v := by
  obtain ⟨S, h1, h2, h3⟩ := h
  exact ⟨S, h1, h2, fun g hg u hu => S.smul_mem _ (h3 g hg u hu)⟩

end Twist

section Cover

variable {p q : ℕ} {T : GrpData p q} {πU : URep T} {M : GKMod p q} {io : M.V →ₗ[ℂ] πU.H}

theorem skewD (h : IsHCMod πU M io) : SkewD M io := fun Y hY v w => by
  have h1 := (h.2.2 Y hY v).inner ℂ (h.2.2 Y hY w)
  simp only [inner_piC, zero_smul, T.expt_zero, map_one, ContinuousLinearMap.one_apply] at h1
  have h2 := h1.unique (hasDerivAt_const _ _)
  linear_combination h2

theorem eigD (h : IsHCMod πU M io) {X : Mat p q} (hX : X ∈ upq p q) {v : M.V} {c : ℂ} (hv : M.act X v = c • v)
    (t : ℝ) : πU.π (T.expt (t • X)) (io v) = Complex.exp (c * t) • io v := by
  have hd : ∀ s : ℝ, HasDerivAt (fun r : ℝ => πU.π (T.expt (r • X)) (io v)) (c • πU.π (T.expt (s • X)) (io v)) s := by
    intro s
    have h0 : HasDerivAt (fun r : ℝ => πU.π (T.expt (r • X)) (io v)) (io (M.act X v)) (s - s) := by
      rw [sub_self]; exact h.2.2 X hX v
    have h1 := ((πU.π (T.expt (s • X))).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt s (h0.comp_sub_const s s)
    rw [hv, map_smul] at h1
    convert h1 using 1
    · funext r
      show _ = πU.π (T.expt (s • X)) (πU.π (T.expt ((r - s) • X)) (io v))
      rw [← pi_mulC, ← T.expt_add X hX, add_sub_cancel]
    · exact (map_smul _ _ _).symm
  have hg : ∀ s : ℝ, HasDerivAt (fun r : ℝ => Complex.exp (-(c * r)) • πU.π (T.expt (r • X)) (io v)) 0 s := by
    intro s
    have h1 := (((hasDerivAt_id s).ofReal_comp.const_mul c).fun_neg.cexp).fun_smul (hd s)
    refine h1.congr_deriv ?_
    rw [smul_smul, ← add_smul, Complex.ofReal_one, show ∀ x : ℂ, x * c + x * -(c * 1) = 0 from fun x => by ring,
      zero_smul]
  have h2 := is_const_of_deriv_eq_zero (fun s => (hg s).differentiableAt) (fun s => (hg s).deriv) t 0
  simp only [Complex.ofReal_zero, mul_zero, neg_zero, Complex.exp_zero, zero_smul, T.expt_zero, map_one,
    ContinuousLinearMap.one_apply, one_smul] at h2
  conv_rhs => rw [← h2]
  rw [smul_smul, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero, one_smul]

theorem iE_memD (a : Formalism.BasicNotions.TH.Ix p q) : Complex.I • Eab a a ∈ upq p q :=
  mem_upq_of_adjZD (by
    rw [adjZ_smulD, adjZ_singleD a a (sameBlock_reflD a), show star Complex.I = -Complex.I from Complex.conj_I, neg_smul])

theorem exp_twoPiD (a : Formalism.BasicNotions.TH.Ix p q) :
    NormedSpace.exp (((2 * Real.pi : ℝ) : ℂ) • rx (Complex.I • Eab a a)) = 1 := by
  have e : ((2 * Real.pi : ℝ) : ℂ) • rx (Complex.I • Eab a a) =
      diagonal fun i => if i = finSumFinEquiv a then 2 * Real.pi * Complex.I else 0 := by
    ext i k
    obtain ⟨b, rfl⟩ := finSumFinEquiv.surjective i
    obtain ⟨d, rfl⟩ := finSumFinEquiv.surjective k
    simp only [rx, Eab, Matrix.smul_apply, reindex_apply, submatrix_apply, Equiv.symm_apply_apply, Matrix.single_apply,
      diagonal_apply, Equiv.apply_eq_iff_eq, smul_eq_mul]
    by_cases h1 : b = d
    · subst h1
      by_cases h2 : b = a
      · subst h2; simp
      · simp [h2, Ne.symm h2]
    · rw [if_neg h1, if_neg (fun h => h1 (h.1.symm.trans h.2))]; simp
  rw [e, Matrix.exp_diagonal, ← diagonal_one]
  congr 1
  funext i
  rw [Pi.coe_exp, ← Complex.exp_eq_exp_ℂ]
  split_ifs
  · exact Complex.exp_two_pi_mul_I
  · exact Complex.exp_zero

theorem signD (h : IsHCMod πU M io) {j : ℕ} {σ : Matrix (Fin (p + q)) (Fin (p + q)) ℂ → (πU.H →L[ℂ] πU.H)}
    (h1 : σ 1 = 1) (hex : ∀ X ∈ upq p q, inG (epq p q) (rx X) ∧ ∀ t : ℝ,
      πU.π (T.expt (t • X)) = Complex.exp ((j : ℂ) * (t * X.trace / 2)) • σ (NormedSpace.exp ((t : ℂ) • rx X)))
    (a : Formalism.BasicNotions.TH.Ix p q) {v : M.V} (hv0 : v ≠ 0) {c : ℂ} (hv : M.act (Eab a a) v = c • v) :
    Complex.exp (Complex.I * c * (2 * Real.pi : ℝ)) = (-1) ^ j := by
  have e := eigD h (iE_memD a) (v := v) (c := Complex.I * c)
    (by rw [map_smul, LinearMap.smul_apply, hv, smul_smul]) (2 * Real.pi)
  rw [(hex _ (iE_memD a)).2, exp_twoPiD, h1, ContinuousLinearMap.smul_apply, ContinuousLinearMap.one_apply] at e
  have hne : io v ≠ 0 := fun h0 => hv0 (h.1 (h0.trans (map_zero io).symm))
  rw [← smul_left_injective ℂ hne e, ← Complex.exp_pi_mul_I, ← Complex.exp_nat_mul, trace_smul, Eab,
    trace_single_eq_same]
  congr 1
  push_cast
  simp only [smul_eq_mul]
  ring

theorem dictD (hS : KFSm) (h : IsHCMod πU M io) {j : ℕ} (m : ℕ)
    {σ : Matrix (Fin (p + q)) (Fin (p + q)) ℂ → (πU.H →L[ℂ] πU.H)}
    (hσ : Formalism.MainNotions.S.IsURepOn (Formalism.MainNotions.S.UJset (epq p q)) σ) (hσi : Formalism.MainNotions.S.IsIrredOn (Formalism.MainNotions.S.UJset (epq p q)) σ)
    (hkf : ∀ x, KFin T πU.π x ↔ Formalism.MainNotions.S.IsKFin (epq p q) σ x)
    (hex : ∀ X ∈ upq p q, inG (epq p q) (rx X) ∧ ∀ t : ℝ,
      πU.π (T.expt (t • X)) = Complex.exp ((j : ℂ) * (t * X.trace / 2)) • σ (NormedSpace.exp ((t : ℂ) • rx X))) :
    ∃ κ : M.V →ₗ[ℂ] smD (epq p q) (twD m σ), (∀ v, (κ v : πU.H) = io v) ∧ ∀ Z v,
      actM (smE (epq p q) (twD m σ)) (rx Z) (κ v) = κ (M.act Z v + (((m : ℂ) - j / 2) * Z.trace) • v) := by
  have hτ := twD_rep m hσ
  obtain ⟨hsm, -⟩ := hS _ _ _ (twD m σ) hτ (twD_irr m hσi)
  have hder := isDerivedOn_smE (ε := epq p q) (σ := twD m σ) hτ
  let κ : M.V →ₗ[ℂ] smD (epq p q) (twD m σ) :=
    io.codRestrict _ fun v => hsm _ (twD_kfin m ((hkf _).1 ((h.2.1 _).1 ⟨v, rfl⟩)))
  refine ⟨κ, fun _ => rfl, ?_⟩
  have key : ∀ Y ∈ upq p q, ∀ v, actLC (smE (epq p q) (twD m σ)) (rx Y) (κ v) =
      κ (M.act Y v + (((m : ℂ) - j / 2) * Y.trace) • v) := by
    intro Y hY v
    refine Subtype.ext ((hder.deriv _ (hex Y hY).1 (κ v)).unique ?_)
    have d1 : HasDerivAt (fun t : ℝ => (NormedSpace.exp (t • rx Y)).det) (rx Y).trace 0 :=
      PI.UnitaryCorollaryDerivatives.DjC.hasDerivAt_det_of_one _ _ (by simp) fun a b => PI.UnitaryCorollaryDerivatives.DjC.hasDerivAt_exp_entry (rx Y) a b
    have d2 := ((((hasDerivAt_id (0 : ℝ)).ofReal_comp.mul_const Y.trace).div_const 2).const_mul (j : ℂ)).fun_neg.cexp
    have d3 := ((d1.fun_pow m).fun_mul d2).fun_smul (h.2.2 Y hY v)
    convert d3 using 1
    · funext t
      rw [(hex Y hY).2, ContinuousLinearMap.smul_apply, smul_smul, mul_assoc, ← Complex.exp_add]
      simp only [id, neg_add_cancel, Complex.exp_zero, mul_one, twD, ContinuousLinearMap.smul_apply, Complex.coe_smul]
      rfl
    · show io _ = _
      simp only [map_add, map_smul, id, zero_smul, NormedSpace.exp_zero, det_one, one_pow, Complex.ofReal_zero, zero_mul,
        zero_div, mul_zero, neg_zero, Complex.exp_zero, mul_one, one_mul, one_smul, T.expt_zero, map_one,
        ContinuousLinearMap.one_apply, trace_rxC, Complex.ofReal_one]
      congr 2
      ring
  intro Z v
  obtain ⟨Y₁, h₁, Y₂, h₂, e, -⟩ := upq_decC Z
  show actLC _ (rx Z) (κ v) = _
  rw [e, show rx (Y₁ + Complex.I • Y₂) = rx Y₁ + Complex.I • rx Y₂ from rfl]
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, key Y₁ h₁, key Y₂ h₂, trace_add, trace_smul,
    smul_eq_mul]
  module

end Cover

theorem clause2_of (h1 : Clause1) (hS : KFSm) (hC : CasScal) (hDe : Descend) : Clause2 := by
  intro p q hpq T π₁ π₂ i₁ i₂ M₁ M₂ io₁ io₂ m₁ m₂ e he
  obtain ⟨hA, hI⟩ := (h1 p q hpq T π₁ i₁).2.2 M₁ io₁ m₁
  obtain ⟨c, hc, hB⟩ := form_propD io₁ (io₂ ∘ₗ e.toLinearMap) m₁.1 (m₂.1.comp e.injective) (skewD m₁)
    (fun Y hY v w => by
      show ⟪io₂ (e (M₁.act Y v)), io₂ (e w)⟫_ℂ = -⟪io₂ (e v), io₂ (e (M₁.act Y w))⟫_ℂ
      rw [he, he]; exact skewD m₂ Y hY _ _) hI hA
  have hs : 0 < √c := Real.sqrt_pos.2 hc
  obtain ⟨r, hr⟩ : ∃ r : ℂ, r = (((√c)⁻¹ : ℝ) : ℂ) := ⟨_, rfl⟩
  have hr0 : r ≠ 0 := by rw [hr]; exact Complex.ofReal_ne_zero.2 (inv_pos.2 hs).ne'
  have dense : ∀ (π : URep T) (M : GKMod p q) (io : M.V →ₗ[ℂ] π.H), IsHCMod π M io → DenseRange io :=
    fun π M io m => (kfinDense_coverC (fun _ _ _ _ _ _ _ hσ => kfinDense_UJC hσ) π).mono fun x hx => (m.2.1 x).2 hx
  have d₁ := dense π₁ M₁ io₁ m₁
  have d₂ : DenseRange (r • io₂) := (dense π₂ M₂ io₂ m₂).mono (by
    rintro _ ⟨v, rfl⟩
    exact ⟨r⁻¹ • v, by rw [LinearMap.smul_apply, map_smul, smul_smul, mul_inv_cancel₀ hr0, one_smul]⟩)
  have hn : ∀ v, ‖(r • io₂) (e v)‖ = ‖io₁ v‖ := fun v => by
    have h2 : ‖io₂ (e v)‖ ^ 2 = c * ‖io₁ v‖ ^ 2 := by
      have := congrArg Complex.re (hB v v)
      rw [Complex.re_ofReal_mul] at this
      rw [← inner_self_eq_norm_sq (𝕜 := ℂ), ← inner_self_eq_norm_sq (𝕜 := ℂ)]
      exact this
    have h3 : ‖io₂ (e v)‖ = √c * ‖io₁ v‖ := by
      rw [← Real.sqrt_sq (norm_nonneg (io₂ (e v))), h2, Real.sqrt_mul hc.le, Real.sqrt_sq (norm_nonneg _)]
    rw [LinearMap.smul_apply, norm_smul, hr, Complex.norm_real, Real.norm_of_nonneg (inv_pos.2 hs).le, h3,
      inv_mul_cancel_left₀ hs.ne']
  let U := e.extendOfIsometry io₁ (r • io₂) d₁ d₂ hn
  have hU : ∀ v, U (io₁ v) = r • io₂ (e v) := LinearEquiv.extendOfIsometry_eq e io₁ (r • io₂) d₁ d₂ hn
  obtain ⟨j₁, σ₁, ⟨hσ₁, hπ₁⟩, hi₁, hk₁, hx₁⟩ := hDe p q T π₁ i₁
  obtain ⟨j₂, σ₂, ⟨hσ₂, hπ₂⟩, hi₂, hk₂, hx₂⟩ := hDe p q T π₂ i₂
  obtain ⟨m, hm⟩ : Even (j₁ + j₂) := by
    obtain ⟨μ, v, hv, hv0⟩ := exists_hwD hI.1
    have a : Formalism.BasicNotions.TH.Ix p q := finSumFinEquiv.symm ⟨0, hpq⟩
    have hw := mem_wtSubD.1 (Submodule.mem_inf.1 hv).1 a
    have s₁ := signD m₁ hσ₁.1.1 hx₁ a hv0 hw
    have s₂ := signD m₂ hσ₂.1.1 hx₂ a (v := e v) (e.map_ne_zero_iff.2 hv0) (by rw [← he, hw, map_smul])
    refine (neg_one_pow_eq_one_iff_even (R := ℂ) (by norm_num)).1 ?_
    rw [pow_add, ← s₁, s₂, ← pow_add, ← two_mul, pow_mul]
    norm_num
  obtain ⟨κ₁, hκ₁, a₁⟩ := dictD hS m₁ m hσ₁ hi₁ hk₁ hx₁
  obtain ⟨κ₂, hκ₂, a₂⟩ := dictD hS m₂ j₂ hσ₂ hi₂ hk₂ hx₂
  have hmj : (m : ℂ) - j₁ / 2 = j₂ / 2 := by
    have : (j₁ : ℂ) + j₂ = m + m := by exact_mod_cast hm
    linear_combination (-1 / 2 : ℂ) * this
  let F : Fin (p + q) → Fin (p + q) → Module.End ℂ M₁.V := fun a b =>
    M₁.act (ixC (single a b 1)) + ((j₂ / 2 : ℂ) * (ixC (single a b (1 : ℂ))).trace) • 1
  obtain ⟨cs, hcs⟩ := hC _ _ _ (twD m σ₁) (twD_rep m hσ₁) (twD_irr m hi₁)
  have hone : ∀ {N : Type} [AddCommGroup N] [Module ℂ N] (E : Fin (p + q) → Fin (p + q) → Module.End ℂ N) a b,
      E a b = actM E (rx (ixC (single a b 1))) := fun E a b => by
    rw [rx_ixC]; exact ((actLC_single E a b 1).trans (one_smul _ _)).symm
  have main : ∀ g ∈ Formalism.MainNotions.S.UJset (epq p q), ∀ w, U (twD m σ₁ g (io₁ w)) = twD j₂ σ₂ g (U (io₁ w)) := by
    intro g hg w
    obtain ⟨W, hWf, hw, hWs⟩ := M₁.kfin w
    have := graphD (ε := epq p q) (twD_rep m hσ₁) (twD_rep j₂ hσ₂) (isDerivedOn_smE (twD_rep m hσ₁))
      (isDerivedOn_smE (twD_rep j₂ hσ₂)) F κ₁ (r • (κ₂ ∘ₗ e.toLinearMap))
      (fun a b h => m₁.1 (by rw [← hκ₁, ← hκ₁, h]))
      (fun a b w => by rw [hone (smE _ _) a b, a₁, hmj]; rfl)
      (fun a b w => by
        show smE _ _ a b (r • κ₂ (e w)) = r • κ₂ (e (M₁.act (ixC (single a b 1)) w + ((j₂ / 2 : ℂ) * (ixC (single a b (1 : ℂ))).trace) • w))
        rw [map_smul, hone (smE _ _) a b, a₂, map_add e, map_smul e, he,
          show (j₂ : ℂ) - j₂ / 2 = j₂ / 2 by ring])
      hcs U.toContinuousLinearEquiv.toContinuousLinearMap
      (fun w => by
        show U (κ₁ w) = r • (κ₂ (e w) : π₂.H)
        rw [hκ₁, hκ₂, hU])
      hWf (fun a b hab u hu => add_mem (hWs _ (fun c d hcd => ?_) u hu) (W.smul_mem _ hu)) hw hg
    · have e2 : ((r • (κ₂ ∘ₗ e.toLinearMap)) w : π₂.H) = U (io₁ w) := by
        rw [hU, ← hκ₂]; rfl
      rw [e2, hκ₁] at this
      exact this
    · show single a b (1 : ℂ) (finSumFinEquiv c) (finSumFinEquiv d) = 0
      rw [Matrix.single_apply, if_neg]
      rintro ⟨rfl, rfl⟩
      simp only [epq, Equiv.symm_apply_apply] at hab
      rcases c with c | c <;> rcases d with d | d <;> simp_all [sameBlock]
  refine ⟨U, fun x => ?_⟩
  refine d₁.induction ?_ (isClosed_eq (U.continuous.comp (π₁.π x).continuous) ((π₂.π x).continuous.comp U.continuous))
  rintro _ ⟨w, rfl⟩
  have h0 : ((T.sq x : ℂˣ) : ℂ) ^ j₂ ≠ 0 := pow_ne_zero _ (Units.ne_zero _)
  have h := main _ (mem_UJC T x) w
  simp only [twD, ContinuousLinearMap.smul_apply, det_rxC, ← sq_sqC, ← pow_mul] at h
  refine smul_right_injective _ h0 ?_
  beta_reduce
  rw [← map_smul U, hπ₁, hπ₂]
  simp only [ContinuousLinearMap.smul_apply, smul_smul, ← pow_add]
  rw [show j₂ + j₁ = 2 * m by omega, show j₂ + j₂ = 2 * j₂ by omega]
  exact h

end CompanionTheory.D.gk.HC
