import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.MultivariableReproducingFormula

noncomputable section

open MeasureTheory Matrix
open scoped ENNReal NNReal ComplexConjugate

namespace UpperTheory.Esk.DiagonalTermsContribution

open UpperTheory.Esk

theorem diag_smul (g : GL (Fin 2) ℝ) (hb : g 0 1 = 0) (hc : g 1 0 = 0) (z : P) :
    (g • z).1 = ((g 0 0 / g 1 1 : ℝ) : ℂ) * z.1 := by
  have hd : g 1 1 ≠ 0 := by
    intro h; apply g.det_ne_zero; rw [det_eq, hb, h]; ring
  have hd' : ((g 1 1 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hd
  rw [coe_smul]
  simp only [num, den, hb, hc, Complex.ofReal_zero, zero_mul, add_zero, zero_add, Complex.ofReal_div]
  field_simp

theorem comm_diag (m d : GL (Fin 2) ℝ) (h1 : d 0 1 = 0) (h2 : d 1 0 = 0) (h3 : d 0 0 ≠ d 1 1)
    (h : m * d = d * m) : m 0 1 = 0 ∧ m 1 0 = 0 := by
  have a1 := congrArg (fun x : GL (Fin 2) ℝ => (x : Matrix (Fin 2) (Fin 2) ℝ) 0 1) h
  have a2 := congrArg (fun x : GL (Fin 2) ℝ => (x : Matrix (Fin 2) (Fin 2) ℝ) 1 0) h
  simp only [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, h1, h2] at a1 a2
  constructor
  · have : m 0 1 * (d 1 1 - d 0 0) = 0 := by linear_combination a1
    rcases mul_eq_zero.1 this with e | e
    · exact e
    · exact absurd (sub_eq_zero.1 e).symm h3
  · have : m 1 0 * (d 0 0 - d 1 1) = 0 := by linear_combination a2
    rcases mul_eq_zero.1 this with e | e
    · exact e
    · exact absurd (sub_eq_zero.1 e) h3

theorem diag_of (g : GL (Fin 2) ℝ) (M Dm : Matrix (Fin 2) (Fin 2) ℝ) (hM : M.det ≠ 0)
    (hgM : (g : Matrix (Fin 2) (Fin 2) ℝ) * M = M * Dm) (h1 : Dm 0 1 = 0) (h2 : Dm 1 0 = 0) (h3 : Dm 0 0 ≠ Dm 1 1) :
    ∃ g0 : GL (Fin 2) ℝ, (g0⁻¹ * g * g0) 0 1 = 0 ∧ (g0⁻¹ * g * g0) 1 0 = 0 ∧ (g0⁻¹ * g * g0) 0 0 ≠ (g0⁻¹ * g * g0) 1 1 := by
  set g0 := Matrix.GeneralLinearGroup.mkOfDetNeZero M hM
  have hv : (g0 : Matrix (Fin 2) (Fin 2) ℝ) = M := rfl
  have e : ((g0⁻¹ * g * g0 : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = Dm := by
    rw [Units.val_mul, Units.val_mul, mul_assoc, hv, hgM, ← mul_assoc, ← hv, Units.inv_mul, one_mul]
  refine ⟨g0, ?_, ?_, ?_⟩ <;> rw [e] <;> assumption

theorem diagz (g : GL (Fin 2) ℝ) (h : 4 * (g : Matrix (Fin 2) (Fin 2) ℝ).det < (g : Matrix (Fin 2) (Fin 2) ℝ).trace ^ 2) :
    ∃ g0 : GL (Fin 2) ℝ, (g0⁻¹ * g * g0) 0 1 = 0 ∧ (g0⁻¹ * g * g0) 1 0 = 0 ∧ (g0⁻¹ * g * g0) 0 0 ≠ (g0⁻¹ * g * g0) 1 1 := by
  rw [Matrix.det_fin_two, Matrix.trace_fin_two] at h
  by_cases hb : g 0 1 = 0
  · have hne : g 0 0 ≠ g 1 1 := by
      intro e; rw [e, hb] at h; nlinarith
    refine diag_of g !![g 0 0 - g 1 1, 0; g 1 0, 1] !![g 0 0, 0; 0, g 1 1] ?_ ?_ (by simp) (by simp) (by simpa using hne)
    · rw [Matrix.det_fin_two_of]; intro e; apply hne; linear_combination e
    · ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, hb] <;> ring
  · have hΔ : 0 < (g 0 0 + g 1 1) ^ 2 - 4 * (g 0 0 * g 1 1 - g 0 1 * g 1 0) := by linarith
    set s := Real.sqrt ((g 0 0 + g 1 1) ^ 2 - 4 * (g 0 0 * g 1 1 - g 0 1 * g 1 0)) with hsd
    have hs : s ^ 2 = (g 0 0 + g 1 1) ^ 2 - 4 * (g 0 0 * g 1 1 - g 0 1 * g 1 0) := Real.sq_sqrt hΔ.le
    have hs0 : 0 < s := Real.sqrt_pos.2 hΔ
    refine diag_of g !![g 0 1, g 0 1; (g 0 0 + g 1 1 + s) / 2 - g 0 0, (g 0 0 + g 1 1 - s) / 2 - g 0 0]
      !![(g 0 0 + g 1 1 + s) / 2, 0; 0, (g 0 0 + g 1 1 - s) / 2] ?_ ?_ (by simp) (by simp) ?_
    · rw [Matrix.det_fin_two_of]; intro e
      have : g 0 1 * s = 0 := by linear_combination -e
      rcases mul_eq_zero.1 this with e' | e'
      · exact hb e'
      · exact hs0.ne' e'
    · ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;>
        first | ring1 | linear_combination (1/4 : ℝ) * hs | linear_combination (-1/4 : ℝ) * hs
    · simp; intro e; linarith

def yco (g0 : GL (Fin 2) ℝ) (w : P) : {y : ℝ // y ≠ 0} := ⟨(g0⁻¹ • w).1.im, (g0⁻¹ • w).2⟩

def fpr (g0 : GL (Fin 2) ℝ) (w : P) : P := g0 • pt 0 (yco g0 w).1 (yco g0 w).2

def proj {I : Type} [DecidableEq I] (g0 : GL (Fin 2) ℝ) (v : I) (z : X I) : X I := Function.update z v (fpr g0 (z v))

def ptE (hc : Continuous fun p : ℝ × {y : ℝ // y ≠ 0} => pt p.1 p.2.1 p.2.2) : ℝ × {y : ℝ // y ≠ 0} ≃ᵐ P where
  toFun p := pt p.1 p.2.1 p.2.2
  invFun z := (z.1.re / z.1.im, ⟨z.1.im, z.2⟩)
  left_inv p := by
    rcases p with ⟨x, y, hy⟩
    refine Prod.ext ?_ (Subtype.ext ?_)
    · simp [pt]; field_simp
    · simp [pt]
  right_inv z := by
    apply Subtype.ext
    apply Complex.ext
    · simp [pt]; field_simp [z.2]
    · simp [pt]
  measurable_toFun := hc.measurable
  measurable_invFun := by
    refine Measurable.prodMk ?_ ?_
    · exact (Complex.measurable_re.comp measurable_subtype_coe).div (Complex.measurable_im.comp measurable_subtype_coe)
    · exact (Complex.measurable_im.comp measurable_subtype_coe).subtype_mk

def smulE (g : GL (Fin 2) ℝ) (h1 : Measurable fun w : P => g • w) (h2 : Measurable fun w : P => g⁻¹ • w) : P ≃ᵐ P where
  toFun w := g • w
  invFun w := g⁻¹ • w
  left_inv w := inv_smul_smul g w
  right_inv w := smul_inv_smul g w
  measurable_toFun := h1
  measurable_invFun := h2

theorem equiv_f (g0 m : GL (Fin 2) ℝ) (h01 : (g0⁻¹ * m * g0) 0 1 = 0) (h10 : (g0⁻¹ * m * g0) 1 0 = 0) (w : P) :
    fpr g0 (m • w) = m • fpr g0 w := by
  have e1 : g0⁻¹ • (m • w) = (g0⁻¹ * m * g0) • (g0⁻¹ • w) := by
    rw [smul_smul, smul_smul]; congr 1; group
  have e2 : m • fpr g0 w = g0 • ((g0⁻¹ * m * g0) • pt 0 (yco g0 w).1 (yco g0 w).2) := by
    rw [fpr, smul_smul, smul_smul]; congr 1; group
  rw [e2, fpr]
  congr 1
  apply Subtype.ext
  rw [diag_smul _ h01 h10]
  show (((g0⁻¹ • (m • w)).1.im : ℝ) : ℂ) * (((0 : ℝ) : ℂ) + Complex.I) = _ * ((((g0⁻¹ • w).1.im : ℝ) : ℂ) * (((0 : ℝ) : ℂ) + Complex.I))
  rw [e1, diag_smul _ h01 h10, Complex.im_ofReal_mul]
  push_cast
  ring

theorem core {I : Type} [Fintype I] [DecidableEq I] [SigmaFinite (volume : Measure P)] (v : I)
    {ν : Measure {y : ℝ // y ≠ 0}} [SFinite ν]
    (E : ℝ × {y : ℝ // y ≠ 0} ≃ᵐ P) (hE : MeasurePreserving E ((volume : Measure ℝ).prod ν) volume)
    (φ : ℝ → ℂ) (hφ : ∫ x, φ x = 0) (fac : I → P → ℂ) (hfac : ∀ x y, fac v (E (x, y)) = φ x)
    (c : ℂ) (b : X I → ℝ)
    (hb : ∀ (z : X I) x y, b (Function.update z v (E (x, y))) = b (Function.update z v (E (0, y))))
    (hint : Integrable (fun z : X I => b z • (c * ∏ i, fac i (z i)))) :
    ∫ z : X I, b z • (c * ∏ i, fac i (z i)) = 0 := by
  let _ : Unique {i // i = v} := ⟨⟨⟨v, rfl⟩⟩, fun a => Subtype.ext a.2⟩
  let Φ : X I ≃ᵐ P × ({i // ¬ i = v} → P) :=
    (MeasurableEquiv.piEquivPiSubtypeProd (fun _ : I => P) (fun i => i = v)).trans
      (MeasurableEquiv.prodCongr (MeasurableEquiv.funUnique {i // i = v} P) (MeasurableEquiv.refl _))
  have hΦm : MeasurePreserving Φ volume ((volume : Measure P).prod volume) := by
    have h1 := measurePreserving_piEquivPiSubtypeProd (fun _ : I => (volume : Measure P)) (fun i => i = v)
    have h2 : MeasurePreserving (Prod.map (MeasurableEquiv.funUnique {i // i = v} P) id)
        ((@Measure.pi {i // i = v} (fun _ => P) (Subtype.fintype (fun i => i = v)) _ fun _ => (volume : Measure P)).prod
          (Measure.pi fun _ : {i // ¬ i = v} => (volume : Measure P)))
        ((volume : Measure P).prod (Measure.pi fun _ : {i // ¬ i = v} => (volume : Measure P))) := by
      convert (measurePreserving_funUnique (volume : Measure P) {i // i = v}).prod
        (MeasurePreserving.id (Measure.pi fun _ : {i // ¬ i = v} => (volume : Measure P))) <;> rfl
    exact h2.comp h1
  have hΦapp : ∀ z : X I, Φ z = (z v, fun i => z i.1) := fun z => rfl
  have hΦs : ∀ w r, Φ.symm (w, r) = Function.update (Φ.symm (iP, r)) v w := by
    intro w r
    apply Φ.injective
    have h0 := Φ.apply_symm_apply (iP, r)
    rw [Φ.apply_symm_apply, hΦapp]
    rw [hΦapp] at h0
    refine Prod.ext ?_ ?_
    · show w = Function.update (Φ.symm (iP, r)) v w v
      rw [Function.update_self]
    · funext i
      have h1 : Φ.symm (iP, r) i.1 = r i := congrFun (congrArg Prod.snd h0) i
      show r i = Function.update (Φ.symm (iP, r)) v w i.1
      rw [Function.update_of_ne i.2, h1]
  have hsymm := MeasurePreserving.symm Φ hΦm
  have hint2 : Integrable (fun q => b (Φ.symm q) • (c * ∏ i, fac i (Φ.symm q i))) ((volume : Measure P).prod volume) :=
    (hsymm.integrable_comp_emb Φ.symm.measurableEmbedding).2 hint
  have inner : ∀ r, ∫ w, b (Φ.symm (w, r)) • (c * ∏ i, fac i (Φ.symm (w, r) i)) = 0 := by
    intro r
    have e1 : ∀ w, b (Φ.symm (w, r)) • (c * ∏ i, fac i (Φ.symm (w, r) i)) =
        (b (Function.update (Φ.symm (iP, r)) v w) : ℂ) * (c * (fac v w * ∏ i ∈ Finset.univ.erase v, fac i (Φ.symm (iP, r) i))) := by
      intro w
      have hp : ∏ i ∈ Finset.univ.erase v, fac i (Function.update (Φ.symm (iP, r)) v w i) =
          ∏ i ∈ Finset.univ.erase v, fac i (Φ.symm (iP, r) i) :=
        Finset.prod_congr rfl fun i hi => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]
      rw [hΦs w r, Complex.real_smul, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ v), Function.update_self, hp]
    simp_rw [e1]
    generalize (∏ i ∈ Finset.univ.erase v, fac i (Φ.symm (iP, r) i)) = K
    generalize Φ.symm (iP, r) = z0
    rw [← hE.integral_comp']
    have e2 : (fun q : ℝ × {y : ℝ // y ≠ 0} => (b (Function.update z0 v (E q)) : ℂ) * (c * (fac v (E q) * K))) =
        fun q => (fun x : ℝ => c * K * φ x) q.1 * (fun y : {y : ℝ // y ≠ 0} => (b (Function.update z0 v (E (0, y))) : ℂ)) q.2 := by
      funext q; obtain ⟨x, y⟩ := q; simp only [hfac]; rw [hb _ x y]; ring
    rw [e2, integral_prod_mul (fun x : ℝ => c * K * φ x) (fun y : {y : ℝ // y ≠ 0} => (b (Function.update z0 v (E (0, y))) : ℂ)),
      integral_const_mul, hφ]
    simp
  rw [← hsymm.integral_comp', integral_prod_symm _ hint2]
  simp only [inner, integral_zero]

end UpperTheory.Esk.DiagonalTermsContribution

open UpperTheory.Esk.DiagonalTermsContribution in
theorem UpperTheory.Esk.diagonal_terms_contribution_proof : UpperTheory.Esk.B1a → UpperTheory.Esk.B1b → UpperTheory.Esk.UpperHalfPlaneMeasureCoordinates → UpperTheory.Esk.DiagonalIntegrandVanishes → UpperTheory.Esk.C1 → UpperTheory.Esk.E0a → UpperTheory.Esk.KernelTermsInvariantBounded → UpperTheory.Esk.Ecut → UpperTheory.Esk.Fcen → UpperTheory.Esk.F2 := by
  classical
  intro hB1a hB1b hB5a hB5b hC1 hE0a hE0c hEcut hFcen
  intro F I Gf ι _ _ _ _ D k a hyp γ ω hTE β hβ hint
  obtain ⟨hcount, -, hpres, -, -, -, -, -⟩ := hE0a F I Gf D hyp.ax
  obtain ⟨-, hconj, hmeas, -, hsupp, hreg⟩ := hE0c F I Gf ι D k a hyp
  obtain ⟨hsfP, -, hB1g⟩ := hB1a
  haveI := hsfP
  haveI : Countable (PG F) := hcount
  have hu : ∀ z : D.Xs, D.kk k a γ (ω, z) = D.Te a γ.out (D.rep ω) *
      ∏ i, (q1 (k i) ((z : X I) i) (D.r i γ.out • (z : X I) i) * j1 (k i) (D.r i γ.out) ((z : X I) i)) := by
    intro z
    show D.Te a γ.out (D.rep ω) * (qq k z (D.act γ.out z) * D.J k γ.out z) = _
    unfold qq Dat.J
    rw [← Finset.prod_mul_distrib]; rfl
  by_cases hT : D.Te a γ.out (D.rep ω) = 0
  · simp [hu, hT]
  obtain ⟨i0, hi0⟩ := hsupp γ ω hT
  obtain ⟨htr, htr2⟩ := hreg γ ω i0 hi0
  have rapp : ∀ v (δ : GL (Fin 2) F) (i j : Fin 2), (D.r v δ : Matrix (Fin 2) (Fin 2) ℝ) i j = D.σ v ((δ : Matrix (Fin 2) (Fin 2) F) i j) :=
    fun _ _ _ _ => rfl
  obtain ⟨v, hv⟩ : ∃ v, 4 * (D.r v γ.out : Matrix (Fin 2) (Fin 2) ℝ).det < (D.r v γ.out : Matrix (Fin 2) (Fin 2) ℝ).trace ^ 2 := by
    unfold Dat.TotEll at hTE
    push_neg at hTE
    obtain ⟨v, hv⟩ := hTE
    refine ⟨v, ?_⟩
    have e1 : (D.r v γ.out : Matrix (Fin 2) (Fin 2) ℝ).det = D.σ v (γ.out : Matrix (Fin 2) (Fin 2) F).det := by
      rw [Matrix.det_fin_two, Matrix.det_fin_two, rapp, rapp, rapp, rapp]; simp
    have e2 : (D.r v γ.out : Matrix (Fin 2) (Fin 2) ℝ).trace = D.σ v (γ.out : Matrix (Fin 2) (Fin 2) F).trace := by
      rw [Matrix.trace_fin_two, Matrix.trace_fin_two, rapp, rapp]; simp
    rw [e1, e2]
    refine lt_of_le_of_ne hv fun h => htr2 ((D.σ v).injective ?_).symm
    rw [map_mul, map_pow, map_ofNat]; exact h
  obtain ⟨g0, h01, h10, hne⟩ := diagz _ hv
  obtain ⟨φ, -, hφeq, -, -, hφ0, -⟩ := hB5b (k v) (hyp.four v) (g0⁻¹ * D.r v γ.out * g0) h01 h10 hne
  obtain ⟨-, hcutS⟩ := hEcut F I Gf D hyp.ax
  have hSmem : ∀ δ : PG F, δ ∈ MulAction.stabilizer (PG F) ((γ, ω) : D.Cj × D.Om) → δ * γ * δ⁻¹ = γ ∧ δ • ω = ω := by
    intro δ hδ
    have h := (MulAction.mem_stabilizer_iff).1 hδ
    exact ⟨congrArg (fun p : D.Cj × D.Om => D.el p.1) h, congrArg Prod.snd h⟩
  set S := MulAction.stabilizer (PG F) ((γ, ω) : D.Cj × D.Om) with hS
  obtain ⟨β0, hβ0⟩ := hcutS ω (MulAction.stabilizer (PG F) ((γ, ω) : D.Cj × D.Om)) fun δ hδ => (hSmem δ hδ).2
  have hcomm : ∀ δ : PG F, δ ∈ MulAction.stabilizer (PG F) ((γ, ω) : D.Cj × D.Om) →
      D.r v δ.out * D.r v γ.out = D.r v γ.out * D.r v δ.out := by
    intro δ hδ
    have h1 := (hSmem δ hδ).1
    have h2 : ((δ.out : GL (Fin 2) F) : PG F) * (γ.out : PG F) * ((δ.out : GL (Fin 2) F) : PG F)⁻¹ = (γ.out : PG F) := by
      simpa only [QuotientGroup.out_eq'] using h1
    rw [← map_mul, hFcen F γ.out δ.out htr h2, map_mul]
  have hdiag : ∀ δ : PG F, δ ∈ MulAction.stabilizer (PG F) ((γ, ω) : D.Cj × D.Om) →
      (g0⁻¹ * D.r v δ.out * g0) 0 1 = 0 ∧ (g0⁻¹ * D.r v δ.out * g0) 1 0 = 0 := by
    intro δ hδ
    apply comm_diag _ _ h01 h10 hne
    simp only [mul_assoc, mul_inv_cancel_left]
    rw [← mul_assoc (D.r v δ.out) (D.r v γ.out) g0, hcomm δ hδ, mul_assoc]
  have hact : ∀ (δ : PG F) (z : D.Xs) (i : I), (δ • z : X I) i = D.r i δ.out • (z : X I) i := by
    intro δ z i
    conv_lhs => rw [← QuotientGroup.out_eq' δ]
    rfl
  have hsm : ∀ h : GL (Fin 2) ℝ, Continuous (fun w : P => h • w) := fun h => (hB1g h).1
  have hyco : Continuous (yco g0) :=
    Continuous.subtype_mk (Complex.continuous_im.comp (continuous_subtype_val.comp (hsm g0⁻¹))) _
  have hfpr : Continuous (fpr g0) := (hsm g0).comp (hB5a.2.2.comp (continuous_const.prodMk hyco))
  have hpm : Measurable (proj g0 v : X I → X I) := (continuous_id.update v (hfpr.comp (continuous_apply v))).measurable
  have hactS : ∀ (δ : S) (z : D.Xs) (i : I), (δ • z : X I) i = D.r i (δ : PG F).out • (z : X I) i :=
    fun δ z i => hact δ z i
  have hpeq : ∀ (δ : S) (z : D.Xs) (i : I), proj g0 v (δ • z) i = D.r i (δ : PG F).out • proj g0 v z i := by
    intro δ z i
    by_cases hi : i = v
    · rw [hi]
      have l1 : proj g0 v (δ • z) v = fpr g0 ((δ • z : X I) v) := Function.update_self _ _ _
      have l2 : proj g0 v z v = fpr g0 ((z : X I) v) := Function.update_self _ _ _
      rw [l1, l2, hactS δ z v]
      exact equiv_f g0 _ (hdiag δ δ.2).1 (hdiag δ δ.2).2 _
    · have l1 : proj g0 v (δ • z) i = (δ • z : X I) i := Function.update_of_ne hi _ _
      have l2 : proj g0 v z i = (z : X I) i := Function.update_of_ne hi _ _
      rw [l1, l2]
      exact hactS δ z i
  have hβ' : IsCut (MulAction.stabilizer (PG F) ((γ, ω) : D.Cj × D.Om)) (fun z : D.Xs => β0 (proj g0 v z)) := by
    refine ⟨hβ0.meas.comp hpm, fun z => hβ0.nonneg _, fun z => ?_⟩
    have hfun : (fun δ : S => β0 (proj g0 v (δ • z))) = fun δ : S => β0 (δ • (show D.Xs from proj g0 v z)) :=
      funext fun δ => congrArg β0 (funext fun i => (hpeq δ z i).trans (hactS δ (proj g0 v z) i).symm)
    show HasSum (fun δ : S => β0 (proj g0 v (δ • z))) 1
    rw [hfun]
    exact hβ0.sum _
  have hpresS : Pres (MulAction.stabilizer (PG F) ((γ, ω) : D.Cj × D.Om)) (volume : Measure D.Xs) :=
    fun δ => hpres (δ : PG F)
  have hum : Measurable (fun z : D.Xs => D.kk k a γ (ω, z)) := (hmeas γ).comp (measurable_const.prodMk measurable_id)
  have hinv : ∀ (δ : MulAction.stabilizer (PG F) ((γ, ω) : D.Cj × D.Om)) (z : D.Xs),
      D.kk k a γ (ω, δ • z) = D.kk k a γ (ω, z) := by
    intro δ z
    obtain ⟨h1, h2⟩ := hSmem δ δ.2
    have := hconj δ γ (ω, z)
    rw [h1] at this
    rw [← this, Prod.smul_mk, h2]
    rfl
  obtain ⟨hint', heq⟩ := (hC1 (MulAction.stabilizer (PG F) ((γ, ω) : D.Cj × D.Om)) D.Xs volume hpresS β
    (fun z : D.Xs => β0 (proj g0 v z)) hβ hβ').2 (fun z : D.Xs => D.kk k a γ (ω, z)) hum hinv hint
  refine heq.trans ?_
  let fac : I → P → ℂ := fun i w => q1 (k i) w (D.r i γ.out • w) * j1 (k i) (D.r i γ.out) w
  have hint'' : Integrable (fun z : D.Xs => β0 (proj g0 v z) • (D.Te a γ.out (D.rep ω) * ∏ i, fac i (z i))) := by
    refine hint'.congr (Filter.Eventually.of_forall fun z => ?_)
    simp only [hu]; rfl
  have e3 : ∫ z : D.Xs, β0 (proj g0 v z) • D.kk k a γ (ω, z) =
      ∫ z : X I, β0 (proj g0 v z) • (D.Te a γ.out (D.rep ω) * ∏ i, fac i (z i)) := by
    congr 1; funext z; rw [hu z]
  have hmeasg : ∀ h : GL (Fin 2) ℝ, Measurable (fun w : P => h • w) := fun h => (hsm h).measurable
  let E : ℝ × {y : ℝ // y ≠ 0} ≃ᵐ P := (ptE hB5a.2.2).trans (smulE g0 (hmeasg g0) (hmeasg g0⁻¹))
  have hEapp : ∀ x y (hy : y ≠ 0), E (x, ⟨y, hy⟩) = g0 • pt x y hy := fun _ _ _ => rfl
  have hE : MeasurePreserving E _ volume := (hB1g g0).2.comp hB5a.1
  have hfE : ∀ x y, fpr g0 (E (x, y)) = E (0, y) := by
    rintro x ⟨y, hy⟩
    have hy' : (yco g0 (E (x, ⟨y, hy⟩))).1 = y := by
      show (g0⁻¹ • E (x, ⟨y, hy⟩)).1.im = y
      rw [hEapp, inv_smul_smul]
      simp [pt]
    rw [fpr, hEapp 0 y hy]
    congr 1
    apply Subtype.ext
    show ((yco g0 (E (x, ⟨y, hy⟩))).1 : ℂ) * (((0 : ℝ) : ℂ) + Complex.I) = (y : ℂ) * (((0 : ℝ) : ℂ) + Complex.I)
    rw [hy']
  obtain ⟨hcoc, hjne, hq, -⟩ := hB1b
  have hs0 : IsOpen {y : ℝ | y ≠ 0} := isOpen_compl_singleton
  haveI : LocallyCompactSpace {y : ℝ // y ≠ 0} := hs0.locallyCompactSpace
  haveI : IsFiniteMeasureOnCompacts (Measure.comap (Subtype.val : {y : ℝ // y ≠ 0} → ℝ) volume) :=
    .comap' _ continuous_subtype_val (MeasurableEmbedding.subtype_coe hs0.measurableSet)
  have hfac : ∀ x y, fac v (E (x, y)) = φ x := by
    rintro x ⟨y, hy⟩
    rw [← hφeq x y hy, hEapp]
    show q1 (k v) (g0 • pt x y hy) (D.r v γ.out • g0 • pt x y hy) * j1 (k v) (D.r v γ.out) (g0 • pt x y hy) = _
    have hgd : D.r v γ.out * g0 = g0 * (g0⁻¹ * D.r v γ.out * g0) := by group
    have e1 : D.r v γ.out • g0 • pt x y hy = g0 • (g0⁻¹ * D.r v γ.out * g0) • pt x y hy := by
      rw [smul_smul, smul_smul, hgd]
    rw [e1]
    have A := hcoc (k v) (D.r v γ.out) g0 (pt x y hy)
    rw [hgd] at A
    have B := hcoc (k v) g0 (g0⁻¹ * D.r v γ.out * g0) (pt x y hy)
    have C := hq (k v) g0 (pt x y hy) ((g0⁻¹ * D.r v γ.out * g0) • pt x y hy)
    apply mul_right_cancel₀ (hjne (k v) g0 (pt x y hy))
    linear_combination (-(q1 (k v) (g0 • pt x y hy) (g0 • (g0⁻¹ * D.r v γ.out * g0) • pt x y hy))) * A +
      q1 (k v) (g0 • pt x y hy) (g0 • (g0⁻¹ * D.r v γ.out * g0) • pt x y hy) * B +
      j1 (k v) (g0⁻¹ * D.r v γ.out * g0) (pt x y hy) * C
  have hb : ∀ (z : X I) x y, β0 (proj g0 v (Function.update z v (E (x, y)))) =
      β0 (proj g0 v (Function.update z v (E (0, y)))) := by
    intro z x y
    simp only [proj, Function.update_idem, Function.update_self, hfE]
  rw [e3]
  exact core v E hE φ hφ0 fac hfac _ (fun z => β0 (proj g0 v z)) hb hint''
