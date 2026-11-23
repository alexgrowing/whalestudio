import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.MultivariableReproducingFormula

noncomputable section

open MeasureTheory Matrix
open scoped ENNReal NNReal ComplexConjugate

namespace UpperTheory.Esk.ImaginaryPartBound

open UpperTheory.Esk

theorem fixed_pt (g : GL (Fin 2) ℝ) (h : g.val.trace ^ 2 < 4 * g.val.det) : ∃ z : P, g • z = z := by
  have ht : g.val.trace = g 0 0 + g 1 1 := Matrix.trace_fin_two _
  have hd : g.val.det = g 0 0 * g 1 1 - g 0 1 * g 1 0 := det_eq g
  rw [ht, hd] at h
  have hc : g 1 0 ≠ 0 := by
    intro hc
    rw [hc] at h
    nlinarith [sq_nonneg (g 0 0 - g 1 1)]
  have hs0 : 0 < 4 * (g 0 0 * g 1 1 - g 0 1 * g 1 0) - (g 0 0 + g 1 1) ^ 2 := by linarith
  set s := Real.sqrt (4 * (g 0 0 * g 1 1 - g 0 1 * g 1 0) - (g 0 0 + g 1 1) ^ 2) with hs_def
  have hspos : 0 < s := Real.sqrt_pos.mpr hs0
  have hs2 : s ^ 2 = 4 * (g 0 0 * g 1 1 - g 0 1 * g 1 0) - (g 0 0 + g 1 1) ^ 2 := Real.sq_sqrt hs0.le
  have h2c : ((2 * g 1 0 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast mul_ne_zero two_ne_zero hc
  set zc : ℂ := (((g 0 0 - g 1 1 : ℝ) : ℂ) + (s : ℂ) * Complex.I) / ((2 * g 1 0 : ℝ) : ℂ) with hzc
  have him : zc.im = s / (2 * g 1 0) := by
    rw [hzc]
    rw [Complex.div_ofReal_im]; simp
  have hz : zc.im ≠ 0 := by
    rw [him]; exact div_ne_zero hspos.ne' (mul_ne_zero two_ne_zero hc)
  have hz2 : ((2 * g 1 0 : ℝ) : ℂ) * zc = ((g 0 0 - g 1 1 : ℝ) : ℂ) + (s : ℂ) * Complex.I := by
    rw [hzc, mul_comm]; exact div_mul_cancel₀ _ h2c
  push_cast at hz2
  have hs2C : (s : ℂ) ^ 2 = 4 * ((g 0 0 : ℂ) * g 1 1 - g 0 1 * g 1 0) - (g 0 0 + g 1 1) ^ 2 := by
    exact_mod_cast hs2
  have hQ : (4 * (g 1 0 : ℂ)) * ((g 1 0 : ℂ) * zc ^ 2 - ((g 0 0 : ℂ) - g 1 1) * zc - g 0 1) = 0 := by
    linear_combination (2 * (g 1 0 : ℂ) * zc + (s : ℂ) * Complex.I - ((g 0 0 : ℂ) - g 1 1)) * hz2
      + (s : ℂ) ^ 2 * Complex.I_sq - hs2C
  have h4c : (4 : ℂ) * (g 1 0 : ℂ) ≠ 0 := mul_ne_zero (by norm_num) (by exact_mod_cast hc)
  have hQ0 := (mul_eq_zero.mp hQ).resolve_left h4c
  let zP : P := ⟨zc, hz⟩
  refine ⟨zP, Subtype.ext ?_⟩
  change (g • zP).1 = zc
  rw [coe_smul]
  change num g zc / den g zc = zc
  rw [div_eq_iff (den_ne g hz)]
  simp only [num, den]
  linear_combination (-1 : ℂ) * hQ0

theorem no_eig {F : Type} [Field F] {I : Type} (σ : I → F →+* ℝ) (v : I) (γ : GL (Fin 2) F)
    (h : σ v γ.val.trace ^ 2 < 4 * σ v γ.val.det) (s : Fin 2 → F) (hs : s ≠ 0) (c : F) : s ᵥ* γ.val ≠ c • s := by
  intro heq
  set M := γ.val with hM
  have h0 : s 0 * M 0 0 + s 1 * M 1 0 = c * s 0 := by
    have := congrFun heq 0
    simpa [Matrix.vecMul, dotProduct, Fin.sum_univ_two] using this
  have h1 : s 0 * M 0 1 + s 1 * M 1 1 = c * s 1 := by
    have := congrFun heq 1
    simpa [Matrix.vecMul, dotProduct, Fin.sum_univ_two] using this
  have hp : c ^ 2 - (M 0 0 + M 1 1) * c + (M 0 0 * M 1 1 - M 0 1 * M 1 0) = 0 := by
    have hs' : s 0 ≠ 0 ∨ s 1 ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hs (funext fun i => by fin_cases i <;> simp [hcon.1, hcon.2])
    rcases hs' with h' | h'
    · have : s 0 * (c ^ 2 - (M 0 0 + M 1 1) * c + (M 0 0 * M 1 1 - M 0 1 * M 1 0)) = 0 := by
        linear_combination (M 1 1 - c) * h0 - M 1 0 * h1
      exact (mul_eq_zero.mp this).resolve_left h'
    · have : s 1 * (c ^ 2 - (M 0 0 + M 1 1) * c + (M 0 0 * M 1 1 - M 0 1 * M 1 0)) = 0 := by
        linear_combination (M 0 0 - c) * h1 - M 0 1 * h0
      exact (mul_eq_zero.mp this).resolve_left h'
  have hσ := congrArg (σ v) hp
  simp only [map_add, map_sub, map_mul, map_pow, map_zero] at hσ
  rw [Matrix.trace_fin_two, Matrix.det_fin_two] at h
  simp only [map_add, map_sub, map_mul] at h
  nlinarith [sq_nonneg (2 * σ v c - (σ v (M 0 0) + σ v (M 1 1)))]

theorem kap_lb (C c U : ℝ) (hc : 0 < c) (z w : P) (hz : |z.1.re| ≤ C ∧ c ≤ |z.1.im| ∧ |z.1.im| ≤ U)
    (hw : |w.1.re| ≤ C ∧ c ≤ |w.1.im| ∧ |w.1.im| ≤ U) (hzw : 0 < z.1.im * w.1.im) :
    c ^ 2 / (C ^ 2 + U ^ 2) ≤ kap z w := by
  obtain ⟨hzr, hzi1, hzi2⟩ := hz
  obtain ⟨hwr, hwi1, hwi2⟩ := hw
  unfold kap
  rw [if_pos hzw]
  have hnorm : ‖z.1 - conj w.1‖ ^ 2 = (z.1.re - w.1.re) ^ 2 + (z.1.im + w.1.im) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; simp; ring
  rw [hnorm]
  have habs : z.1.im * w.1.im = |z.1.im| * |w.1.im| := by rw [← abs_mul, abs_of_pos hzw]
  have hp : c ^ 2 ≤ z.1.im * w.1.im := by
    rw [habs]; nlinarith [mul_le_mul hzi1 hwi1 hc.le (abs_nonneg _)]
  have hU0 : 0 ≤ U := le_trans (abs_nonneg _) hzi2
  have hU : 0 < U := by linarith
  have hzr' := abs_le.mp hzr
  have hwr' := abs_le.mp hwr
  have hre : (z.1.re - w.1.re) ^ 2 ≤ 4 * C ^ 2 := by
    nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ 2 * C - (z.1.re - w.1.re))
      (by linarith : (0:ℝ) ≤ 2 * C + (z.1.re - w.1.re))]
  have him2 : (z.1.im + w.1.im) ^ 2 ≤ 4 * U ^ 2 := by
    nlinarith [sq_abs z.1.im, sq_abs w.1.im, mul_le_mul hzi2 hzi2 (abs_nonneg _) hU0,
      mul_le_mul hwi2 hwi2 (abs_nonneg _) hU0, mul_le_mul hzi2 hwi2 (abs_nonneg _) hU0]
  have hden : 0 < (z.1.re - w.1.re) ^ 2 + (z.1.im + w.1.im) ^ 2 := by
    nlinarith [sq_nonneg (z.1.re - w.1.re), sq_nonneg z.1.im, sq_nonneg w.1.im]
  have hCU : 0 < C ^ 2 + U ^ 2 := by positivity
  rw [div_le_div_iff₀ hCU hden]
  nlinarith [mul_le_mul_of_nonneg_left (add_le_add hre him2) (sq_nonneg c),
    mul_le_mul_of_nonneg_right hp hCU.le]

end UpperTheory.Esk.ImaginaryPartBound

namespace UpperTheory.Esk.ImaginaryPartBound

open UpperTheory.Esk

variable {F I Gf : Type} [Field F] [Group Gf] [Fintype I] (D : Dat F I Gf)

theorem smul_X (γ : PG F) (z : D.Xs) (v : I) : (γ • z : X I) v = D.r v γ.out • (z : X I) v := by
  have hγ : ((γ.out : GL (Fin 2) F) : PG F) = γ := by
    exact QuotientGroup.out_eq' γ
  have := congrArg (fun g : PG F => ((g • z : D.Xs) : X I) v) hγ
  try simp only at this
  rw [← this, Dat.mk_smulX]
  rfl

theorem rep_spec (ω : D.Om) : ((D.rep ω : Gf) : Gf ⧸ D.H) = ω := by
  unfold Dat.rep
  exact Quotient.out_eq ω

theorem kap_inv (hB : B1b) (γ : PG F) (z w : D.Xs) (v : I) :
    kap ((γ • z : X I) v) ((γ • w : X I) v) = kap ((z : X I) v) ((w : X I) v) := by
  rw [smul_X D, smul_X D]
  exact hB.2.2.2.1 _ _ _

theorem fixX (γ : PG F) (hell : D.TotEll γ.out) : ∃ z : D.Xs, γ • z = z := by
  have hfx : ∀ v, ∃ w : P, D.r v γ.out • w = w := by
    intro v
    apply fixed_pt
    have ht : (D.r v γ.out).val.trace = D.σ v γ.out.val.trace := by
      rw [Matrix.trace_fin_two, Matrix.trace_fin_two, map_add]; rfl
    have hd : (D.r v γ.out).val.det = D.σ v γ.out.val.det := by
      rw [Matrix.det_fin_two, Matrix.det_fin_two, map_sub, map_mul, map_mul]; rfl
    rw [ht, hd]
    exact hell v
  choose w hw using hfx
  refine ⟨w, ?_⟩
  funext v
  exact (smul_X D γ w v).trans (hw v)

theorem near_of (hB : B1b) (hC : B1c) (γ1 γ2 : PG F) (z1 z2 : D.Xs) (h1 : γ1 • z1 = z1) (h2 : γ2 • z2 = z2)
    (δ : ℝ) (hδ : 0 ≤ δ) (hk : ∀ v, δ ≤ kap ((z1 : X I) v) ((z2 : X I) v)) :
    Near (δ ^ 2 / 4) z1 ((γ1⁻¹ * γ2) • z1 : D.Xs) := by
  intro v
  have k1 : kap ((z1 : X I) v) (((γ1⁻¹ * γ2) • z1 : D.Xs) v) = kap ((z1 : X I) v) ((γ2 • z1 : D.Xs) v) := by
    have := kap_inv D hB γ1 z1 ((γ1⁻¹ * γ2) • z1) v
    rw [h1, ← mul_smul, mul_inv_cancel_left] at this
    exact this.symm
  have k2 : kap ((z2 : X I) v) ((γ2 • z1 : D.Xs) v) = kap ((z2 : X I) v) ((z1 : X I) v) := by
    have := kap_inv D hB γ2 z2 z1 v
    rwa [h2] at this
  have hsym := (hC.1 ((z1 : X I) v) ((z2 : X I) v)).2.2
  have htri := hC.2.2.1 ((z1 : X I) v) ((z2 : X I) v) ((γ2 • z1 : D.Xs) v)
  have hk2 : δ ≤ kap ((z2 : X I) v) ((γ2 • z1 : D.Xs) v) := by rw [k2, ← hsym]; exact hk v
  have hprod : δ * δ ≤ kap ((z1 : X I) v) ((z2 : X I) v) * kap ((z2 : X I) v) ((γ2 • z1 : D.Xs) v) :=
    mul_le_mul (hk v) hk2 hδ (le_trans hδ (hk v))
  show δ ^ 2 / 4 ≤ kap ((z1 : X I) v) (((γ1⁻¹ * γ2) • z1 : D.Xs) v)
  rw [k1]
  nlinarith

theorem bound_im [Nonempty I] {C c : ℝ} (hc : 0 < c) (z : X I) (hz : Sg C c z) (B : ℝ)
    (hB : ∏ v, |(z v).1.im| ≤ B) (v : I) : |(z v).1.im| ≤ C * max 1 B := by
  obtain ⟨v0, hv0⟩ := Finite.exists_min (fun u => |(z u).1.im|)
  have hC0 : 0 ≤ C := le_trans (abs_nonneg _) (hz v).1
  have h1 := (hz v).2.2 v0
  suffices hm : |(z v0).1.im| ≤ max 1 B from h1.trans (mul_le_mul_of_nonneg_left hm hC0)
  by_cases hle : |(z v0).1.im| ≤ 1
  · exact hle.trans (le_max_left _ _)
  · push Not at hle
    have hP : |(z v0).1.im| ^ (Finset.univ : Finset I).card ≤ ∏ u, |(z u).1.im| := by
      calc |(z v0).1.im| ^ (Finset.univ : Finset I).card = ∏ _u : I, |(z v0).1.im| := (Finset.prod_const _).symm
        _ ≤ ∏ u, |(z u).1.im| := Finset.prod_le_prod (fun _ _ => abs_nonneg _) (fun u _ => hv0 u)
    have hcard : (Finset.univ : Finset I).card ≠ 0 := Finset.card_ne_zero.mpr Finset.univ_nonempty
    have hself : |(z v0).1.im| ≤ |(z v0).1.im| ^ (Finset.univ : Finset I).card := by
      exact le_self_pow₀ hle.le hcard
    exact le_max_of_le_right (hself.trans (hP.trans hB))

theorem htY_e (ω : D.Om) (z : D.Xs) :
    D.HtY ![0, 1] (ω, z) = (∏ v, |((z : X I) v).1.im|) * D.hf ![0, 1] (D.rep ω) := by
  simp [Dat.HtY, Dat.Ht]

end UpperTheory.Esk.ImaginaryPartBound

namespace UpperTheory.Esk.ImaginaryPartBound

open UpperTheory.Esk

variable {F I Gf : Type} [Field F] [Group Gf] [Fintype I] (D : Dat F I Gf)

def W (S0 : Finset Gf) : Set D.Om := (fun x : Gf => (show D.Om from ((x : Gf) : Gf ⧸ D.H))) '' (S0 : Set Gf)

def T (a : Gf) (ω : D.Om) : Set D.Om := {ω3 | ∃ h ∈ D.H, ω3 = (show D.Om from ((D.rep ω * h * a : Gf) : Gf ⧸ D.H))}

def Good (C c Cm : ℝ) (W : Set D.Om) (a : Gf) (q : (D.Cj × D.Om) × D.Xs) : Prop :=
  D.el q.1.1 • q.2 = q.2 ∧ Sg C c q.2 ∧ q.1.2 ∈ W ∧ D.HtY ![0, 1] (q.1.2, q.2) ^ 2 ≤ Cm ∧ D.el q.1.1 • q.1.2 ∈ T D a q.1.2

theorem e_ne : (![0, 1] : Fin 2 → F) ≠ 0 := by
  intro h
  have := congrFun h 1
  simp at this

theorem Tmem (a : Gf) (δ : GL (Fin 2) F) (γ : PG F) (ω : D.Om)
    (hs : γ • ω = (show D.Om from ((D.rep ω * a : Gf) : Gf ⧸ D.H))) :
    ((δ : PG F) * γ * (δ : PG F)⁻¹) • ((δ : PG F) • ω) ∈ T D a ((δ : PG F) • ω) := by
  have hω' : ((δ : PG F) • ω) = ((D.j δ * D.rep ω : Gf) : Gf ⧸ D.H) := by
    have := Dat.mk_smulO D δ (D.rep ω)
    try simp only at this
    rw [rep_spec D ω] at this
    exact this
  have hmem : (D.rep ((δ : PG F) • ω))⁻¹ * (D.j δ * D.rep ω) ∈ D.H :=
    QuotientGroup.eq.mp ((rep_spec D _).trans hω')
  refine ⟨_, hmem, ?_⟩
  rw [mul_smul, mul_smul, inv_smul_smul, hs]
  have h2 := Dat.mk_smulO D δ (D.rep ω * a)
  try simp only at h2
  try simp only
  rw [h2, mul_inv_cancel_left, mul_assoc]

theorem fix_of_10 (M : Matrix (Fin 2) (Fin 2) F) (h : M 1 0 = 0) : ![0, 1] ᵥ* M = M 1 1 • ![0, 1] := by
  funext i
  fin_cases i <;> simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two, h]

theorem vecMul_ne (δ : GL (Fin 2) F) : (![0, 1] : Fin 2 → F) ᵥ* δ.val ≠ 0 := by
  intro h
  apply e_ne (F := F)
  have := congrArg (fun x => x ᵥ* (δ⁻¹ : GL (Fin 2) F).val) h
  simp [Matrix.vecMul_vecMul] at this

theorem conj_10 (hE : E0d) (hD : D.Ax) (γ : PG F) (hell : D.TotEll γ.out) (δ : GL (Fin 2) F) :
    ((δ : PG F) * γ * (δ : PG F)⁻¹).out 1 0 ≠ 0 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, h11⟩ := hE F I Gf D hD
  have : Nontrivial I := hD.two
  obtain ⟨v⟩ : Nonempty I := inferInstance
  intro h0
  have hγ : ((γ.out : GL (Fin 2) F) : PG F) = γ := by
    exact QuotientGroup.out_eq' γ
  have hfix : Fix ![0, 1] ((δ : PG F) * ((γ.out : GL (Fin 2) F) : PG F) * (δ : PG F)⁻¹) := by
    rw [hγ]
    exact ⟨_, fix_of_10 _ h0⟩
  obtain ⟨c', hc'⟩ := (h11 _ γ.out δ).mp hfix
  exact no_eig D.σ v γ.out (hell v) _ (vecMul_ne δ) c' hc'

theorem htBound (hE : E0d) (hD : D.Ax) (a : Gf) (Cm : ℝ) (hCm : ∀ s, s ≠ 0 → ∀ x, D.hf s (x * a⁻¹) ≤ Cm * D.hf s x)
    (γ : PG F) (ω : D.Om) (z : D.Xs) (hfix : γ • z = z) (h10 : γ.out 1 0 ≠ 0) (hT : γ • ω ∈ T D a ω) :
    D.HtY ![0, 1] (ω, z) ^ 2 ≤ Cm := by
  obtain ⟨-, h2, -, h4, h5, -⟩ := hE F I Gf D hD
  have he : (![0, 1] : Fin 2 → F) ≠ 0 := e_ne
  have hγ : ((γ.out : GL (Fin 2) F) : PG F) = γ := by
    exact QuotientGroup.out_eq' γ
  have hB := h2 _ he γ.out (ω, z)
  rw [hγ] at hB
  have hsm : γ • ((ω, z) : D.Y) = (γ • ω, z) := by rw [Prod.smul_mk, hfix]
  rw [hsm] at hB
  have he0 : (![0, 1] ᵥ* γ.out.val) 0 * (![0, 1] : Fin 2 → F) 1
      - (![0, 1] ᵥ* γ.out.val) 1 * (![0, 1] : Fin 2 → F) 0 ≠ 0 := by
    simpa [Matrix.vecMul, dotProduct, Fin.sum_univ_two] using h10
  have hprod := h5 _ _ he0 (ω, z)
  rw [← hB] at hprod
  have hpos1 := h4 _ he (ω, z)
  have hpos2 := h4 _ he (γ • ω, z)
  obtain ⟨h, hh, hω⟩ := hT
  have hq : ((D.rep ω * h * a : Gf) : Gf ⧸ D.H) = ((D.rep (γ • ω) : Gf) : Gf ⧸ D.H) := by
    rw [rep_spec D]; exact hω.symm
  have hf1 : D.hf ![0, 1] (D.rep (γ • ω)) = D.hf ![0, 1] (D.rep ω * h * a) := by
    have := hD.lev _ he (D.rep ω * h * a) _ (QuotientGroup.eq.mp hq)
    rwa [mul_inv_cancel_left] at this
  have hf2 : D.hf ![0, 1] (D.rep ω) ≤ Cm * D.hf ![0, 1] (D.rep ω * h * a) := by
    have := hCm _ he (D.rep ω * h * a)
    rwa [mul_inv_cancel_right, hD.lev _ he _ h hh] at this
  simp only [htY_e D] at hprod hpos1 hpos2 ⊢
  rw [hf1] at hprod hpos2
  have hP0 : 0 ≤ ∏ v, |((z : X I) v).1.im| := Finset.prod_nonneg fun _ _ => abs_nonneg _
  have k1 : (∏ v, |((z : X I) v).1.im|) * D.hf ![0, 1] (D.rep ω)
      ≤ Cm * ((∏ v, |((z : X I) v).1.im|) * D.hf ![0, 1] (D.rep ω * h * a)) := by
    nlinarith [mul_le_mul_of_nonneg_left hf2 hP0]
  have hCm0 : 0 ≤ Cm := by
    by_contra hneg
    push Not at hneg
    nlinarith [mul_neg_of_neg_of_pos hneg hpos2]
  nlinarith [mul_le_mul_of_nonneg_right k1 hpos1.le, mul_le_mul_of_nonneg_left hprod hCm0]

end UpperTheory.Esk.ImaginaryPartBound

namespace UpperTheory.Esk.ImaginaryPartBound

open UpperTheory.Esk

variable {F I Gf : Type} [Field F] [Group Gf] [Fintype I] (D : Dat F I Gf)

def key (q : (D.Cj × D.Om) × D.Xs) : D.Om × D.Om × (I → Bool) :=
  (q.1.2, D.el q.1.1 • q.1.2, fun v => decide (0 < ((q.2 : X I) v).1.im))

theorem sign_pos {x y : ℝ} (hx : x ≠ 0) (hy : y ≠ 0) (h : decide (0 < x) = decide (0 < y)) : 0 < x * y := by
  rcases lt_or_gt_of_ne hx with hx' | hx' <;> rcases lt_or_gt_of_ne hy with hy' | hy'
  · exact mul_pos_of_neg_of_neg hx' hy'
  · simp [not_lt.mpr hx'.le, hy'] at h
  · simp [hx', not_lt.mpr hy'.le] at h
  · exact mul_pos hx' hy'

theorem fiber_fin (hB : B1b) (hC : B1c) (hE : E0d) (hM : Mult) (hD : D.Ax) (C c Cm : ℝ) (hc : 0 < c)
    (Ws : Set D.Om) (a : Gf) (k : D.Om × D.Om × (I → Bool)) :
    (Prod.fst '' {q | Good D C c Cm Ws a q ∧ key D q = k}).Finite := by
  classical
  have : Nontrivial I := hD.two
  rcases Set.eq_empty_or_nonempty {q | Good D C c Cm Ws a q ∧ key D q = k} with h0 | ⟨q0, hq0⟩
  · rw [h0, Set.image_empty]; exact Set.finite_empty
  have hq0' := hq0
  obtain ⟨⟨hfix0, hsg0, -, -, -⟩, hk0⟩ := hq0'
  have hhf : 0 < D.hf ![0, 1] (D.rep q0.1.2) := hD.pos _ e_ne _
  set B : ℝ := max 1 Cm / D.hf ![0, 1] (D.rep q0.1.2) with hBdef
  set U : ℝ := C * max 1 B with hUdef
  have hbox : ∀ q ∈ {q | Good D C c Cm Ws a q ∧ key D q = k}, q.1.2 = q0.1.2 ∧
      D.el q.1.1 • q.1.2 = D.el q0.1.1 • q0.1.2 ∧
      ∀ v, (|((q.2 : X I) v).1.re| ≤ C ∧ c ≤ |((q.2 : X I) v).1.im| ∧ |((q.2 : X I) v).1.im| ≤ U) ∧
        0 < ((q0.2 : X I) v).1.im * ((q.2 : X I) v).1.im := by
    rintro q ⟨⟨-, hsg, -, hht, -⟩, hk⟩
    have hkk := hk.trans hk0.symm
    simp only [key, Prod.mk.injEq] at hkk
    obtain ⟨e1, e2, e3⟩ := hkk
    refine ⟨e1, e2, fun v => ⟨⟨(hsg v).1, (hsg v).2.1, ?_⟩, ?_⟩⟩
    · have hP : (∏ u, |((q.2 : X I) u).1.im|) ≤ B := by
        rw [htY_e D, e1] at hht
        have hle : (∏ u, |((q.2 : X I) u).1.im|) * D.hf ![0, 1] (D.rep q0.1.2) ≤ max 1 Cm := by
          by_cases h1 : (∏ u, |((q.2 : X I) u).1.im|) * D.hf ![0, 1] (D.rep q0.1.2) ≤ 1
          · exact le_max_of_le_left h1
          · push Not at h1
            exact le_max_of_le_right (by nlinarith)
        rw [hBdef]
        exact (le_div_iff₀ hhf).mpr hle
      exact bound_im hc _ hsg B hP v
    · have := congrFun e3 v
      exact sign_pos ((q0.2 : X I) v).2 ((q.2 : X I) v).2 this.symm
  obtain ⟨v0⟩ : Nonempty I := inferInstance
  have hU : 0 < U := by
    have := ((hbox q0 hq0).2.2 v0).1
    linarith [this.2.1, this.2.2]
  set δ0 : ℝ := c ^ 2 / (C ^ 2 + U ^ 2) with hδ0def
  have hδ0 : 0 < δ0 := by positivity
  obtain ⟨C', hC'⟩ := hD.count q0.1.2 (δ0 ^ 2 / 4) C c (by positivity) hc
  have hfin := (hC' q0.2 hsg0).1
  refine (hfin.image (fun g : PG F => ((D.el q0.1.1 * g : PG F), q0.1.2) : PG F → D.Cj × D.Om)).subset ?_
  rintro _ ⟨q, hq, rfl⟩
  obtain ⟨e1, e2, hv⟩ := hbox q hq
  obtain ⟨⟨hfix, -, -, -, -⟩, -⟩ := hq
  refine ⟨(D.el q0.1.1)⁻¹ * D.el q.1.1, ⟨?_, ?_⟩, ?_⟩
  · have e2' : D.el q.1.1 • q0.1.2 = D.el q0.1.1 • q0.1.2 := by
      calc D.el q.1.1 • q0.1.2 = D.el q.1.1 • q.1.2 := by rw [e1]
        _ = _ := e2
    rw [mul_smul, e2', inv_smul_smul]
  · exact near_of D hB hC (D.el q0.1.1) (D.el q.1.1) q0.2 q.2 hfix0 hfix δ0 hδ0.le
      (fun v => kap_lb C c U hc _ _ ((hbox q0 hq0).2.2 v).1 (hv v).1 (hv v).2)
  · show ((D.el q0.1.1 * ((D.el q0.1.1)⁻¹ * D.el q.1.1) : PG F), q0.1.2) = q.1
    rw [mul_inv_cancel_left, ← e1]
    rfl

end UpperTheory.Esk.ImaginaryPartBound

namespace UpperTheory.Esk.ImaginaryPartBound

open UpperTheory.Esk

variable {F I Gf : Type} [Field F] [Group Gf] [Fintype I] (D : Dat F I Gf)

theorem good_fin (hB : B1b) (hC : B1c) (hE : E0d) (hM : Mult) (hD : D.Ax) (C c Cm : ℝ) (hc : 0 < c)
    (S0 : Finset Gf) (a : Gf) : (Prod.fst '' {q | Good D C c Cm (W D S0) a q}).Finite := by
  classical
  have hW : (W D S0).Finite := S0.finite_toSet.image _
  have hTf : ∀ ω, (T D a ω).Finite := by
    intro ω
    refine ((hD.dbl a).image (fun x : Gf ⧸ D.H => (D.rep ω : Gf) • x)).subset ?_
    rintro _ ⟨h, hh, rfl⟩
    refine ⟨((h * a : Gf) : Gf ⧸ D.H), ⟨h, hh, rfl⟩, ?_⟩
    show (D.rep ω : Gf) • ((h * a : Gf) : Gf ⧸ D.H) = ((D.rep ω * h * a : Gf) : Gf ⧸ D.H)
    rw [mul_assoc]
    rfl
  have hK : ((W D S0) ×ˢ ((⋃ ω ∈ W D S0, T D a ω) ×ˢ (Set.univ : Set (I → Bool)))).Finite :=
    hW.prod ((hW.biUnion fun ω _ => hTf ω).prod Set.finite_univ)
  refine (hK.biUnion fun k _ => fiber_fin D hB hC hE hM hD C c Cm hc (W D S0) a k).subset ?_
  rintro _ ⟨q, hq, rfl⟩
  exact Set.mem_biUnion (x := key D q)
    ⟨hq.2.2.1, Set.mem_biUnion hq.2.2.1 hq.2.2.2.2, Set.mem_univ _⟩ ⟨q, ⟨hq, rfl⟩, rfl⟩

theorem move (hE : E0d) (hD : D.Ax) (a : Gf) (c0 : ℝ) (hmink : ∀ z x, ∃ s, s ≠ 0 ∧ c0 ≤ D.Ht s z x)
    (S0 : Finset Gf) (C c : ℝ)
    (hnorm : ∀ z x, c0 ≤ D.Ht ![0, 1] z x → ∃ b : GL (Fin 2) F, b 1 0 = 0 ∧
      (∃ x' ∈ S0, ∃ h ∈ D.H, D.j b * x = x' * h) ∧ Sg C c (D.act b z))
    (Cm : ℝ) (hCm : ∀ s, s ≠ 0 → ∀ x, D.hf s (x * a⁻¹) ≤ Cm * D.hf s x)
    (γ : PG F) (ω : D.Om) (hell : D.TotEll γ.out) (hs : γ • ω = (show D.Om from ((D.rep ω * a : Gf) : Gf ⧸ D.H))) :
    ∃ δ : PG F, δ • ((γ, ω) : D.Cj × D.Om) ∈ Prod.fst '' {q | Good D C c Cm (W D S0) a q} := by
  classical
  obtain ⟨-, h2, -, -, -, -, -, -, -, h10, -⟩ := hE F I Gf D hD
  obtain ⟨z, hz⟩ := fixX D γ hell
  obtain ⟨s, hs0, hsz⟩ := hmink z (D.rep ω)
  obtain ⟨g, hg⟩ := h10 s hs0
  have he : (![0, 1] : Fin 2 → F) ≠ 0 := e_ne
  have hmov : c0 ≤ D.HtY ![0, 1] ((g : PG F) • ((ω, z) : D.Y)) := by
    rw [h2 _ he g, hg]
    exact hsz
  have hmov' : c0 ≤ D.Ht ![0, 1] ((g : PG F) • z : D.Xs) (D.rep ((g : PG F) • ω)) := hmov
  obtain ⟨b, -, ⟨x', hx', h, hh, hbx⟩, hsg⟩ := hnorm _ _ hmov'
  have hmul : (((b * g : GL (Fin 2) F)) : PG F) = (b : PG F) * (g : PG F) := rfl
  have hδz : (((b * g : GL (Fin 2) F)) : PG F) • z = D.act b ((g : PG F) • z : D.Xs) := by
    rw [hmul, mul_smul, Dat.mk_smulX]
  have hδω : (((b * g : GL (Fin 2) F)) : PG F) • ω = ((x' : Gf) : Gf ⧸ D.H) := by
    rw [hmul, mul_smul]
    have e1 : (g : PG F) • ω = ((D.rep ((g : PG F) • ω) : Gf) : Gf ⧸ D.H) := (rep_spec D _).symm
    have e2 := Dat.mk_smulO D b (D.rep ((g : PG F) • ω))
    try simp only at e2
    rw [e1, e2, hbx]
    refine QuotientGroup.eq.mpr ?_
    rw [_root_.mul_inv_rev, mul_assoc, inv_mul_cancel, mul_one]
    exact inv_mem hh
  have hfixδ : ((((b * g : GL (Fin 2) F)) : PG F) * γ * (((b * g : GL (Fin 2) F)) : PG F)⁻¹) •
      ((((b * g : GL (Fin 2) F)) : PG F) • z) = (((b * g : GL (Fin 2) F)) : PG F) • z := by
    rw [mul_smul, mul_smul, inv_smul_smul, hz]
  have h10' := conj_10 D hE hD γ hell (b * g)
  have hT := Tmem D a (b * g) γ ω hs
  have hht := htBound D hE hD a Cm hCm _ _ _ hfixδ h10' hT
  refine ⟨(((b * g : GL (Fin 2) F)) : PG F),
    ((((b * g : GL (Fin 2) F)) : PG F) • ((γ, ω) : D.Cj × D.Om), (((b * g : GL (Fin 2) F)) : PG F) • z), ?_, rfl⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact hfixδ
  · show Sg C c ((((b * g : GL (Fin 2) F)) : PG F) • z : D.Xs)
    rw [hδz]
    exact hsg
  · show (((b * g : GL (Fin 2) F)) : PG F) • ω ∈ W D S0
    rw [hδω]
    exact ⟨x', hx', rfl⟩
  · exact hht
  · exact hT

end UpperTheory.Esk.ImaginaryPartBound

theorem UpperTheory.Esk.imaginary_part_bound_proof : UpperTheory.Esk.B1b → UpperTheory.Esk.B1c → UpperTheory.Esk.E0d → UpperTheory.Esk.Mult → UpperTheory.Esk.F4 := by
  intro hB hC hE hM F I Gf _ _ _ D hD a
  obtain ⟨c0, hc0, hmink⟩ := hD.mink
  obtain ⟨S0, C, c, hc, hnorm⟩ := hD.normal c0 hc0
  obtain ⟨Cm, hCm⟩ := hD.mul a⁻¹
  refine ⟨Prod.fst '' {q | UpperTheory.Esk.ImaginaryPartBound.Good D C c Cm (UpperTheory.Esk.ImaginaryPartBound.W D S0) a q},
    UpperTheory.Esk.ImaginaryPartBound.good_fin D hB hC hE hM hD C c Cm hc S0 a, ?_⟩
  intro γ ω hell hs
  exact UpperTheory.Esk.ImaginaryPartBound.move D hE hD a c0 hmink S0 C c hnorm Cm hCm γ ω hell hs
