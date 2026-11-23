import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.MultivariableReproducingFormula

noncomputable section

open MeasureTheory Matrix
open scoped ENNReal NNReal ComplexConjugate

namespace UpperTheory.Esk.EllipticTermsContribution

open UpperTheory.Esk

theorem mk_out {F : Type} [Field F] (q : PG F) : ((q.out : GL (Fin 2) F) : PG F) = q := Quotient.out_eq' q

theorem elliptic_lower_left_ne_zero (h : GL (Fin 2) ℝ) (hh : h.val.trace ^ 2 < 4 * h.val.det) : h 1 0 ≠ 0 := by
  intro e
  rw [Matrix.trace_fin_two, det_eq, e] at hh
  nlinarith [sq_nonneg (h 0 0 - h 1 1)]

def disc (h : GL (Fin 2) ℝ) : ℝ := 4 * h.val.det - h.val.trace ^ 2

def fpC (h : GL (Fin 2) ℝ) : ℂ :=
  (((h 0 0 - h 1 1) / (2 * h 1 0) : ℝ) : ℂ) + Complex.I * ((Real.sqrt (disc h) / (2 * h 1 0) : ℝ) : ℂ)

theorem fpC_im (h : GL (Fin 2) ℝ) (hh : h.val.trace ^ 2 < 4 * h.val.det) : (fpC h).im ≠ 0 := by
  have hr := elliptic_lower_left_ne_zero h hh
  have hd : 0 < disc h := by unfold disc; linarith
  simp only [fpC, Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re, Complex.I_im,
    Complex.ofReal_re, zero_mul, one_mul, zero_add]
  exact div_ne_zero (Real.sqrt_pos.2 hd).ne' (mul_ne_zero two_ne_zero hr)

def fp (h : GL (Fin 2) ℝ) (hh : h.val.trace ^ 2 < 4 * h.val.det) : P := ⟨fpC h, fpC_im h hh⟩

theorem fp_eq (h : GL (Fin 2) ℝ) (hh : h.val.trace ^ 2 < 4 * h.val.det) :
    ((h 1 0 : ℝ) : ℂ) * fpC h ^ 2 + (((h 1 1 : ℝ) : ℂ) - ((h 0 0 : ℝ) : ℂ)) * fpC h - ((h 0 1 : ℝ) : ℂ) = 0 := by
  have hr := elliptic_lower_left_ne_zero h hh
  have hd : 0 < disc h := by unfold disc; linarith
  have hr' : ((h 1 0 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hr
  have hs : ((Real.sqrt (disc h) : ℝ) : ℂ) ^ 2 = ((disc h : ℝ) : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt hd.le]
  have hD : ((disc h : ℝ) : ℂ) = 4 * (((h 0 0 : ℝ) : ℂ) * ((h 1 1 : ℝ) : ℂ) - ((h 0 1 : ℝ) : ℂ) * ((h 1 0 : ℝ) : ℂ))
      - (((h 0 0 : ℝ) : ℂ) + ((h 1 1 : ℝ) : ℂ)) ^ 2 := by
    simp only [disc, Matrix.trace_fin_two, det_eq]; push_cast; ring
  have hz : 2 * ((h 1 0 : ℝ) : ℂ) * fpC h = (((h 0 0 : ℝ) : ℂ) - ((h 1 1 : ℝ) : ℂ)) + Complex.I * ((Real.sqrt (disc h) : ℝ) : ℂ) := by
    simp only [fpC]; push_cast; field_simp
  have h4 : (4 * ((h 1 0 : ℝ) : ℂ)) * (((h 1 0 : ℝ) : ℂ) * fpC h ^ 2 + (((h 1 1 : ℝ) : ℂ) - ((h 0 0 : ℝ) : ℂ)) * fpC h - ((h 0 1 : ℝ) : ℂ)) = 0 := by
    rw [show (4 * ((h 1 0 : ℝ) : ℂ)) * (((h 1 0 : ℝ) : ℂ) * fpC h ^ 2 + (((h 1 1 : ℝ) : ℂ) - ((h 0 0 : ℝ) : ℂ)) * fpC h - ((h 0 1 : ℝ) : ℂ))
      = (2 * ((h 1 0 : ℝ) : ℂ) * fpC h) ^ 2 + 2 * (((h 1 1 : ℝ) : ℂ) - ((h 0 0 : ℝ) : ℂ)) * (2 * ((h 1 0 : ℝ) : ℂ) * fpC h)
        - 4 * ((h 1 0 : ℝ) : ℂ) * ((h 0 1 : ℝ) : ℂ) by ring, hz]
    linear_combination ((Real.sqrt (disc h) : ℝ) : ℂ) ^ 2 * Complex.I_sq - hs - hD
  rcases mul_eq_zero.1 h4 with h5 | h5
  · exact absurd h5 (mul_ne_zero (by norm_num : (4 : ℂ) ≠ 0) hr')
  · exact h5

theorem fix_comm (h g : GL (Fin 2) ℝ) (hh : h.val.trace ^ 2 < 4 * h.val.det) (hc : g * h = h * g) :
    g • fp h hh = fp h hh := by
  have hr := elliptic_lower_left_ne_zero h hh
  have hr' : ((h 1 0 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hr
  have e00 := congrArg (fun M : GL (Fin 2) ℝ => M 0 0) hc
  have e10 := congrArg (fun M : GL (Fin 2) ℝ => M 1 0) hc
  simp only [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two] at e00 e10
  have e00' : ((g 0 0 : ℝ) : ℂ) * ((h 0 0 : ℝ) : ℂ) + ((g 0 1 : ℝ) : ℂ) * ((h 1 0 : ℝ) : ℂ)
      = ((h 0 0 : ℝ) : ℂ) * ((g 0 0 : ℝ) : ℂ) + ((h 0 1 : ℝ) : ℂ) * ((g 1 0 : ℝ) : ℂ) := by exact_mod_cast e00
  have e10' : ((g 1 0 : ℝ) : ℂ) * ((h 0 0 : ℝ) : ℂ) + ((g 1 1 : ℝ) : ℂ) * ((h 1 0 : ℝ) : ℂ)
      = ((h 1 0 : ℝ) : ℂ) * ((g 0 0 : ℝ) : ℂ) + ((h 1 1 : ℝ) : ℂ) * ((g 1 0 : ℝ) : ℂ) := by exact_mod_cast e10
  have hQ := fp_eq h hh
  apply Subtype.ext
  rw [coe_smul, div_eq_iff (den_ne g (fp h hh).2)]
  apply mul_left_cancel₀ hr'
  change ((h 1 0 : ℝ) : ℂ) * (((g 0 0 : ℝ) : ℂ) * fpC h + ((g 0 1 : ℝ) : ℂ))
    = ((h 1 0 : ℝ) : ℂ) * (fpC h * (((g 1 0 : ℝ) : ℂ) * fpC h + ((g 1 1 : ℝ) : ℂ)))
  linear_combination e00' - fpC h * e10' - ((g 1 0 : ℝ) : ℂ) * hQ

theorem tr_r {F I Gf : Type} [Field F] [Group Gf] (D : Dat F I Gf) (v : I) (g : GL (Fin 2) F) :
    (D.r v g).val.trace = D.σ v g.val.trace := by
  rw [Matrix.trace_fin_two, Matrix.trace_fin_two, map_add]; rfl

theorem det_r {F I Gf : Type} [Field F] [Group Gf] (D : Dat F I Gf) (v : I) (g : GL (Fin 2) F) :
    (D.r v g).val.det = D.σ v g.val.det := by
  rw [Matrix.det_fin_two, Matrix.det_fin_two, map_sub, map_mul, map_mul]; rfl

end UpperTheory.Esk.EllipticTermsContribution

open UpperTheory.Esk.EllipticTermsContribution in
theorem UpperTheory.Esk.elliptic_terms_contribution_proof : UpperTheory.Esk.B1a → UpperTheory.Esk.B1b → UpperTheory.Esk.B1c → UpperTheory.Esk.B4 → UpperTheory.Esk.C1 → UpperTheory.Esk.E0a → UpperTheory.Esk.KernelTermsInvariantBounded → UpperTheory.Esk.E0d → UpperTheory.Esk.Mult → UpperTheory.Esk.Fcen → UpperTheory.Esk.F3 := by
  intro hB1a _ hB1c hB4 hC1 hE0a hE0c _ hMult hFcen F I Gf ι _ _ _ _ D k a hyp γ ω hT hTe
  have : SigmaFinite (volume : Measure P) := hB1a.1
  obtain ⟨_, c2, c3, _, c5, c6⟩ := hE0c F I Gf ι D k a hyp
  have htr : γ.out.val.trace ≠ 0 := by
    obtain ⟨i, hi⟩ := c5 γ ω hTe
    exact (c6 γ ω i hi).1
  have hTv : ∀ v, (D.r v γ.out).val.trace ^ 2 < 4 * (D.r v γ.out).val.det := fun v => by
    rw [tr_r, det_r]; exact hT v
  let z0 : D.Xs := fun v => fp (D.r v γ.out) (hTv v)
  set S := MulAction.stabilizer (PG F) ((γ, ω) : D.Cj × D.Om) with hS
  have memS : ∀ g : PG F, g ∈ S → g * γ * g⁻¹ = γ ∧ g • ω = ω := by
    intro g hg
    rw [hS, MulAction.mem_stabilizer_iff] at hg
    exact ⟨congrArg Prod.fst hg, congrArg Prod.snd hg⟩
  have fixS : ∀ g : PG F, g ∈ S → g • z0 = z0 := by
    intro g hg
    obtain ⟨h1, -⟩ := memS g hg
    have hc : g.out * γ.out = γ.out * g.out := by
      apply hFcen F γ.out g.out htr
      rw [mk_out, mk_out]; exact h1
    rw [← mk_out g, Dat.mk_smulX]
    funext v
    exact fix_comm _ _ (hTv v) (by rw [← map_mul, ← map_mul, hc])
  obtain ⟨c₀, hc₀, hmink⟩ := hyp.ax.mink
  obtain ⟨s, hs, hsc⟩ := hmink z0 (D.rep ω)
  obtain ⟨C, hC⟩ := hMult F I Gf D hyp.ax 1 c₀ one_pos hc₀
  have hfin := (hC (ω, z0) s hs hsc).1
  have hSfin : (S : Set (PG F)).Finite := hfin.subset fun g hg => ⟨(memS g hg).2, fun v => by
      show 1 ≤ kap (z0 v) ((g • z0 : D.Xs) v)
      rw [fixS g hg, hB1c.2.1]⟩
  have hSF : Finite S := hSfin.to_subtype
  refine ⟨hSF, fun β hβ => ?_⟩
  let f : I → P → ℂ := fun v w => q1 (k v) w (D.r v γ.out • w) * j1 (k v) (D.r v γ.out) w
  have hu : ∀ z : D.Xs, D.kk k a γ (ω, z) = D.Te a γ.out (D.rep ω) * ∏ v, f v (z v) := by
    intro z
    show D.Te a γ.out (D.rep ω) * (qq k z (D.act γ.out z) * D.J k γ.out z) =
      D.Te a γ.out (D.rep ω) * ∏ v, (q1 (k v) (z v) (D.r v γ.out • z v) * j1 (k v) (D.r v γ.out) (z v))
    rw [Finset.prod_mul_distrib]; rfl
  have hint : Integrable (fun z : D.Xs => ∏ v, f v (z v)) :=
    Integrable.fintype_prod (f := f) (μ := fun _ => volume) fun v => (hB4 (k v) (hyp.four v) _ (hTv v)).1
  have hval : ∫ z : D.Xs, ∏ v, f v (z v) = D.orb k γ.out := by
    rw [show (∫ z : D.Xs, ∏ v, f v (z v)) = ∫ z : I → P, ∏ v, f v (z v) ∂(Measure.pi fun _ => volume) from rfl,
      integral_fintype_prod_eq_prod]
    unfold Dat.orb
    refine Finset.prod_congr rfl fun v _ => ?_
    rw [(hB4 (k v) (hyp.four v) _ (hTv v)).2, tr_r, det_r]
  haveI : Fintype S := Fintype.ofFinite S
  have hcard : (0 : ℝ) < Fintype.card S := by exact_mod_cast Fintype.card_pos_iff.2 ⟨1⟩
  let c : ℝ := (Fintype.card S : ℝ)⁻¹
  have hcut : IsCut S (fun _ : D.Xs => c) := ⟨measurable_const, fun _ => inv_nonneg.2 hcard.le, fun _ => by
      have e : ∑ _ : S, c = 1 := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_inv_cancel₀ hcard.ne']
      rw [← e]; exact hasSum_fintype _⟩
  have hP : Pres S (volume : Measure D.Xs) := fun g => (hE0a F I Gf D hyp.ax).2.2.1 (g : PG F)
  have hinv : ∀ (g : S) (z : D.Xs), D.kk k a γ (ω, g • z) = D.kk k a γ (ω, z) := by
    intro g z
    obtain ⟨h1, h2⟩ := memS g g.2
    have := c2 g γ (ω, z)
    have e : (g : PG F) • ((ω, z) : D.Y) = (ω, g • z) := Prod.ext h2 rfl
    rw [h1, e] at this
    exact this
  have hmeas : Measurable (fun z : D.Xs => D.kk k a γ (ω, z)) := (c3 γ).comp measurable_prodMk_left
  have hintc : Integrable (fun z : D.Xs => c • D.kk k a γ (ω, z)) := by
    rw [show (fun z : D.Xs => c • D.kk k a γ (ω, z)) = fun z => c • (D.Te a γ.out (D.rep ω) * ∏ v, f v (z v)) from
      funext fun z => by rw [hu]]
    exact (hint.const_mul _).smul c
  obtain ⟨-, heq⟩ := (hC1 (↥S) D.Xs volume hP (fun _ => c) β hcut hβ).2 _ hmeas hinv hintc
  rw [← heq]
  simp_rw [hu]
  rw [integral_smul, integral_const_mul, hval, Nat.card_eq_fintype_card, Complex.real_smul]
  simp only [c, Complex.ofReal_inv, Complex.ofReal_natCast]
