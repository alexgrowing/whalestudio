import Formalism.HermitianCurvature.StatementM

open Formalism.FourierDecayAlt.M Formalism.FourierDecayAlt Finset

namespace Formalism.FourierDecayAlt.P.Mx2

theorem eulerLeibniz : EulerLeibniz := by
  intro r v f g
  ext γ
  have hf : (euler v f).support ⊆ f.support := by
    intro γ h
    simp only [euler, LinearMap.coe_mk, AddHom.coe_mk, HahnSeries.mem_support, ne_eq, mul_eq_zero, not_or] at h
    exact h.2
  have hg : (euler v g).support ⊆ g.support := by
    intro γ h
    simp only [euler, LinearMap.coe_mk, AddHom.coe_mk, HahnSeries.mem_support, ne_eq, mul_eq_zero, not_or] at h
    exact h.2
  rw [HahnSeries.coeff_add, HahnSeries.coeff_mul_left' f.isPWO_support hf,
    HahnSeries.coeff_mul_right' g.isPWO_support hg, ← Finset.sum_add_distrib]
  show ((ofLex γ v : ℤ) : ℂ) * (f * g).coeff γ = _
  rw [HahnSeries.coeff_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  rintro ⟨a, b⟩ h
  have hab : a + b = γ := (Finset.mem_addAntidiagonal.1 h).2.2
  subst hab
  show _ = (((ofLex a v : ℤ) : ℂ) * f.coeff a) * g.coeff b + f.coeff a * (((ofLex b v : ℤ) : ℂ) * g.coeff b)
  have : ((ofLex (a + b) v : ℤ) : ℂ) = ((ofLex a v : ℤ) : ℂ) + ((ofLex b v : ℤ) : ℂ) := by
    have h2 : ofLex (a + b) v = ofLex a v + ofLex b v := rfl
    rw [h2]; push_cast; ring
  rw [this]; ring

theorem eulerCoord : EulerCoord := by
  intro r v w z
  constructor
  · ext γ
    simp only [euler, coord, LinearMap.coe_mk, AddHom.coe_mk]
    by_cases h : γ = toLex (Pi.single w (1 : ℤ))
    · subst h
      by_cases hv : v = w
      · subst hv; simp
      · simp [hv, Pi.single_apply]
    · split_ifs <;> simp [HahnSeries.coeff_single_of_ne h]
  · ext γ
    simp only [euler, LinearMap.coe_mk, AddHom.coe_mk, HahnSeries.algebraMap_apply]
    by_cases h : γ = 0
    · subst h; simp; left; rfl
    · simp [HahnSeries.coeff_single_of_ne h]

theorem eulerMul : EulerMul := by
  intro r v f
  ext g : 1
  simp only [Module.End.mul_apply, LinearMap.add_apply, mulOp, LinearMap.mulLeft_apply]
  rw [eulerLeibniz, add_comm]

theorem coord_ne (r : ℕ) (v : Var r) : coord v ≠ 0 := by
  simp [coord]

variable {r : ℕ}

theorem mulOp_mul (f g : Fn r) : mulOp f * mulOp g = mulOp (f * g) := by
  ext h : 1; simp [mulOp, mul_assoc]
theorem mulOp_add (f g : Fn r) : mulOp f + mulOp g = mulOp (f + g) := by
  ext h : 1; simp [mulOp, add_mul]

theorem multiplierPair_mul (f fb g gb : Fn r) : fnP f fb * fnP g gb = fnP (f * g) (fb * gb) := by
  refine Prod.ext ?_ ?_
  · exact mulOp_mul f g
  · show MulOpposite.op (mulOp gb * mulOp fb) = MulOpposite.op (mulOp (fb * gb))
    rw [mulOp_mul, mul_comm]
theorem multiplierPair_add (f fb g gb : Fn r) : fnP f fb + fnP g gb = fnP (f + g) (fb + gb) := by
  refine Prod.ext ?_ ?_
  · exact mulOp_add f g
  · show MulOpposite.op (mulOp fb + mulOp gb) = MulOpposite.op (mulOp (fb + gb))
    rw [mulOp_add]
theorem multiplierPair_one : (fnP 1 1 : Pr r) = 1 := by
  have : mulOp (1 : Fn r) = 1 := by ext h : 1; simp [mulOp]
  refine Prod.ext ?_ ?_
  · exact this
  · show MulOpposite.op (mulOp (1 : Fn r)) = 1
    rw [this]; rfl
theorem multiplierPair_neg (f fb : Fn r) : -fnP f fb = fnP (-f) (-fb) := by
  rw [neg_eq_iff_add_eq_zero, multiplierPair_add]; simp
  refine Prod.ext ?_ ?_
  · show mulOp (0 : Fn r) = 0
    ext h : 1; simp [mulOp]
  · show MulOpposite.op (mulOp (0 : Fn r)) = 0
    have : mulOp (0 : Fn r) = 0 := by ext h : 1; simp [mulOp]
    rw [this]; rfl
theorem multiplierPair_comm (f fb g gb : Fn r) : fnP f fb * fnP g gb = fnP g gb * fnP f fb := by
  rw [multiplierPair_mul, multiplierPair_mul, mul_comm f, mul_comm fb]

theorem der_fn (a b : Fn r) (v w : Var r) (f fb : Fn r) :
    mk (mulOp a * euler v) (-(mulOp b * euler w)) * fnP f fb =
      fnP f fb * mk (mulOp a * euler v) (-(mulOp b * euler w)) + fnP (a * euler v f) (b * euler w fb) := by
  refine Prod.ext ?_ ?_
  · show mulOp a * euler v * mulOp f = mulOp f * (mulOp a * euler v) + mulOp (a * euler v f)
    rw [mul_assoc, eulerMul, mul_add, ← mul_assoc, ← mul_assoc, mulOp_mul, mulOp_mul, mulOp_mul, mul_comm a f]
  · show MulOpposite.op (mulOp fb * -(mulOp b * euler w)) =
      MulOpposite.op (-(mulOp b * euler w) * mulOp fb + mulOp (b * euler w fb))
    congr 1
    rw [neg_mul, mul_assoc, eulerMul, mul_add, ← mul_assoc, mulOp_mul, mulOp_mul, mul_neg, ← mul_assoc, mulOp_mul,
      mul_comm b fb]
    abel

theorem euler_one (v : Var r) : euler v (1 : Fn r) = 0 := by
  have := (eulerCoord r v v 1).2
  simpa using this

theorem euler_inv (v : Var r) (f : Fn r) (hf : f ≠ 0) : euler v f⁻¹ = -(f⁻¹ * f⁻¹ * euler v f) := by
  have h := eulerLeibniz r v f f⁻¹
  rw [mul_inv_cancel₀ hf, euler_one] at h
  have h2 : f * euler v f⁻¹ = -(euler v f * f⁻¹) := by
    rw [eq_neg_iff_add_eq_zero, add_comm]; exact h.symm
  have h3 : euler v f⁻¹ = f⁻¹ * (f * euler v f⁻¹) := by rw [← mul_assoc, inv_mul_cancel₀ hf, one_mul]
  rw [h3, h2]; ring

theorem vz_ne : (vz : Var r) ≠ vzb := by
  intro h; have := congrArg (fun p : Var r => (ofLex p).2) h; simp [vz, vzb] at this

theorem euler_GG_z (TT : ℝ) : euler vz (gg TT : Fn r) = coord vz * coord vzb := by
  unfold gg
  rw [map_sub, eulerLeibniz, (eulerCoord r vz vz 0).1, (eulerCoord r vz vzb 0).1, (eulerCoord r vz vz _).2,
    if_pos rfl, if_neg vz_ne]; simp
theorem euler_gg_zb (TT : ℝ) : euler vzb (gg TT : Fn r) = coord vz * coord vzb := by
  unfold gg
  rw [map_sub, eulerLeibniz, (eulerCoord r vzb vz 0).1, (eulerCoord r vzb vzb 0).1, (eulerCoord r vzb vz _).2,
    if_pos rfl, if_neg vz_ne.symm]; simp

theorem gg_ne (TT : ℝ) : (gg TT : Fn r) ≠ 0 := by
  intro h
  have h1 := euler_GG_z (r := r) TT
  rw [h, map_zero] at h1
  exact mul_ne_zero (coord_ne r vz) (coord_ne r vzb) h1.symm

theorem smul_fnP (a : ℝ) (f fb : Fn r) : (a : ℂ) • fnP f fb = fnP ((a : ℂ) • f) ((a : ℂ) • fb) := by
  rw [Algebra.smul_def]
  refine Prod.ext ?_ ?_
  · show algebraMap ℂ (Op r) a * mulOp f = mulOp ((a : ℂ) • f)
    ext h : 1; simp [mulOp]
  · show (algebraMap ℂ (Op r)ᵐᵒᵖ) (starRingEnd ℂ (a : ℂ)) * MulOpposite.op (mulOp fb) = MulOpposite.op (mulOp ((a : ℂ) • fb))
    rw [Complex.conj_ofReal, ← Algebra.smul_def, ← MulOpposite.op_smul]
    congr 1
    ext h : 1; simp [mulOp]

noncomputable def nabE (a TT : ℝ) : Pr r := dzP + (a : ℂ) • (zbP * ggiP TT)
noncomputable def nabsE (a TT : ℝ) : Pr r := -dzbP + (a : ℂ) • (zP * ggiP TT)

theorem nabE_fn (a TT : ℝ) (f fb : Fn r) :
    nabE a TT * fnP f fb = fnP f fb * nabE a TT + fnP ((coord vz)⁻¹ * euler vz f) ((coord vzb)⁻¹ * euler vzb fb) := by
  unfold nabE
  rw [zbP, ggiP, multiplierPair_mul, smul_fnP, add_mul, mul_add, multiplierPair_comm, dzP, der_fn]
  abel

theorem nabsE_fn (a TT : ℝ) (f fb : Fn r) :
    nabsE a TT * fnP f fb = fnP f fb * nabsE a TT - fnP ((coord vzb)⁻¹ * euler vzb f) ((coord vz)⁻¹ * euler vz fb) := by
  unfold nabsE
  rw [zP, ggiP, multiplierPair_mul, smul_fnP, add_mul, mul_add, multiplierPair_comm, dzbP, neg_mul, der_fn, mul_neg]
  abel

theorem nabla_zeta_comm (a TT : ℝ) : nabE a TT * (zP : Pr r) = zP * nabE a TT + 1 := by
  rw [zP, nabE_fn, (eulerCoord r vz vz 0).1, (eulerCoord r vzb vzb 0).1, if_pos rfl, if_pos rfl,
    inv_mul_cancel₀ (coord_ne r _), inv_mul_cancel₀ (coord_ne r _), multiplierPair_one]
theorem nab_zi (a TT : ℝ) : nabE a TT * (ziP : Pr r) = ziP * nabE a TT - ziP * ziP := by
  rw [ziP, nabE_fn, euler_inv _ _ (coord_ne r _), euler_inv _ _ (coord_ne r _), (eulerCoord r vz vz 0).1,
    (eulerCoord r vzb vzb 0).1, if_pos rfl, if_pos rfl, multiplierPair_mul, sub_eq_add_neg, multiplierPair_neg]
  congr 2
  · field_simp [coord_ne r vz]
  · field_simp [coord_ne r vzb]
theorem nab_zb (a TT : ℝ) : nabE a TT * (zbP : Pr r) = zbP * nabE a TT := by
  rw [zbP, nabE_fn, (eulerCoord r vz vzb 0).1, (eulerCoord r vzb vz 0).1, if_neg vz_ne, if_neg vz_ne.symm]
  simp only [mul_zero]
  have h0 : mulOp (0 : Fn r) = 0 := by ext h : 1; simp [mulOp]
  have : (fnP 0 0 : Pr r) = 0 := by
    refine Prod.ext h0 ?_
    show MulOpposite.op (mulOp (0 : Fn r)) = 0
    rw [h0]; rfl
  rw [this, add_zero]
theorem nab_gg (a TT : ℝ) : nabE a TT * (ggP TT : Pr r) = ggP TT * nabE a TT + zbP := by
  rw [ggP, nabE_fn, euler_GG_z, euler_gg_zb, zbP]
  congr 2
  · field_simp [coord_ne r vz]
  · field_simp [coord_ne r vzb]
theorem nab_ggi (a TT : ℝ) : nabE a TT * (ggiP TT : Pr r) = ggiP TT * nabE a TT - zbP * ggiP TT * ggiP TT := by
  rw [ggiP, nabE_fn, euler_inv _ _ (gg_ne TT), euler_inv _ _ (gg_ne TT), euler_GG_z, euler_gg_zb, zbP, multiplierPair_mul, multiplierPair_mul,
    sub_eq_add_neg, multiplierPair_neg]
  congr 2
  · field_simp [coord_ne r vz]
  · field_simp [coord_ne r vzb]
theorem nabs_zb (a TT : ℝ) : nabsE a TT * (zbP : Pr r) = zbP * nabsE a TT - 1 := by
  rw [zbP, nabsE_fn, (eulerCoord r vz vz 0).1, (eulerCoord r vzb vzb 0).1, if_pos rfl, if_pos rfl,
    inv_mul_cancel₀ (coord_ne r _), inv_mul_cancel₀ (coord_ne r _), multiplierPair_one]
theorem nabs_gg (a TT : ℝ) : nabsE a TT * (ggP TT : Pr r) = ggP TT * nabsE a TT - zP := by
  rw [ggP, nabsE_fn, euler_GG_z, euler_gg_zb, zP]
  congr 2
  · field_simp [coord_ne r vzb]
  · field_simp [coord_ne r vz]
theorem nabs_ggi (a TT : ℝ) : nabsE a TT * (ggiP TT : Pr r) = ggiP TT * nabsE a TT + zP * ggiP TT * ggiP TT := by
  rw [ggiP, nabsE_fn, euler_inv _ _ (gg_ne TT), euler_inv _ _ (gg_ne TT), euler_GG_z, euler_gg_zb, zP, multiplierPair_mul, multiplierPair_mul,
    sub_eq_add_neg, multiplierPair_neg]
  congr 2
  · field_simp [coord_ne r vzb]
  · field_simp [coord_ne r vz]

theorem partialDeriv_def (l : Fin r) : (pP l : Pr r) = mk (mulOp 1 * euler (vc l)) (-(mulOp 1 * euler (vcb l))) := by
  have : mulOp (1 : Fn r) = 1 := by ext h : 1; simp [mulOp]
  rw [this, one_mul, one_mul]; rfl
theorem p_c (l : Fin r) : pP l * cP l = cP l * pP l + cP l := by
  rw [partialDeriv_def, cP, der_fn, (eulerCoord r _ _ 0).1, (eulerCoord r _ _ 0).1, if_pos rfl, if_pos rfl, one_mul, one_mul]
theorem p_ci (l : Fin r) : pP l * ciP l = ciP l * pP l - ciP l := by
  rw [partialDeriv_def, ciP, der_fn, euler_inv _ _ (coord_ne r _), euler_inv _ _ (coord_ne r _), (eulerCoord r _ _ 0).1,
    (eulerCoord r _ _ 0).1, if_pos rfl, if_pos rfl, one_mul, one_mul, sub_eq_add_neg, multiplierPair_neg]
  congr 2
  · field_simp [coord_ne r (vc l)]
  · field_simp [coord_ne r (vcb l)]

theorem nabA_eq (P : Par) : nabA P = Matrix.diagonal fun π => nabE (aC P π) P.TT := rfl
theorem nabsA_eq (P : Par) : nabsA P = Matrix.diagonal fun π => nabsE (aC P π) P.TT := rfl

theorem eulerComm : EulerComm := by
  intro r v w
  ext f γ
  simp only [Module.End.mul_apply, euler, LinearMap.coe_mk, AddHom.coe_mk]
  ring

theorem multiplierPair_zero : (fnP 0 0 : Pr r) = 0 := by
  have h0 : mulOp (0 : Fn r) = 0 := by ext h : 1; simp [mulOp]
  refine Prod.ext h0 ?_
  show MulOpposite.op (mulOp (0 : Fn r)) = 0
  rw [h0]; rfl

theorem ec (v w : Var r) : euler v (coord w) = if v = w then coord w else 0 := (eulerCoord r v w 0).1
theorem eci (v w : Var r) : euler v (coord w)⁻¹ = if v = w then -(coord w)⁻¹ else 0 := by
  rw [euler_inv _ _ (coord_ne r w), ec]
  split_ifs
  · field_simp [coord_ne r w]
  · simp

theorem vc_inj (l m : Fin r) : (vc l : Var r) = vc m ↔ l = m := by
  constructor
  · intro h; have := congrArg (fun p : Var r => (ofLex p).1) h; simpa [vc] using this
  · rintro rfl; rfl
theorem vcb_inj (l m : Fin r) : (vcb l : Var r) = vcb m ↔ l = m := by
  constructor
  · intro h; have := congrArg (fun p : Var r => (ofLex p).1) h; simpa [vcb] using this
  · rintro rfl; rfl
theorem vc_vcb (l m : Fin r) : (vc l : Var r) ≠ vcb m := by
  intro h; have := congrArg (fun p : Var r => (ofLex p).2) h; simp [vc, vcb] at this
theorem vc_vz (l : Fin r) : (vc l : Var r) ≠ vz := by
  intro h; have := congrArg (fun p : Var r => (ofLex p).1) h
  exact (Fin.castSucc_lt_last l).ne this
theorem vc_vzb (l : Fin r) : (vc l : Var r) ≠ vzb := by
  intro h; have := congrArg (fun p : Var r => (ofLex p).1) h
  exact (Fin.castSucc_lt_last l).ne this
theorem vcb_vz (l : Fin r) : (vcb l : Var r) ≠ vz := by
  intro h; have := congrArg (fun p : Var r => (ofLex p).1) h
  exact (Fin.castSucc_lt_last l).ne this
theorem vcb_vzb (l : Fin r) : (vcb l : Var r) ≠ vzb := by
  intro h; have := congrArg (fun p : Var r => (ofLex p).1) h
  exact (Fin.castSucc_lt_last l).ne this

theorem euler_gamma_vanish (v : Var r) (h1 : v ≠ vz) (h2 : v ≠ vzb) (TT : ℝ) : euler v (gg TT : Fn r) = 0 := by
  unfold gg
  rw [map_sub, eulerLeibniz, ec, ec, (eulerCoord r v v _).2, if_neg h1, if_neg h2]; simp
theorem euler_gamma_inv_vanish (v : Var r) (h1 : v ≠ vz) (h2 : v ≠ vzb) (TT : ℝ) : euler v (gg TT : Fn r)⁻¹ = 0 := by
  rw [euler_inv _ _ (gg_ne TT), euler_gamma_vanish v h1 h2]; simp

def ZF (f : Fn r) : Prop := ∀ l : Fin r, euler (vc l) f = 0 ∧ euler (vcb l) f = 0

def CF (f : Fn r) : Prop := euler vz f = 0 ∧ euler vzb f = 0

theorem zeta_free_of_variable : ZF (coord vz : Fn r) := fun l => ⟨by rw [ec, if_neg (vc_vz l)], by rw [ec, if_neg (vcb_vz l)]⟩
theorem zf_zb : ZF (coord vzb : Fn r) := fun l => ⟨by rw [ec, if_neg (vc_vzb l)], by rw [ec, if_neg (vcb_vzb l)]⟩
theorem zf_zi : ZF ((coord vz)⁻¹ : Fn r) := fun l => ⟨by rw [eci, if_neg (vc_vz l)], by rw [eci, if_neg (vcb_vz l)]⟩
theorem zf_zbi : ZF ((coord vzb)⁻¹ : Fn r) := fun l => ⟨by rw [eci, if_neg (vc_vzb l)], by rw [eci, if_neg (vcb_vzb l)]⟩
theorem zf_gg (TT : ℝ) : ZF (gg TT : Fn r) := fun l =>
  ⟨euler_gamma_vanish _ (vc_vz l) (vc_vzb l) TT, euler_gamma_vanish _ (vcb_vz l) (vcb_vzb l) TT⟩
theorem zf_ggi (TT : ℝ) : ZF ((gg TT)⁻¹ : Fn r) := fun l =>
  ⟨euler_gamma_inv_vanish _ (vc_vz l) (vc_vzb l) TT, euler_gamma_inv_vanish _ (vcb_vz l) (vcb_vzb l) TT⟩
theorem zf_mul {f g : Fn r} (hf : ZF f) (hg : ZF g) : ZF (f * g) := fun l =>
  ⟨by rw [eulerLeibniz, (hf l).1, (hg l).1]; simp, by rw [eulerLeibniz, (hf l).2, (hg l).2]; simp⟩
theorem zf_smul {f : Fn r} (z : ℂ) (hf : ZF f) : ZF (z • f) := fun l =>
  ⟨by rw [map_smul, (hf l).1, smul_zero], by rw [map_smul, (hf l).2, smul_zero]⟩

theorem cf_c (m : Fin r) : CF (coord (vc m) : Fn r) := ⟨by rw [ec, if_neg (vc_vz m).symm], by rw [ec, if_neg (vc_vzb m).symm]⟩
theorem cf_cb (m : Fin r) : CF (coord (vcb m) : Fn r) := ⟨by rw [ec, if_neg (vcb_vz m).symm], by rw [ec, if_neg (vcb_vzb m).symm]⟩
theorem cf_ci (m : Fin r) : CF ((coord (vc m))⁻¹ : Fn r) := ⟨by rw [eci, if_neg (vc_vz m).symm], by rw [eci, if_neg (vc_vzb m).symm]⟩
theorem cf_cbi (m : Fin r) : CF ((coord (vcb m))⁻¹ : Fn r) := ⟨by rw [eci, if_neg (vcb_vz m).symm], by rw [eci, if_neg (vcb_vzb m).symm]⟩

theorem partialDerivBar_def (l : Fin r) : (pbP l : Pr r) = mk (mulOp 1 * euler (vcb l)) (-(mulOp 1 * euler (vc l))) := by
  have : mulOp (1 : Fn r) = 1 := by ext h : 1; simp [mulOp]
  rw [this, one_mul, one_mul]; rfl

theorem partialDeriv_mul_fn (l : Fin r) (f fb : Fn r) : pP l * fnP f fb = fnP f fb * pP l + fnP (euler (vc l) f) (euler (vcb l) fb) := by
  rw [partialDeriv_def, der_fn, one_mul, one_mul]
theorem partialDerivBar_mul_fn (l : Fin r) (f fb : Fn r) : pbP l * fnP f fb = fnP f fb * pbP l + fnP (euler (vcb l) f) (euler (vc l) fb) := by
  rw [partialDerivBar_def, der_fn, one_mul, one_mul]

theorem comm_eu (v w : Var r) (f : Fn r) (h : euler v f = 0) :
    euler v * (mulOp f * euler w) = (mulOp f * euler w) * euler v := by
  have h0 : mulOp (0 : Fn r) = 0 := by ext h : 1; simp [mulOp]
  rw [← mul_assoc, eulerMul, h, h0, add_zero, mul_assoc, mul_assoc, eulerComm]

theorem mk_comm (X Xs Y Ys : Op r) (h1 : X * Y = Y * X) (h2 : Xs * Ys = Ys * Xs) : mk X Xs * mk Y Ys = mk Y Ys * mk X Xs := by
  refine Prod.ext h1 ?_
  show MulOpposite.op (Ys * Xs) = MulOpposite.op (Xs * Ys)
  rw [h2]

theorem partialDeriv_commute_nab (l : Fin r) (a TT : ℝ) : pP l * nabE a TT = nabE a TT * pP l := by
  unfold nabE
  rw [zbP, ggiP, multiplierPair_mul, smul_fnP, mul_add, add_mul, partialDeriv_mul_fn,
    ((zf_smul _ (zf_mul zf_zb (zf_ggi TT))) l).1, ((zf_smul _ (zf_mul zeta_free_of_variable (zf_ggi TT))) l).2, multiplierPair_zero, add_zero]
  congr 1
  apply mk_comm
  · exact comm_eu _ _ _ (zf_zi l).1
  · rw [neg_mul_neg, neg_mul_neg]; exact comm_eu _ _ _ (zf_zbi l).2
theorem partialDerivBar_commute_nab (l : Fin r) (a TT : ℝ) : pbP l * nabE a TT = nabE a TT * pbP l := by
  unfold nabE
  rw [zbP, ggiP, multiplierPair_mul, smul_fnP, mul_add, add_mul, partialDerivBar_mul_fn,
    ((zf_smul _ (zf_mul zf_zb (zf_ggi TT))) l).2, ((zf_smul _ (zf_mul zeta_free_of_variable (zf_ggi TT))) l).1, multiplierPair_zero, add_zero]
  congr 1
  apply mk_comm
  · exact comm_eu _ _ _ (zf_zi l).2
  · rw [neg_mul_neg, neg_mul_neg]; exact comm_eu _ _ _ (zf_zbi l).1
theorem partialDeriv_commute_nabs (l : Fin r) (a TT : ℝ) : pP l * nabsE a TT = nabsE a TT * pP l := by
  unfold nabsE
  rw [zP, ggiP, multiplierPair_mul, smul_fnP, mul_add, add_mul, partialDeriv_mul_fn,
    ((zf_smul _ (zf_mul zeta_free_of_variable (zf_ggi TT))) l).1, ((zf_smul _ (zf_mul zf_zb (zf_ggi TT))) l).2, multiplierPair_zero, add_zero,
    mul_neg, neg_mul]
  congr 2
  apply mk_comm
  · exact comm_eu _ _ _ (zf_zbi l).1
  · rw [neg_mul_neg, neg_mul_neg]; exact comm_eu _ _ _ (zf_zi l).2
theorem partialDerivBar_commute_nabs (l : Fin r) (a TT : ℝ) : pbP l * nabsE a TT = nabsE a TT * pbP l := by
  unfold nabsE
  rw [zP, ggiP, multiplierPair_mul, smul_fnP, mul_add, add_mul, partialDerivBar_mul_fn,
    ((zf_smul _ (zf_mul zeta_free_of_variable (zf_ggi TT))) l).2, ((zf_smul _ (zf_mul zf_zb (zf_ggi TT))) l).1, multiplierPair_zero, add_zero,
    mul_neg, neg_mul]
  congr 2
  apply mk_comm
  · exact comm_eu _ _ _ (zf_zbi l).2
  · rw [neg_mul_neg, neg_mul_neg]; exact comm_eu _ _ _ (zf_zi l).1

theorem nabs_zbi (a TT : ℝ) : nabsE a TT * (zbiP : Pr r) = zbiP * nabsE a TT + zbiP * zbiP := by
  rw [zbiP, nabsE_fn, eci, eci, if_pos rfl, if_pos rfl, multiplierPair_mul, sub_eq_add_neg, multiplierPair_neg]
  congr 2 <;> ring
theorem nab_cf (a TT : ℝ) (f fb : Fn r) (h1 : euler vz f = 0) (h2 : euler vzb fb = 0) :
    nabE a TT * fnP f fb = fnP f fb * nabE a TT := by
  rw [nabE_fn, h1, h2, mul_zero, mul_zero, multiplierPair_zero, add_zero]
theorem nabs_cf (a TT : ℝ) (f fb : Fn r) (h1 : euler vzb f = 0) (h2 : euler vz fb = 0) :
    nabsE a TT * fnP f fb = fnP f fb * nabsE a TT := by
  rw [nabsE_fn, h1, h2, mul_zero, mul_zero, multiplierPair_zero, sub_zero]

local macro "mx2_dg" : tactic => `(tactic| (simp only [pA, pbA, cA, ciA, cbA, cbiA, zA, ziA, zbA, zbiA, ggA, ggiA, nabA_eq, nabsA_eq, sc,
  Matrix.scalar_apply, Matrix.diagonal_mul_diagonal, Matrix.diagonal_add, Matrix.diagonal_sub, ← Matrix.diagonal_one]; congr 1; funext π))

theorem levNab : LevNab := by
  intro P
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · mx2_dg; exact nabla_zeta_comm _ _
  · mx2_dg; exact nab_zi _ _
  · mx2_dg; exact nab_zb _ _
  · mx2_dg; exact nab_cf _ _ _ _ (by rw [eci, if_neg vz_ne]) (by rw [eci, if_neg vz_ne.symm])
  · mx2_dg; exact nab_gg _ _
  · mx2_dg; exact nab_ggi _ _
  · rintro x (((⟨m, rfl⟩ | ⟨m, rfl⟩) | ⟨m, rfl⟩) | ⟨m, rfl⟩)
    · mx2_dg; exact nab_cf _ _ _ _ (cf_c m).1 (cf_cb m).2
    · mx2_dg; exact nab_cf _ _ _ _ (cf_ci m).1 (cf_cbi m).2
    · mx2_dg; exact nab_cf _ _ _ _ (cf_cb m).1 (cf_c m).2
    · mx2_dg; exact nab_cf _ _ _ _ (cf_cbi m).1 (cf_ci m).2

theorem levNabs : LevNabs := by
  intro P
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · mx2_dg; exact nabs_zb _ _
  · mx2_dg; exact nabs_zbi _ _
  · mx2_dg; exact nabs_cf _ _ _ _ (by rw [ec, if_neg vz_ne.symm]) (by rw [ec, if_neg vz_ne])
  · mx2_dg; exact nabs_cf _ _ _ _ (by rw [eci, if_neg vz_ne.symm]) (by rw [eci, if_neg vz_ne])
  · mx2_dg; exact nabs_gg _ _
  · mx2_dg; exact nabs_ggi _ _
  · rintro x (((⟨m, rfl⟩ | ⟨m, rfl⟩) | ⟨m, rfl⟩) | ⟨m, rfl⟩)
    · mx2_dg; exact nabs_cf _ _ _ _ (cf_c m).2 (cf_cb m).1
    · mx2_dg; exact nabs_cf _ _ _ _ (cf_ci m).2 (cf_cbi m).1
    · mx2_dg; exact nabs_cf _ _ _ _ (cf_cb m).2 (cf_c m).1
    · mx2_dg; exact nabs_cf _ _ _ _ (cf_cbi m).2 (cf_ci m).1

theorem levPP : LevPP := by
  intro P l m
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · mx2_dg; exact mk_comm _ _ _ _ (eulerComm _ _ _) (by rw [neg_mul_neg, neg_mul_neg]; exact eulerComm _ _ _)
  · mx2_dg; exact mk_comm _ _ _ _ (eulerComm _ _ _) (by rw [neg_mul_neg, neg_mul_neg]; exact eulerComm _ _ _)
  · mx2_dg; exact mk_comm _ _ _ _ (eulerComm _ _ _) (by rw [neg_mul_neg, neg_mul_neg]; exact eulerComm _ _ _)
  · mx2_dg; exact partialDeriv_commute_nab _ _ _
  · mx2_dg; exact partialDerivBar_commute_nab _ _ _
  · mx2_dg; exact partialDeriv_commute_nabs _ _ _
  · mx2_dg; exact partialDerivBar_commute_nabs _ _ _

theorem pP_0 (l : Fin r) (f fb : Fn r) (h1 : euler (vc l) f = 0) (h2 : euler (vcb l) fb = 0) :
    pP l * fnP f fb = fnP f fb * pP l := by rw [partialDeriv_mul_fn, h1, h2, multiplierPair_zero, add_zero]
theorem pbP_0 (l : Fin r) (f fb : Fn r) (h1 : euler (vcb l) f = 0) (h2 : euler (vc l) fb = 0) :
    pbP l * fnP f fb = fnP f fb * pbP l := by rw [partialDerivBar_mul_fn, h1, h2, multiplierPair_zero, add_zero]

theorem levP : LevP := by
  intro P l
  refine ⟨?_, ?_, ?_⟩
  · intro m
    by_cases h : l = m
    · subst h; rw [if_pos rfl]; mx2_dg; exact p_c l
    · rw [if_neg h, add_zero]; mx2_dg
      exact pP_0 _ _ _ (by rw [ec, if_neg (fun e => h ((vc_inj _ _).1 e))]) (by rw [ec, if_neg (fun e => h ((vcb_inj _ _).1 e))])
  · intro m
    by_cases h : l = m
    · subst h; rw [if_pos rfl]; mx2_dg; exact p_ci l
    · rw [if_neg h, sub_zero]; mx2_dg
      exact pP_0 _ _ _ (by rw [eci, if_neg (fun e => h ((vc_inj _ _).1 e))]) (by rw [eci, if_neg (fun e => h ((vcb_inj _ _).1 e))])
  · rintro x ((⟨m, rfl⟩ | ⟨m, rfl⟩) | hx)
    · mx2_dg; exact pP_0 _ _ _ (by rw [ec, if_neg (vc_vcb _ _)]) (by rw [ec, if_neg (vc_vcb _ _).symm])
    · mx2_dg; exact pP_0 _ _ _ (by rw [eci, if_neg (vc_vcb _ _)]) (by rw [eci, if_neg (vc_vcb _ _).symm])
    · simp only [zfnsA, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
      · mx2_dg; exact pP_0 _ _ _ (zeta_free_of_variable l).1 (zf_zb l).2
      · mx2_dg; exact pP_0 _ _ _ (zf_zi l).1 (zf_zbi l).2
      · mx2_dg; exact pP_0 _ _ _ (zf_zb l).1 (zeta_free_of_variable l).2
      · mx2_dg; exact pP_0 _ _ _ (zf_zbi l).1 (zf_zi l).2
      · mx2_dg; exact pP_0 _ _ _ (zf_gg _ l).1 (zf_gg _ l).2
      · mx2_dg; exact pP_0 _ _ _ (zf_ggi _ l).1 (zf_ggi _ l).2

theorem levPb : LevPb := by
  intro P l
  refine ⟨?_, ?_, ?_⟩
  · intro m
    by_cases h : l = m
    · subst h; rw [if_pos rfl]; mx2_dg
      rw [cbP, partialDerivBar_mul_fn, ec, ec, if_pos rfl, if_pos rfl]
    · rw [if_neg h, add_zero]; mx2_dg
      exact pbP_0 _ _ _ (by rw [ec, if_neg (fun e => h ((vcb_inj _ _).1 e))]) (by rw [ec, if_neg (fun e => h ((vc_inj _ _).1 e))])
  · intro m
    by_cases h : l = m
    · subst h; rw [if_pos rfl]; mx2_dg
      rw [cbiP, partialDerivBar_mul_fn, eci, eci, if_pos rfl, if_pos rfl, sub_eq_add_neg, multiplierPair_neg]
    · rw [if_neg h, sub_zero]; mx2_dg
      exact pbP_0 _ _ _ (by rw [eci, if_neg (fun e => h ((vcb_inj _ _).1 e))]) (by rw [eci, if_neg (fun e => h ((vc_inj _ _).1 e))])
  · rintro x ((⟨m, rfl⟩ | ⟨m, rfl⟩) | hx)
    · mx2_dg; exact pbP_0 _ _ _ (by rw [ec, if_neg (vc_vcb _ _).symm]) (by rw [ec, if_neg (vc_vcb _ _)])
    · mx2_dg; exact pbP_0 _ _ _ (by rw [eci, if_neg (vc_vcb _ _).symm]) (by rw [eci, if_neg (vc_vcb _ _)])
    · simp only [zfnsA, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
      · mx2_dg; exact pbP_0 _ _ _ (zeta_free_of_variable l).2 (zf_zb l).1
      · mx2_dg; exact pbP_0 _ _ _ (zf_zi l).2 (zf_zbi l).1
      · mx2_dg; exact pbP_0 _ _ _ (zf_zb l).2 (zeta_free_of_variable l).1
      · mx2_dg; exact pbP_0 _ _ _ (zf_zbi l).2 (zf_zi l).1
      · mx2_dg; exact pbP_0 _ _ _ (zf_gg _ l).2 (zf_gg _ l).1
      · mx2_dg; exact pbP_0 _ _ _ (zf_ggi _ l).2 (zf_ggi _ l).1

theorem form (P : Par) (x : A P) (hx : x ∈ fnsA P) : ∃ f fb, x = sc P (fnP f fb) := by
  rcases hx with ((((⟨m, rfl⟩ | ⟨m, rfl⟩) | ⟨m, rfl⟩) | ⟨m, rfl⟩) | hx)
  · exact ⟨_, _, rfl⟩
  · exact ⟨_, _, rfl⟩
  · exact ⟨_, _, rfl⟩
  · exact ⟨_, _, rfl⟩
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨_, _, rfl⟩

theorem inv1 (f fb : Fn r) (h : f ≠ 0) (hb : fb ≠ 0) : fnP f fb * fnP f⁻¹ fb⁻¹ = 1 := by
  rw [multiplierPair_mul, mul_inv_cancel₀ h, mul_inv_cancel₀ hb, multiplierPair_one]
theorem inv2 (f fb : Fn r) (h : f ≠ 0) (hb : fb ≠ 0) : fnP f⁻¹ fb⁻¹ * fnP f fb = 1 := by
  rw [multiplierPair_mul, inv_mul_cancel₀ h, inv_mul_cancel₀ hb, multiplierPair_one]

theorem levFns : LevFns := by
  intro P
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx y hy
    obtain ⟨f, fb, rfl⟩ := form P x hx
    obtain ⟨g, gb, rfl⟩ := form P y hy
    mx2_dg; exact multiplierPair_comm _ _ _ _
  · intro l
    refine ⟨?_, ?_, ?_, ?_⟩
    · mx2_dg; exact inv1 _ _ (coord_ne _ _) (coord_ne _ _)
    · mx2_dg; exact inv2 _ _ (coord_ne _ _) (coord_ne _ _)
    · mx2_dg; exact inv1 _ _ (coord_ne _ _) (coord_ne _ _)
    · mx2_dg; exact inv2 _ _ (coord_ne _ _) (coord_ne _ _)
  · mx2_dg; exact inv1 _ _ (coord_ne _ _) (coord_ne _ _)
  · mx2_dg; exact inv2 _ _ (coord_ne _ _) (coord_ne _ _)
  · mx2_dg; exact inv1 _ _ (coord_ne _ _) (coord_ne _ _)
  · mx2_dg; exact inv2 _ _ (coord_ne _ _) (coord_ne _ _)
  · mx2_dg; exact inv1 _ _ (gg_ne _) (gg_ne _)
  · mx2_dg; exact inv2 _ _ (gg_ne _) (gg_ne _)
  · rw [Matrix.algebraMap_eq_diagonal]
    mx2_dg
    rw [Pi.algebraMap_apply, Algebra.algebraMap_eq_smul_one, ← multiplierPair_one, smul_fnP, zP, zbP, multiplierPair_mul, sub_eq_add_neg, multiplierPair_neg,
      multiplierPair_add, ggP]
    congr 1
    · unfold gg; rw [Algebra.algebraMap_eq_smul_one, sub_eq_add_neg]
    · unfold gg; rw [Algebra.algebraMap_eq_smul_one, sub_eq_add_neg, mul_comm]

theorem levelAssemble : LevelAssemble := by
  intro hF hP hPb hPP hN hNs P
  have z1 : zA P ∈ zfnsA P := by simp [zfnsA]
  have z2 : ziA P ∈ zfnsA P := by simp [zfnsA]
  have z3 : zbA P ∈ zfnsA P := by simp [zfnsA]
  have z4 : zbiA P ∈ zfnsA P := by simp [zfnsA]
  have z5 : ggA P ∈ zfnsA P := by simp [zfnsA]
  have z6 : ggiA P ∈ zfnsA P := by simp [zfnsA]
  obtain ⟨f0, f1, f2, f3, f4, f5, f6, f7, f8⟩ := hF P
  obtain ⟨n1, n2, n3, n4, n5, n6, n7⟩ := hN P
  obtain ⟨s1, s2, s3, s4, s5, s6, s7⟩ := hNs P
  refine ⟨{
    p := pA P, pb := pbA P, c := cA P, ci := ciA P, cb := cbA P, cbi := cbiA P, ζ := zA P, ζi := ziA P,
    ζb := zbA P, ζbi := zbiA P, GG := ggA P, GGi := ggiA P, nab := nabA P, nabs := nabsA P, TT := (P.TT : ℂ),
    fns_comm := f0,
    c_ci := fun l => (f1 l).1, ci_c := fun l => (f1 l).2.1, cb_cbi := fun l => (f1 l).2.2.1, cbi_cb := fun l => (f1 l).2.2.2,
    ζ_ζi := f2, ζi_ζ := f3, ζb_ζbi := f4, ζbi_ζb := f5, GG_GGi := f6, GGi_GG := f7, GG_def := f8,
    p_c := fun l m => (hP P l).1 m, p_ci := fun l m => (hP P l).2.1 m,
    p_cb := fun l m => (hP P l).2.2 _ (Or.inl (Or.inl ⟨m, rfl⟩)), p_cbi := fun l m => (hP P l).2.2 _ (Or.inl (Or.inr ⟨m, rfl⟩)),
    p_ζ := fun l => (hP P l).2.2 _ (Or.inr z1), p_ζi := fun l => (hP P l).2.2 _ (Or.inr z2),
    p_ζb := fun l => (hP P l).2.2 _ (Or.inr z3), p_ζbi := fun l => (hP P l).2.2 _ (Or.inr z4),
    p_GG := fun l => (hP P l).2.2 _ (Or.inr z5), p_GGi := fun l => (hP P l).2.2 _ (Or.inr z6),
    pb_cb := fun l m => (hPb P l).1 m, pb_cbi := fun l m => (hPb P l).2.1 m,
    pb_c := fun l m => (hPb P l).2.2 _ (Or.inl (Or.inl ⟨m, rfl⟩)), pb_ci := fun l m => (hPb P l).2.2 _ (Or.inl (Or.inr ⟨m, rfl⟩)),
    pb_ζ := fun l => (hPb P l).2.2 _ (Or.inr z1), pb_ζi := fun l => (hPb P l).2.2 _ (Or.inr z2),
    pb_ζb := fun l => (hPb P l).2.2 _ (Or.inr z3), pb_ζbi := fun l => (hPb P l).2.2 _ (Or.inr z4),
    pb_GG := fun l => (hPb P l).2.2 _ (Or.inr z5), pb_GGi := fun l => (hPb P l).2.2 _ (Or.inr z6),
    p_p := fun l m => (hPP P l m).1, p_pb := fun l m => (hPP P l m).2.1, pb_pb := fun l m => (hPP P l m).2.2.1,
    p_nab := fun l => (hPP P l l).2.2.2.1, pb_nab := fun l => (hPP P l l).2.2.2.2.1,
    p_nabs := fun l => (hPP P l l).2.2.2.2.2.1, pb_nabs := fun l => (hPP P l l).2.2.2.2.2.2,
    nab_ζ := n1, nab_ζi := n2, nab_ζb := n3, nab_ζbi := n4, nab_GG := n5, nab_GGi := n6,
    nab_c := fun l => n7 _ (Or.inl (Or.inl (Or.inl ⟨l, rfl⟩))), nab_ci := fun l => n7 _ (Or.inl (Or.inl (Or.inr ⟨l, rfl⟩))),
    nab_cb := fun l => n7 _ (Or.inl (Or.inr ⟨l, rfl⟩)), nab_cbi := fun l => n7 _ (Or.inr ⟨l, rfl⟩),
    nabs_ζb := s1, nabs_ζbi := s2, nabs_ζ := s3, nabs_ζi := s4, nabs_GG := s5, nabs_GGi := s6,
    nabs_c := fun l => s7 _ (Or.inl (Or.inl (Or.inl ⟨l, rfl⟩))), nabs_ci := fun l => s7 _ (Or.inl (Or.inl (Or.inr ⟨l, rfl⟩))),
    nabs_cb := fun l => s7 _ (Or.inl (Or.inr ⟨l, rfl⟩)), nabs_cbi := fun l => s7 _ (Or.inr ⟨l, rfl⟩) }, ?_⟩
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem levelExists : LevelExists := levelAssemble levFns levP levPb levPP levNab levNabs

end Formalism.FourierDecayAlt.P.Mx2

namespace Formalism.FourierDecayAlt.P

theorem level_function_relations : Formalism.FourierDecayAlt.M.LevFns := Mx2.levFns
theorem level_p_relations : Formalism.FourierDecayAlt.M.LevP := Mx2.levP
theorem level_pb_relations : Formalism.FourierDecayAlt.M.LevPb := Mx2.levPb
theorem level_pp_relations : Formalism.FourierDecayAlt.M.LevPP := Mx2.levPP
theorem level_nabla_relations : Formalism.FourierDecayAlt.M.LevNab := Mx2.levNab
theorem level_nabla_star_relations : Formalism.FourierDecayAlt.M.LevNabs := Mx2.levNabs
theorem level_exists_model : Formalism.FourierDecayAlt.M.LevelExists := Mx2.levelExists
theorem level_assemble : Formalism.FourierDecayAlt.M.LevelAssemble := Mx2.levelAssemble

end Formalism.FourierDecayAlt.P
