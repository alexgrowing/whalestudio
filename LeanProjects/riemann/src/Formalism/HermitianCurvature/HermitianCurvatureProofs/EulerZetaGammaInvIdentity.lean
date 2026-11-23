import Formalism.HermitianCurvature.StatementM

open Formalism.FourierDecayAlt.M Formalism.FourierDecayAlt Finset

namespace Formalism.FourierDecayAlt.P.Mx4

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
      · simp [hv]
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

theorem eulerComm : EulerComm := by
  intro r v w
  ext f γ
  simp only [Module.End.mul_apply, euler, LinearMap.coe_mk, AddHom.coe_mk]
  ring

theorem coord_ne (r : ℕ) (v : Var r) : coord v ≠ 0 := by
  simp [coord]

variable {r : ℕ}

theorem mulOp_mul (f g : Fn r) : mulOp f * mulOp g = mulOp (f * g) := by
  ext h : 1; simp [mulOp]
theorem mulOp_add (f g : Fn r) : mulOp f + mulOp g = mulOp (f + g) := by
  ext h : 1; simp [mulOp, add_mul]
theorem mulOp_zero : mulOp (0 : Fn r) = 0 := by ext h : 1; simp [mulOp]

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
theorem multiplierPair_zero : (fnP 0 0 : Pr r) = 0 := by
  refine Prod.ext mulOp_zero ?_
  show MulOpposite.op (mulOp (0 : Fn r)) = 0
  rw [mulOp_zero]; rfl
theorem multiplierPair_neg (f fb : Fn r) : -fnP f fb = fnP (-f) (-fb) := by
  rw [neg_eq_iff_add_eq_zero, multiplierPair_add, add_neg_cancel, add_neg_cancel, multiplierPair_zero]
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

theorem ec (v w : Var r) : euler v (coord w) = if v = w then coord w else 0 := (eulerCoord r v w 0).1
theorem eci (v w : Var r) : euler v (coord w)⁻¹ = if v = w then -(coord w)⁻¹ else 0 := by
  rw [euler_inv _ _ (coord_ne r w), ec]
  split_ifs
  · field_simp [coord_ne r w]
  · simp

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

theorem comm_eu (v w : Var r) (f : Fn r) (h : euler v f = 0) :
    euler v * (mulOp f * euler w) = (mulOp f * euler w) * euler v := by
  rw [← mul_assoc, eulerMul, h, mulOp_zero, add_zero, mul_assoc, mul_assoc, eulerComm]

theorem mk_comm (X Xs Y Ys : Op r) (h1 : X * Y = Y * X) (h2 : Xs * Ys = Ys * Xs) : mk X Xs * mk Y Ys = mk Y Ys * mk X Xs := by
  refine Prod.ext h1 ?_
  show MulOpposite.op (Ys * Xs) = MulOpposite.op (Xs * Ys)
  rw [h2]

theorem dd_comm : (mulOp (coord vzb)⁻¹ * euler vzb : Op r) * (mulOp (coord vz)⁻¹ * euler vz) =
    (mulOp (coord vz)⁻¹ * euler vz) * (mulOp (coord vzb)⁻¹ * euler vzb) := by
  have h1 : euler vzb ((coord vz)⁻¹ : Fn r) = 0 := by rw [eci, if_neg vz_ne.symm]
  have h2 : euler vz ((coord vzb)⁻¹ : Fn r) = 0 := by rw [eci, if_neg vz_ne]
  have a1 := comm_eu vzb vz _ h1
  have a2 := comm_eu vz vzb _ h2
  calc (mulOp (coord vzb)⁻¹ * euler vzb : Op r) * (mulOp (coord vz)⁻¹ * euler vz)
      = mulOp (coord vzb)⁻¹ * (euler vzb * (mulOp (coord vz)⁻¹ * euler vz)) := mul_assoc _ _ _
    _ = mulOp (coord vzb)⁻¹ * ((mulOp (coord vz)⁻¹ * euler vz) * euler vzb) := by rw [a1]
    _ = (mulOp (coord vzb)⁻¹ * mulOp (coord vz)⁻¹) * (euler vz * euler vzb) := by simp only [mul_assoc]
    _ = (mulOp (coord vz)⁻¹ * mulOp (coord vzb)⁻¹) * (euler vzb * euler vz) := by
        rw [mulOp_mul, mulOp_mul, mul_comm (coord vzb)⁻¹ (coord vz)⁻¹, eulerComm r vz vzb]
    _ = mulOp (coord vz)⁻¹ * ((mulOp (coord vzb)⁻¹ * euler vzb) * euler vz) := by simp only [mul_assoc]
    _ = mulOp (coord vz)⁻¹ * (euler vz * (mulOp (coord vzb)⁻¹ * euler vzb)) := by rw [a2]
    _ = (mulOp (coord vz)⁻¹ * euler vz) * (mulOp (coord vzb)⁻¹ * euler vzb) := (mul_assoc _ _ _).symm

theorem dz_comm : (dzbP : Pr r) * dzP = dzP * dzbP := by
  apply mk_comm
  · exact dd_comm
  · rw [neg_mul_neg, neg_mul_neg]; exact dd_comm.symm

theorem key_zb (TT : ℝ) : (coord vzb)⁻¹ * euler vzb (coord vzb * (gg TT)⁻¹ : Fn r) =
    -(algebraMap ℂ (Fn r) (TT : ℂ) * ((gg TT)⁻¹ * (gg TT)⁻¹)) := by
  have hg : (coord vz * coord vzb : Fn r) = gg TT + algebraMap ℂ (Fn r) (TT : ℂ) := by unfold gg; ring
  have h1 := gg_ne (r := r) TT
  have h2 := coord_ne r vzb
  rw [eulerLeibniz, ec, if_pos rfl, euler_inv _ _ h1, euler_gg_zb, hg]
  field_simp
  ring

theorem euler_zeta_gamma_inv_identity (TT : ℝ) : (coord vz)⁻¹ * euler vz (coord vz * (gg TT)⁻¹ : Fn r) =
    -(algebraMap ℂ (Fn r) (TT : ℂ) * ((gg TT)⁻¹ * (gg TT)⁻¹)) := by
  have hg : (coord vz * coord vzb : Fn r) = gg TT + algebraMap ℂ (Fn r) (TT : ℂ) := by unfold gg; ring
  have h1 := gg_ne (r := r) TT
  have h2 := coord_ne r vz
  rw [eulerLeibniz, ec, if_pos rfl, euler_inv _ _ h1, euler_GG_z, hg]
  field_simp
  ring

theorem curv (a TT : ℝ) :
    (-dzbP + (a : ℂ) • (zP * ggiP TT)) * (dzP + (a : ℂ) • (zbP * ggiP TT)) -
      (dzP + (a : ℂ) • (zbP * ggiP TT)) * (-dzbP + (a : ℂ) • (zP * ggiP TT)) =
      (algebraMap ℂ (Pr r) ((2 * a * TT : ℝ) : ℂ)) * ggiP TT * ggiP TT := by
  have e1 : (dzbP : Pr r) * fnP ((a : ℂ) • (coord vzb * (gg TT)⁻¹)) ((a : ℂ) • (coord vz * (gg TT)⁻¹)) =
      fnP ((a : ℂ) • (coord vzb * (gg TT)⁻¹)) ((a : ℂ) • (coord vz * (gg TT)⁻¹)) * dzbP +
      fnP ((coord vzb)⁻¹ * euler vzb ((a : ℂ) • (coord vzb * (gg TT)⁻¹)))
        ((coord vz)⁻¹ * euler vz ((a : ℂ) • (coord vz * (gg TT)⁻¹))) := by
    rw [dzbP, der_fn]
  have e2 : (dzP : Pr r) * fnP ((a : ℂ) • (coord vz * (gg TT)⁻¹)) ((a : ℂ) • (coord vzb * (gg TT)⁻¹)) =
      fnP ((a : ℂ) • (coord vz * (gg TT)⁻¹)) ((a : ℂ) • (coord vzb * (gg TT)⁻¹)) * dzP +
      fnP ((coord vz)⁻¹ * euler vz ((a : ℂ) • (coord vz * (gg TT)⁻¹)))
        ((coord vzb)⁻¹ * euler vzb ((a : ℂ) • (coord vzb * (gg TT)⁻¹))) := by
    rw [dzP, der_fn]
  rw [mul_assoc, ← Algebra.smul_def, zP, zbP, ggiP, multiplierPair_mul, multiplierPair_mul, multiplierPair_mul, smul_fnP, smul_fnP, smul_fnP]
  simp only [map_smul, mul_smul_comm, euler_zeta_gamma_inv_identity, key_zb] at e1 e2
  have e3 := multiplierPair_comm ((a : ℂ) • (coord vz * (gg TT)⁻¹ : Fn r)) ((a : ℂ) • (coord vzb * (gg TT)⁻¹))
    ((a : ℂ) • (coord vzb * (gg TT)⁻¹)) ((a : ℂ) • (coord vz * (gg TT)⁻¹))
  have e4 : fnP (((2 * a * TT : ℝ) : ℂ) • ((gg TT)⁻¹ * (gg TT)⁻¹ : Fn r)) (((2 * a * TT : ℝ) : ℂ) • ((gg TT)⁻¹ * (gg TT)⁻¹)) =
      -fnP ((a : ℂ) • -(algebraMap ℂ (Fn r) (TT : ℂ) * ((gg TT)⁻¹ * (gg TT)⁻¹)))
        ((a : ℂ) • -(algebraMap ℂ (Fn r) (TT : ℂ) * ((gg TT)⁻¹ * (gg TT)⁻¹))) -
      fnP ((a : ℂ) • -(algebraMap ℂ (Fn r) (TT : ℂ) * ((gg TT)⁻¹ * (gg TT)⁻¹)))
        ((a : ℂ) • -(algebraMap ℂ (Fn r) (TT : ℂ) * ((gg TT)⁻¹ * (gg TT)⁻¹))) := by
    rw [multiplierPair_neg, sub_eq_add_neg, multiplierPair_neg, multiplierPair_add]
    have : (((2 * a * TT : ℝ) : ℂ) • ((gg TT)⁻¹ * (gg TT)⁻¹ : Fn r)) =
        -((a : ℂ) • -(algebraMap ℂ (Fn r) (TT : ℂ) * ((gg TT)⁻¹ * (gg TT)⁻¹))) +
        -((a : ℂ) • -(algebraMap ℂ (Fn r) (TT : ℂ) * ((gg TT)⁻¹ * (gg TT)⁻¹))) := by
      simp only [Algebra.smul_def]
      push_cast
      simp only [map_ofNat]
      ring
    rw [← this]
  rw [e4]
  simp only [add_mul, mul_add, neg_mul, mul_neg]
  rw [e1, e2, e3, dz_comm]
  abel

theorem rho_eq (P : Par) (π : Ty P) (i : ℕ) (h : 1 ≤ i ∧ i ≤ P.k - 1) :
    rho P π i = P.lo i + (((π ⟨i - 1, by omega⟩ : Fin _) : ℕ) : ℝ) := by
  simp only [rho, dif_pos h]

theorem tyInterlaces : TyInterlaces := by
  intro P hP π i hi
  have h := Finset.mem_Icc.1 hi
  have hg := hP.gap i hi
  rw [rho_eq P π i h]
  have hb : ((π ⟨i - 1, by omega⟩ : Fin _) : ℕ) ≤ P.wid i := by
    have := (π ⟨i - 1, by omega⟩).2
    have e : i - 1 + 1 = i := by omega
    simp only [e] at this
    omega
  have hw : (P.wid i : ℝ) ≤ P.hi i - P.lo i := Nat.floor_le (by linarith)
  have hb' : (((π ⟨i - 1, by omega⟩ : Fin _) : ℕ) : ℝ) ≤ P.wid i := by exact_mod_cast hb
  have h0 : (0 : ℝ) ≤ (((π ⟨i - 1, by omega⟩ : Fin _) : ℕ) : ℝ) := Nat.cast_nonneg _
  have a1 : P.hi i ≤ P.u i - 1 / 2 := by unfold Par.hi; linarith [min_le_left (P.u i) (P.u' i)]
  have a2 : P.hi i ≤ P.u' i - 1 / 2 := by unfold Par.hi; linarith [min_le_right (P.u i) (P.u' i)]
  have a3 : P.u (i + 1) + 1 / 2 ≤ P.lo i := by unfold Par.lo; linarith [le_max_left (P.u (i + 1)) (P.u' (i + 1))]
  have a4 : P.u' (i + 1) + 1 / 2 ≤ P.lo i := by unfold Par.lo; linarith [le_max_right (P.u (i + 1)) (P.u' (i + 1))]
  refine ⟨by linarith, by linarith, by linarith, by linarith⟩

theorem rhoUp : RhoUp := by
  intro P l π π' hU i hi
  have h := Finset.mem_Icc.1 hi
  rw [rho_eq P π i h, rho_eq P π' i h, hU ⟨i - 1, by omega⟩]
  have e : i - 1 + 1 = i := by omega
  simp only [e]
  split_ifs <;> push_cast <;> ring

theorem mono (k : ℕ) (u u' ρ : ℕ → ℝ) (h : I.Interlaces k u u' ρ) :
    ∀ d i, 1 ≤ i → i + d ≤ k → u (i + d) ≤ u i ∧ u' (i + d) ≤ u' i := by
  intro d
  induction d with
  | zero => intro i _ _; simp
  | succ d ih =>
    intro i h1 h2
    have a := ih i h1 (by omega)
    have b := h (i + d) (Finset.mem_Icc.2 ⟨by omega, by omega⟩)
    have e : i + (d + 1) = i + d + 1 := by ring
    rw [e]
    constructor <;> linarith [b.1, b.2.1, b.2.2.1, b.2.2.2]

theorem val_congr (P : Par) (π : Ty P) (a b : Fin (P.k - 1)) (h : a = b) :
    ((π a : Fin _) : ℕ) = ((π b : Fin _) : ℕ) := by subst h; rfl

theorem lo_int (P : Par) (hP : P.OK) (i : ℕ) (hi : i ∈ Icc 1 (P.k - 1)) : ∃ n : ℤ, P.lo i - P.u 1 - 1 / 2 = n := by
  have h := Finset.mem_Icc.1 hi
  obtain ⟨a, ha⟩ := hP.int_u (i + 1) (Finset.mem_Icc.2 ⟨by omega, by omega⟩)
  obtain ⟨b, hb⟩ := hP.int_u' (i + 1) (Finset.mem_Icc.2 ⟨by omega, by omega⟩)
  unfold Par.lo
  rcases max_choice (P.u (i + 1)) (P.u' (i + 1)) with h | h
  · exact ⟨a, by rw [h]; linarith⟩
  · exact ⟨b, by rw [h]; linarith⟩

theorem hi_int (P : Par) (hP : P.OK) (i : ℕ) (hi : i ∈ Icc 1 (P.k - 1)) : ∃ n : ℤ, P.hi i - P.u 1 + 1 / 2 = n := by
  have h := Finset.mem_Icc.1 hi
  obtain ⟨a, ha⟩ := hP.int_u i (Finset.mem_Icc.2 ⟨by omega, by omega⟩)
  obtain ⟨b, hb⟩ := hP.int_u' i (Finset.mem_Icc.2 ⟨by omega, by omega⟩)
  unfold Par.hi
  rcases min_choice (P.u i) (P.u' i) with h | h
  · exact ⟨a, by rw [h]; linarith⟩
  · exact ⟨b, by rw [h]; linarith⟩

theorem floor_of_int (x : ℝ) (h0 : 0 ≤ x) (z : ℤ) (hz : x = z) : ((⌊x⌋₊ : ℕ) : ℝ) = x := by
  have hz0 : 0 ≤ z := by have : (0 : ℝ) ≤ (z : ℝ) := hz ▸ h0; exact_mod_cast this
  obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hz0
  rw [hz]; simp

theorem wid_eq (P : Par) (hP : P.OK) (i : ℕ) (hi : i ∈ Icc 1 (P.k - 1)) : (P.wid i : ℝ) = P.hi i - P.lo i := by
  obtain ⟨a, ha⟩ := lo_int P hP i hi
  obtain ⟨b, hb⟩ := hi_int P hP i hi
  exact floor_of_int _ (by linarith [hP.gap i hi]) (b - a - 1) (by push_cast; linarith)

theorem ord (k : ℕ) (u u' ρ : ℕ → ℝ) (hI : I.Interlaces k u u' ρ) (l : ℕ) (hl : l ∈ Icc 1 (k - 1)) :
    (∀ i ∈ Icc 1 k, i ≤ l → u l ≤ u i ∧ u' l ≤ u' i) ∧ (∀ i ∈ Icc 1 k, l < i → u i ≤ u (l + 1) ∧ u' i ≤ u' (l + 1)) ∧
    (∀ j ∈ Icc 1 (k - 1), j < l → u l + 1 / 2 ≤ ρ j ∧ u' l + 1 / 2 ≤ ρ j) ∧
    (∀ j ∈ Icc 1 (k - 1), l < j → ρ j + 1 / 2 ≤ u (l + 1) ∧ ρ j + 1 / 2 ≤ u' (l + 1)) := by
  have hm := mono k u u' ρ hI
  have hl' := Finset.mem_Icc.1 hl
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i hi h
    have hi' := Finset.mem_Icc.1 hi
    have c := hm (l - i) i hi'.1 (by omega)
    have e : i + (l - i) = l := by omega
    rwa [e] at c
  · intro i hi h
    have hi' := Finset.mem_Icc.1 hi
    have c := hm (i - (l + 1)) (l + 1) (by omega) (by omega)
    have e : l + 1 + (i - (l + 1)) = i := by omega
    rwa [e] at c
  · intro j hj h
    have hj' := Finset.mem_Icc.1 hj
    have b := hI j hj
    have c := hm (l - (j + 1)) (j + 1) (by omega) (by omega)
    have e : j + 1 + (l - (j + 1)) = l := by omega
    rw [e] at c
    constructor <;> linarith [b.2.2.1, b.2.2.2, c.1, c.2]
  · intro j hj h
    have hj' := Finset.mem_Icc.1 hj
    have b := hI j hj
    have c := hm (j - (l + 1)) (l + 1) (by omega) (by omega)
    have e : l + 1 + (j - (l + 1)) = j := by omega
    rw [e] at c
    constructor <;> linarith [b.1, b.2.1, c.1, c.2]

theorem nrm_pos (P : Par) (hP : P.OK) (l : ℕ) (hl : l ∈ Icc 1 (P.k - 1)) (π π' : Ty P) (hU : Up P l π π') :
    0 < Nrm P l π := by
  have hI := tyInterlaces P hP π
  have hI' := tyInterlaces P hP π'
  have hr := rhoUp P l π π' hU l hl
  rw [if_pos rfl] at hr
  have b' := hI' l hl
  rw [hr] at b'
  have b := hI l hl
  obtain ⟨o1, o2, o3, o4⟩ := ord P.k P.u P.u' (rho P π) hI l hl
  unfold Nrm I.qpoly
  apply div_pos
  · rw [neg_mul, neg_neg]
    apply mul_pos (mul_pos hP.T_pos hP.T'_pos)
    apply Finset.prod_pos
    intro i hi
    by_cases h : i ≤ l
    · have := o1 i hi h
      apply mul_pos <;> linarith [b'.1, b'.2.1, this.1, this.2]
    · have := o2 i hi (by omega)
      apply mul_pos_of_neg_of_neg <;> linarith [b.2.2.1, b.2.2.2, this.1, this.2]
  · rw [← Finset.prod_mul_distrib]
    apply Finset.prod_pos
    intro j hj
    have hj1 := Finset.mem_of_mem_erase hj
    have hj2 := Finset.ne_of_mem_erase hj
    by_cases h : j < l
    · have := o3 j hj1 h
      apply mul_pos <;> linarith [b'.1, b'.2.1, this.1, this.2]
    · have := o4 j hj1 (by omega)
      apply mul_pos_of_neg_of_neg <;> linarith [b.2.2.1, b.2.2.2, this.1, this.2]

theorem nrm_down (P : Par) (l : ℕ) (hl : l ∈ Icc 1 (P.k - 1)) (π π' : Ty P) (hU : Up P l π π') :
    NrmDown P l π' = Nrm P l π := by
  have hr := rhoUp P l π π' hU
  have hrl := hr l hl
  rw [if_pos rfl] at hrl
  unfold NrmDown Nrm
  rw [hrl]
  have e1 : ∏ j ∈ (Icc 1 (P.k - 1)).erase l, (rho P π' j - (rho P π l + 1) + 1) =
      ∏ j ∈ (Icc 1 (P.k - 1)).erase l, (rho P π j - rho P π l) := by
    refine Finset.prod_congr rfl ?_
    intro j hj
    rw [hr j (Finset.mem_of_mem_erase hj), if_neg (Finset.ne_of_mem_erase hj)]; ring
  have e2 : ∏ j ∈ (Icc 1 (P.k - 1)).erase l, (rho P π' j - (rho P π l + 1)) =
      ∏ j ∈ (Icc 1 (P.k - 1)).erase l, (rho P π j - rho P π l - 1) := by
    refine Finset.prod_congr rfl ?_
    intro j hj
    rw [hr j (Finset.mem_of_mem_erase hj), if_neg (Finset.ne_of_mem_erase hj)]; ring
  rw [e1, e2]
  congr 3
  ring

theorem top (P : Par) (hP : P.OK) (l : ℕ) (hl : l ∈ Icc 1 (P.k - 1)) (π : Ty P) (h : ¬ ∃ π', Up P l π π') :
    rho P π l = P.hi l := by
  have hl' := Finset.mem_Icc.1 hl
  have e : l - 1 + 1 = l := by omega
  by_contra hne
  apply h
  have hlt : ((π ⟨l - 1, by omega⟩ : Fin _) : ℕ) < P.wid l := by
    by_contra hge
    apply hne
    have h2 := (π ⟨l - 1, by omega⟩).2
    simp only [e] at h2
    have h3 : ((π ⟨l - 1, by omega⟩ : Fin _) : ℕ) = P.wid l := by omega
    rw [rho_eq P π l hl', h3, wid_eq P hP l hl]; ring
  refine ⟨fun i => if hi : (i : ℕ) + 1 = l then ⟨(π i : ℕ) + 1, ?_⟩ else π i, ?_⟩
  · have : i = ⟨l - 1, by omega⟩ := Fin.ext (by simp; omega)
    rw [val_congr P π _ _ this, hi]; omega
  · intro i
    by_cases hi : (i : ℕ) + 1 = l
    · simp [hi]
    · simp [hi]

theorem bot (P : Par) (l : ℕ) (hl : l ∈ Icc 1 (P.k - 1)) (π : Ty P) (h : ¬ ∃ π', Up P l π' π) :
    rho P π l = P.lo l := by
  have hl' := Finset.mem_Icc.1 hl
  by_contra hne
  apply h
  have hpos : 0 < ((π ⟨l - 1, by omega⟩ : Fin _) : ℕ) := by
    by_contra hge
    apply hne
    have h3 : ((π ⟨l - 1, by omega⟩ : Fin _) : ℕ) = 0 := by omega
    rw [rho_eq P π l hl', h3]; simp
  refine ⟨fun i => if hi : (i : ℕ) + 1 = l then ⟨(π i : ℕ) - 1, ?_⟩ else π i, ?_⟩
  · have := (π i).2; omega
  · intro i
    by_cases hi : (i : ℕ) + 1 = l
    · have : i = ⟨l - 1, by omega⟩ := Fin.ext (by simp; omega)
      have h5 := val_congr P π _ _ this
      simp [hi]; omega
    · simp [hi]

theorem nrmFacts : NrmFacts := by
  intro P hP l hl π
  have hl' := Finset.mem_Icc.1 hl
  refine ⟨fun π' hU => ⟨nrm_pos P hP l hl π π' hU, nrm_down P l hl π π' hU⟩, ?_, ?_⟩
  · intro h
    have ht := top P hP l hl π h
    unfold Nrm I.qpoly
    have : ∏ i ∈ Icc 1 P.k, ((-rho P π l - 1 + 1 / 2 + P.u i) * (-rho P π l - 1 + 1 / 2 + P.u' i)) = 0 := by
      apply Finset.prod_eq_zero (i := l) (Finset.mem_Icc.2 ⟨hl'.1, by omega⟩)
      rw [ht]; unfold Par.hi
      rcases min_choice (P.u l) (P.u' l) with h | h <;> rw [h] <;> ring
    rw [this]; simp
  · intro h
    have ht := bot P l hl π h
    unfold NrmDown I.qpoly
    have : ∏ i ∈ Icc 1 P.k, ((-rho P π l + 1 / 2 + P.u i) * (-rho P π l + 1 / 2 + P.u' i)) = 0 := by
      apply Finset.prod_eq_zero (i := l + 1) (Finset.mem_Icc.2 ⟨by omega, by omega⟩)
      rw [ht]; unfold Par.lo
      rcases max_choice (P.u (l + 1)) (P.u' (l + 1)) with h | h <;> rw [h] <;> ring
    rw [this]; simp

theorem up_fun (P : Par) (l : ℕ) (π π1 π2 : Ty P) (h1 : Up P l π π1) (h2 : Up P l π π2) : π1 = π2 := by
  funext i; apply Fin.ext; rw [h1 i, h2 i]

theorem up_inj (P : Par) (l : ℕ) (π π1 π2 : Ty P) (h1 : Up P l π1 π) (h2 : Up P l π2 π) : π1 = π2 := by
  funext i; apply Fin.ext
  exact Nat.add_right_cancel ((h1 i).symm.trans (h2 i))

theorem up_square (P : Par) (l j : ℕ) (hjl : j ≠ l) (π π1 π2 : Ty P) (h1 : Up P l π π1) (h2 : Up P j π1 π2) :
    ∃ π3, Up P j π π3 ∧ Up P l π3 π2 := by
  refine ⟨fun i => if (i : ℕ) + 1 = j then π2 i else π i, fun i => ?_, fun i => ?_⟩
  all_goals
    have a := h1 i
    have b := h2 i
    by_cases hj : (i : ℕ) + 1 = j
    · have hl : (i : ℕ) + 1 ≠ l := fun h => hjl (hj.symm.trans h)
      simp only [if_pos hj, if_neg hl] at a b ⊢; omega
    · by_cases hl : (i : ℕ) + 1 = l
      · simp only [if_neg hj, if_pos hl] at a b ⊢; omega
      · simp only [if_neg hj, if_neg hl] at a b ⊢; omega

theorem up_mixed1 (P : Par) (l j : ℕ) (hjl : j ≠ l) (π π1 π2 : Ty P) (h1 : Up P j π π1) (h2 : Up P l π2 π1) :
    ∃ π3, Up P l π3 π ∧ Up P j π3 π2 := by
  refine ⟨fun i => if (i : ℕ) + 1 = l then π2 i else π i, fun i => ?_, fun i => ?_⟩
  all_goals
    have a := h1 i
    have b := h2 i
    by_cases hj : (i : ℕ) + 1 = j
    · have hl : (i : ℕ) + 1 ≠ l := fun h => hjl (hj.symm.trans h)
      simp only [if_pos hj, if_neg hl] at a b ⊢; omega
    · by_cases hl : (i : ℕ) + 1 = l
      · simp only [if_neg hj, if_pos hl] at a b ⊢; omega
      · simp only [if_neg hj, if_neg hl] at a b ⊢; omega

theorem up_mixed2 (P : Par) (l j : ℕ) (hjl : j ≠ l) (π π2 π3 : Ty P) (h1 : Up P l π3 π) (h2 : Up P j π3 π2) :
    ∃ π1, Up P j π π1 ∧ Up P l π2 π1 := by
  refine ⟨fun i => if (i : ℕ) + 1 = j then π2 i else π i, fun i => ?_, fun i => ?_⟩
  all_goals
    have a := h1 i
    have b := h2 i
    by_cases hj : (i : ℕ) + 1 = j
    · have hl : (i : ℕ) + 1 ≠ l := fun h => hjl (hj.symm.trans h)
      simp only [if_pos hj, if_neg hl] at a b ⊢; omega
    · by_cases hl : (i : ℕ) + 1 = l
      · simp only [if_neg hj, if_pos hl] at a b ⊢; omega
      · simp only [if_neg hj, if_neg hl] at a b ⊢; omega

theorem nrm_shift (P : Par) (l j : ℕ) (hl : l ∈ Icc 1 (P.k - 1)) (hj : j ∈ Icc 1 (P.k - 1)) (hjl : j ≠ l)
    (π πj : Ty P) (hU : Up P j π πj) (hp : rho P π j - rho P π l + 1 ≠ 0) (hm : rho P π j - rho P π l - 1 ≠ 0) :
    Nrm P l πj * (rho P π j - rho P π l + 1) = Nrm P l π * (rho P π j - rho P π l - 1) := by
  have hr := rhoUp P j π πj hU
  have hrl : rho P πj l = rho P π l := by rw [hr l hl, if_neg hjl.symm, add_zero]
  have hrj : rho P πj j = rho P π j + 1 := by rw [hr j hj, if_pos rfl]
  have hjm : j ∈ (Icc 1 (P.k - 1)).erase l := Finset.mem_erase.2 ⟨hjl, hj⟩
  have hother : ∀ i ∈ ((Icc 1 (P.k - 1)).erase l).erase j, rho P πj i = rho P π i := by
    intro i hi
    have h1 := Finset.mem_erase.1 hi
    rw [hr i (Finset.mem_of_mem_erase h1.2), if_neg h1.1, add_zero]
  have p1 : ∏ i ∈ (Icc 1 (P.k - 1)).erase l, (rho P πj i - rho P πj l) =
      (rho P π j - rho P π l + 1) * ∏ i ∈ ((Icc 1 (P.k - 1)).erase l).erase j, (rho P π i - rho P π l) := by
    rw [← Finset.mul_prod_erase _ _ hjm, hrj, hrl]
    congr 1
    · ring
    · exact Finset.prod_congr rfl (fun i hi => by rw [hother i hi])
  have p2 : ∏ i ∈ (Icc 1 (P.k - 1)).erase l, (rho P πj i - rho P πj l - 1) =
      (rho P π j - rho P π l) * ∏ i ∈ ((Icc 1 (P.k - 1)).erase l).erase j, (rho P π i - rho P π l - 1) := by
    rw [← Finset.mul_prod_erase _ _ hjm, hrj, hrl]
    congr 1
    · ring
    · exact Finset.prod_congr rfl (fun i hi => by rw [hother i hi])
  have p3 : ∏ i ∈ (Icc 1 (P.k - 1)).erase l, (rho P π i - rho P π l) =
      (rho P π j - rho P π l) * ∏ i ∈ ((Icc 1 (P.k - 1)).erase l).erase j, (rho P π i - rho P π l) :=
    (Finset.mul_prod_erase _ _ hjm).symm
  have p4 : ∏ i ∈ (Icc 1 (P.k - 1)).erase l, (rho P π i - rho P π l - 1) =
      (rho P π j - rho P π l - 1) * ∏ i ∈ ((Icc 1 (P.k - 1)).erase l).erase j, (rho P π i - rho P π l - 1) :=
    (Finset.mul_prod_erase _ _ hjm).symm
  have g : ∀ Q A B d : ℝ, d + 1 ≠ 0 → d - 1 ≠ 0 →
      Q / (((d + 1) * A) * (d * B)) * (d + 1) = Q / ((d * A) * ((d - 1) * B)) * (d - 1) := by
    intro Q A B d hp hm
    have e1 : ((d + 1) * A) * (d * B) = (d + 1) * (A * d * B) := by ring
    have e2 : (d * A) * ((d - 1) * B) = (d - 1) * (A * d * B) := by ring
    rw [e1, e2, div_mul_eq_mul_div, div_mul_eq_mul_div, mul_comm Q (d + 1), mul_comm Q (d - 1),
      mul_div_mul_left _ _ hp, mul_div_mul_left _ _ hm]
  unfold Nrm
  rw [p1, p2, p3, p4, hrl]
  exact g _ _ _ _ hp hm

theorem gap (P : Par) (hP : P.OK) (l j : ℕ) (hl : l ∈ Icc 1 (P.k - 1)) (hj : j ∈ Icc 1 (P.k - 1)) (hjl : j ≠ l)
    (π πl πj : Ty P) (h1 : Up P l π πl) (h2 : Up P j π πj) :
    2 ≤ rho P π j - rho P π l ∨ rho P π j - rho P π l ≤ -2 := by
  have hI := tyInterlaces P hP π
  rcases Nat.lt_or_gt_of_ne hjl with h | h
  · left
    have o := (ord P.k P.u P.u' (rho P π) hI l hl).2.2.1 j hj h
    have b := tyInterlaces P hP πl l hl
    have e := rhoUp P l π πl h1 l hl
    rw [if_pos rfl] at e
    rw [e] at b
    linarith [o.1, b.1]
  · right
    have hIj := tyInterlaces P hP πj
    have o := (ord P.k P.u P.u' (rho P πj) hIj l hl).2.2.2 j hj h
    have b := hI l hl
    have e := rhoUp P j π πj h2 j hj
    rw [if_pos rfl] at e
    rw [e] at o
    linarith [o.1, b.2.2.1]

theorem sq_lemma (a b a' b' d : ℝ) (h1 : a * (d - 1) = b' * (d + 1)) (h2 : a' * (d + 1) = b * (d - 1))
    (hd : 2 ≤ d ∨ d ≤ -2) :
    Real.sqrt a * Real.sqrt b * (d - 1) = Real.sqrt a' * Real.sqrt b' * (d + 1) ∧
      Real.sqrt a' * Real.sqrt a = Real.sqrt b' * Real.sqrt b := by
  have hm : d - 1 ≠ 0 := by rcases hd with h | h <;> intro h0 <;> linarith
  obtain ⟨t, htd⟩ : ∃ t, t = (d + 1) / (d - 1) := ⟨_, rfl⟩
  have ht : 0 < t := by
    rw [htd]
    rcases hd with h | h
    · exact div_pos (by linarith) (by linarith)
    · exact div_pos_of_neg_of_neg (by linarith) (by linarith)
  have ht2 : t * (d - 1) = d + 1 := by rw [htd]; exact div_mul_cancel₀ _ hm
  have ea : a = b' * t := by rw [htd, ← mul_div_assoc, eq_div_iff hm]; exact h1
  have eb : b = a' * t := by rw [htd, ← mul_div_assoc, eq_div_iff hm]; exact h2.symm
  have hs : Real.sqrt t * Real.sqrt t = t := Real.mul_self_sqrt ht.le
  rw [ea, eb, Real.sqrt_mul' _ ht.le, Real.sqrt_mul' _ ht.le]
  constructor
  · linear_combination (Real.sqrt a' * Real.sqrt b' * (d - 1)) * hs + (Real.sqrt a' * Real.sqrt b') * ht2
  · ring

theorem corner (P : Par) (hP : P.OK) (l j : ℕ) (hl : l ∈ Icc 1 (P.k - 1)) (hj : j ∈ Icc 1 (P.k - 1)) (hjl : j ≠ l)
    (π πl πj : Ty P) (h1 : Up P l π πl) (h2 : Up P j π πj) :
    Real.sqrt (Nrm P j πl) * Real.sqrt (Nrm P l π) * (rho P π j - rho P π l - 1) =
      Real.sqrt (Nrm P l πj) * Real.sqrt (Nrm P j π) * (rho P π j - rho P π l + 1) ∧
    Real.sqrt (Nrm P l πj) * Real.sqrt (Nrm P j πl) = Real.sqrt (Nrm P j π) * Real.sqrt (Nrm P l π) := by
  have hd := gap P hP l j hl hj hjl π πl πj h1 h2
  have hp : rho P π j - rho P π l + 1 ≠ 0 := by rcases hd with h | h <;> intro h0 <;> linarith
  have hm : rho P π j - rho P π l - 1 ≠ 0 := by rcases hd with h | h <;> intro h0 <;> linarith
  have hp' : rho P π l - rho P π j + 1 ≠ 0 := by rcases hd with h | h <;> intro h0 <;> linarith
  have hm' : rho P π l - rho P π j - 1 ≠ 0 := by rcases hd with h | h <;> intro h0 <;> linarith
  have s1 := nrm_shift P l j hl hj hjl π πj h2 hp hm
  have s2 := nrm_shift P j l hj hl hjl.symm π πl h1 hp' hm'
  exact sq_lemma _ _ _ _ _ (by linear_combination (-1) * s2) s1 hd

noncomputable def sR (P : Par) (l : ℕ) : Matrix (Ty P) (Ty P) ℝ :=
  Matrix.of fun π' π => if Up P l π π' then Real.sqrt (Nrm P l π) else 0

noncomputable def ioR (P : Par) : Matrix (Ty P) (Ty P) ℝ →+* A P :=
  ((algebraMap ℂ (Pr P.r)).comp Complex.ofRealHom).mapMatrix

theorem ioR_apply (P : Par) (M : Matrix (Ty P) (Ty P) ℝ) (a b : Ty P) :
    ioR P M a b = algebraMap ℂ (Pr P.r) ((M a b : ℝ) : ℂ) := rfl

theorem kap_eq (P : Par) (f : Ty P → ℂ) :
    kap P f = Matrix.diagonal fun π => algebraMap ℂ (Pr P.r) (f π) := by
  rfl

theorem ioR_sR (P : Par) (l : ℕ) : ioR P (sR P l) = SS P l := by
  ext π' π
  rw [ioR_apply]
  simp only [sR, SS, Matrix.of_apply]
  split_ifs
  · rfl
  · simp

theorem ioR_diag (P : Par) (f : Ty P → ℝ) : ioR P (Matrix.diagonal f) = kap P fun π => ((f π : ℝ) : ℂ) := by
  rw [kap_eq]
  ext a b
  rw [ioR_apply]
  by_cases h : a = b
  · subst h; simp
  · simp [Matrix.diagonal_apply_ne _ h]

theorem ioR_transpose (P : Par) (M : Matrix (Ty P) (Ty P) ℝ) : ioR P M.transpose = star (ioR P M) := by
  ext a b
  rw [Matrix.star_apply, ioR_apply, ioR_apply, Matrix.transpose_apply, ← algebraMap_star_comm]
  simp

theorem sR_pos {P : Par} {l : ℕ} {π π' : Ty P} (h : Up P l π π') : sR P l π' π = Real.sqrt (Nrm P l π) := by
  unfold sR; rw [Matrix.of_apply, if_pos h]

theorem sR_neg {P : Par} {l : ℕ} {π π' : Ty P} (h : ¬ Up P l π π') : sR P l π' π = 0 := by
  unfold sR; rw [Matrix.of_apply, if_neg h]

theorem r_norm (P : Par) (hP : P.OK) (l : ℕ) (hl : l ∈ Icc 1 (P.k - 1)) :
    (sR P l).transpose * sR P l = Matrix.diagonal (Nrm P l) := by
  ext π1 π2
  rw [Matrix.mul_apply]
  simp only [Matrix.transpose_apply]
  by_cases h : π1 = π2
  · subst h
    rw [Matrix.diagonal_apply_eq]
    by_cases hu : ∃ π', Up P l π1 π'
    · obtain ⟨π', hU⟩ := hu
      rw [Finset.sum_eq_single π' (fun b _ hb => by
        rw [sR_neg (fun hb' => hb (up_fun P l π1 b π' hb' hU)), zero_mul])
        (fun h => absurd (Finset.mem_univ _) h), sR_pos hU]
      exact Real.mul_self_sqrt (nrm_pos P hP l hl π1 π' hU).le
    · rw [(nrmFacts P hP l hl π1).2.1 hu]
      apply Finset.sum_eq_zero
      intro b _
      rw [sR_neg (fun hb => hu ⟨b, hb⟩), zero_mul]
  · rw [Matrix.diagonal_apply_ne _ h]
    apply Finset.sum_eq_zero
    intro b _
    by_cases h1 : Up P l π1 b
    · rw [sR_neg (π := π2) (π' := b) (fun h2 => h (up_inj P l b π1 π2 h1 h2)), mul_zero]
    · rw [sR_neg h1, zero_mul]

theorem r_normDown (P : Par) (hP : P.OK) (l : ℕ) (hl : l ∈ Icc 1 (P.k - 1)) :
    sR P l * (sR P l).transpose = Matrix.diagonal (NrmDown P l) := by
  ext π1 π2
  rw [Matrix.mul_apply]
  simp only [Matrix.transpose_apply]
  by_cases h : π1 = π2
  · subst h
    rw [Matrix.diagonal_apply_eq]
    by_cases hu : ∃ π', Up P l π' π1
    · obtain ⟨π', hU⟩ := hu
      rw [Finset.sum_eq_single π' (fun b _ hb => by
        rw [sR_neg (fun hb' => hb (up_inj P l π1 b π' hb' hU)), zero_mul])
        (fun h => absurd (Finset.mem_univ _) h), sR_pos hU, nrm_down P l hl π' π1 hU]
      exact Real.mul_self_sqrt (nrm_pos P hP l hl π' π1 hU).le
    · rw [(nrmFacts P hP l hl π1).2.2 hu]
      apply Finset.sum_eq_zero
      intro b _
      rw [sR_neg (fun hb => hu ⟨b, hb⟩), zero_mul]
  · rw [Matrix.diagonal_apply_ne _ h]
    apply Finset.sum_eq_zero
    intro b _
    by_cases h1 : Up P l b π1
    · rw [sR_neg (π := b) (π' := π2) (fun h2 => h (up_fun P l b π1 π2 h1 h2)), mul_zero]
    · rw [sR_neg h1, zero_mul]

theorem prod_one (P : Par) (l j : ℕ) (π π1 π2 : Ty P) (h1 : Up P l π π1) (h2 : Up P j π1 π2) :
    (sR P j * sR P l) π2 π = Real.sqrt (Nrm P j π1) * Real.sqrt (Nrm P l π) := by
  rw [Matrix.mul_apply, Finset.sum_eq_single π1 (fun b _ hb => by
    rw [sR_neg (l := l) (π := π) (π' := b) (fun hb' => hb (up_fun P l π b π1 hb' h1)), mul_zero])
    (fun h => absurd (Finset.mem_univ _) h), sR_pos h1, sR_pos h2]

theorem prod_zero {P : Par} {l j : ℕ} {π π2 : Ty P} (h : ¬ ∃ π1, Up P l π π1 ∧ Up P j π1 π2) :
    (sR P j * sR P l) π2 π = 0 := by
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro b _
  by_cases h1 : Up P l π b
  · rw [sR_neg (l := j) (π := b) (π' := π2) (fun h2 => h ⟨b, h1, h2⟩), zero_mul]
  · rw [sR_neg h1, mul_zero]

theorem r_comm (P : Par) (hP : P.OK) (l j : ℕ) (hl : l ∈ Icc 1 (P.k - 1)) (hj : j ∈ Icc 1 (P.k - 1)) (hjl : j ≠ l) :
    sR P j * sR P l * Matrix.diagonal (fun π => rho P π j - rho P π l - 1) =
      sR P l * sR P j * Matrix.diagonal (fun π => rho P π j - rho P π l + 1) := by
  ext π2 π
  rw [Matrix.mul_diagonal, Matrix.mul_diagonal]
  by_cases h : ∃ π1, Up P l π π1 ∧ Up P j π1 π2
  · obtain ⟨π1, h1, h2⟩ := h
    obtain ⟨π3, h3, h4⟩ := up_square P l j hjl π π1 π2 h1 h2
    rw [prod_one P l j π π1 π2 h1 h2, prod_one P j l π π3 π2 h3 h4]
    exact (corner P hP l j hl hj hjl π π1 π3 h1 h3).1
  · have h' : ¬ ∃ π3, Up P j π π3 ∧ Up P l π3 π2 :=
      fun ⟨π3, h3, h4⟩ => h (up_square P j l hjl.symm π π3 π2 h3 h4)
    rw [prod_zero h, prod_zero h', zero_mul, zero_mul]

theorem r_mixed (P : Par) (hP : P.OK) (l j : ℕ) (hl : l ∈ Icc 1 (P.k - 1)) (hj : j ∈ Icc 1 (P.k - 1)) (hjl : j ≠ l) :
    (sR P l).transpose * sR P j = sR P j * (sR P l).transpose := by
  ext π2 π
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp only [Matrix.transpose_apply]
  by_cases h : ∃ π1, Up P j π π1 ∧ Up P l π2 π1
  · obtain ⟨π1, h1, h2⟩ := h
    obtain ⟨π3, h3, h4⟩ := up_mixed1 P l j hjl π π1 π2 h1 h2
    have L : ∑ b, sR P l b π2 * sR P j b π = sR P l π1 π2 * sR P j π1 π :=
      Finset.sum_eq_single π1 (fun b _ hb => by
        rw [sR_neg (l := j) (π := π) (π' := b) (fun hb' => hb (up_fun P j π b π1 hb' h1)), mul_zero])
        (fun h => absurd (Finset.mem_univ _) h)
    have R : ∑ b, sR P j π2 b * sR P l π b = sR P j π2 π3 * sR P l π π3 :=
      Finset.sum_eq_single π3 (fun b _ hb => by
        rw [sR_neg (l := l) (π := b) (π' := π) (fun hb' => hb (up_inj P l π b π3 hb' h3)), mul_zero])
        (fun h => absurd (Finset.mem_univ _) h)
    rw [L, R, sR_pos h1, sR_pos h2, sR_pos h3, sR_pos h4]
    exact (corner P hP l j hl hj hjl π3 π π2 h3 h4).2
  · have L : ∑ b, sR P l b π2 * sR P j b π = 0 := by
      apply Finset.sum_eq_zero
      intro b _
      by_cases h1 : Up P j π b
      · rw [sR_neg (l := l) (π := π2) (π' := b) (fun h2 => h ⟨b, h1, h2⟩), zero_mul]
      · rw [sR_neg h1, mul_zero]
    have R : ∑ b, sR P j π2 b * sR P l π b = 0 := by
      apply Finset.sum_eq_zero
      intro b _
      by_cases h1 : Up P l b π
      · rw [sR_neg (l := j) (π := b) (π' := π2) (fun h2 => h (up_mixed2 P l j hjl π π2 b h1 h2)), zero_mul]
      · rw [sR_neg h1, mul_zero]
    rw [L, R]

theorem aC_up (P : Par) (l : ℕ) (hl : l ∈ Icc 1 (P.k - 1)) (π π' : Ty P) (hU : Up P l π π') :
    aC P π' = aC P π - 1 := by
  unfold aC
  have : ∑ i ∈ Icc 1 (P.k - 1), rho P π' i = ∑ i ∈ Icc 1 (P.k - 1), rho P π i + 1 := by
    rw [Finset.sum_congr rfl (rhoUp P l π π' hU), Finset.sum_add_distrib, Finset.sum_ite_eq', if_pos hl]
  rw [this]; ring

theorem nab_step (a : ℝ) (D W : Pr r) (c : ℂ) :
    (D + ((a - 1 : ℝ) : ℂ) • W) * algebraMap ℂ (Pr r) c =
      algebraMap ℂ (Pr r) c * (D + (a : ℂ) • W) - W * algebraMap ℂ (Pr r) c := by
  rw [Algebra.commutes c (D + (a : ℂ) • W), ← sub_mul]
  congr 1
  push_cast
  rw [sub_smul, one_smul]
  abel

end Formalism.FourierDecayAlt.P.Mx4

namespace Formalism.FourierDecayAlt.P

open Mx4

theorem shift_scalar_relation : Formalism.FourierDecayAlt.M.SSScalar := by
  intro P l w
  show SS P l * sc P w = sc P w * SS P l
  ext π' π
  simp only [sc, Matrix.scalar_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, SS, Matrix.of_apply]
  split_ifs
  · exact (Algebra.commutes _ _)
  · simp

theorem shift_shift_relation : Formalism.FourierDecayAlt.M.SSShift := by
  intro P l f g h
  rw [kap_eq, kap_eq]
  ext π' π
  rw [Matrix.diagonal_mul, Matrix.mul_diagonal]
  by_cases hu : Up P l π π'
  · simp only [SS, Matrix.of_apply, if_pos hu, h π π' hu]
    exact (Algebra.commutes _ _)
  · simp [SS, hu]

theorem shift_norm_relation : Formalism.FourierDecayAlt.M.SSNorm := by
  intro P hP l hl
  constructor
  · rw [← ioR_sR P l, ← ioR_transpose, ← map_mul, r_norm P hP l hl, ioR_diag]
  · rw [← ioR_sR P l, ← ioR_transpose, ← map_mul, r_normDown P hP l hl, ioR_diag]

theorem shift_commute_relation : Formalism.FourierDecayAlt.M.SSComm := by
  intro P hP l hl j hj hjl
  have e1 : (kap P fun π => ((rho P π j - rho P π l - 1 : ℝ) : ℂ)) =
      ioR P (Matrix.diagonal fun π => rho P π j - rho P π l - 1) := (ioR_diag P _).symm
  have e2 : (kap P fun π => ((rho P π j - rho P π l + 1 : ℝ) : ℂ)) =
      ioR P (Matrix.diagonal fun π => rho P π j - rho P π l + 1) := (ioR_diag P _).symm
  rw [e1, e2, ← ioR_sR P l, ← ioR_sR P j]
  simp only [← map_mul]
  rw [r_comm P hP l j hl hj hjl]

theorem shift_mixed_relation : Formalism.FourierDecayAlt.M.SSMixed := by
  intro P hP l hl j hj hjl
  rw [← ioR_sR P l, ← ioR_sR P j, ← ioR_transpose]
  simp only [← map_mul]
  rw [r_mixed P hP l j hl hj hjl]

theorem nabla_shift_relation : Formalism.FourierDecayAlt.M.NabSS := by
  intro P l hl
  constructor
  · ext π' π
    simp only [nabA, zbA, ggiA, sc, Matrix.scalar_apply, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul,
      Matrix.mul_diagonal, Matrix.sub_apply]
    by_cases hU : Up P l π π'
    · simp only [SS, Matrix.of_apply, if_pos hU]
      rw [aC_up P l hl π π' hU]
      exact nab_step _ _ _ _
    · simp only [SS, Matrix.of_apply, if_neg hU, mul_zero, zero_mul, sub_zero]
  · ext π' π
    simp only [nabsA, zA, ggiA, sc, Matrix.scalar_apply, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul,
      Matrix.mul_diagonal, Matrix.sub_apply]
    by_cases hU : Up P l π π'
    · simp only [SS, Matrix.of_apply, if_pos hU]
      rw [aC_up P l hl π π' hU]
      exact nab_step _ _ _ _
    · simp only [SS, Matrix.of_apply, if_neg hU, mul_zero, zero_mul, sub_zero]

theorem m_curvature_proof : Formalism.FourierDecayAlt.M.Curvature := by
  intro P
  rw [kap_eq]
  simp only [nabA, nabsA, ggiA, sc, Matrix.scalar_apply, Matrix.diagonal_mul_diagonal, Matrix.diagonal_sub]
  congr 1
  funext π
  exact curv _ _

end Formalism.FourierDecayAlt.P
