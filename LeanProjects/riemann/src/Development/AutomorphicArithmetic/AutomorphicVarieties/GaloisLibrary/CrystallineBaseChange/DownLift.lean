import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.RnStmt
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.RotEig
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.NslMul
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.MemMirabIff

open NumberField IsDedekindDomain GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Nf UpperTheory.V.Sd
open UpperHalfPlane hiding I

namespace UpperTheory.V.Br.DescentLift

private noncomputable def sc (t : ℝ) : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.mk0 (Real.exp t) (Real.exp_pos t).ne')

private theorem sc_val (t : ℝ) : (sc t).val = !![Real.exp t, 0; 0, Real.exp t] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sc]

private theorem sc_add (s t : ℝ) : sc (s + t) = sc s * sc t := by
  refine Units.ext ?_
  rw [Units.val_mul, sc_val, sc_val, sc_val]
  simp [Real.exp_add]

private theorem sc_zero : sc 0 = 1 := by
  refine Units.ext ?_
  rw [sc_val, Real.exp_zero, Units.val_one, Matrix.one_fin_two]

private theorem sc_inv (φ : TR.Sm ℚ 2) (h : ∀ v, TR.Eop v 0 0 φ + TR.Eop v 1 1 φ = 0) (g : GA ℚ 2) (t : ℝ) :
    φ.1 (g * upR (sc t)) = φ.1 g := by
  classical
  let X : TR.Lie ℚ 2 := TR.toL 1
  have hX : X = TR.toL (Matrix.single 0 0 (Pi.single Rat.infinitePlace 1)) +
      TR.toL (Matrix.single 1 1 (Pi.single Rat.infinitePlace 1)) := by
    ext i j u
    rw [Subsingleton.elim u Rat.infinitePlace]
    fin_cases i <;> fin_cases j <;> simp [X]
  have hL : TR.lie ℚ 2 X φ = 0 := by
    rw [hX, map_add, LinearMap.add_apply, ← h Rat.infinitePlace]
    simp only [TR.Eop]
    congr!
  let c : ℝ → GL (Fin 2) (TR.Rinf ℚ) := fun s => Matrix.GeneralLinearGroup.map (algebraMap ℝ (TR.Rinf ℚ)) (sc s)
  have hcv : ∀ s i j v, (c s).val i j v = (sc s).val i j := fun _ _ _ _ => rfl
  have hc : HasDerivAt (fun s : ℝ => TR.toL (c s).val) X 0 := by
    refine hasDerivAt_pi.2 fun i => hasDerivAt_pi.2 fun j => hasDerivAt_pi.2 fun v => ?_
    have h1 : HasDerivAt Real.exp 1 0 := by simpa using Real.hasDerivAt_exp 0
    show HasDerivAt (fun s => (sc s).val i j) _ 0
    simp only [sc_val]
    fin_cases i <;> fin_cases j
    · simpa [X] using h1
    · simpa [X] using hasDerivAt_const (0 : ℝ) (0 : ℝ)
    · simpa [X] using hasDerivAt_const (0 : ℝ) (0 : ℝ)
    · simpa [X] using h1
  let f : ℝ → ℂ := fun t => φ.1 (g * upR (sc t))
  have hf : ∀ t, HasDerivAt f 0 t := fun t => by
    have h1 := TR.hasDerivAt_curve φ (g * upR (sc t)) c X (by simp only [c, sc_zero, map_one]) hc
    rw [← TR.lie_apply, hL] at h1
    have h2 : HasDerivAt (fun s => f (t + s)) 0 0 := by
      simpa only [f, sc_add, map_mul, mul_assoc] using! h1
    have h3 := HasDerivAt.comp_sub_const t t (f := fun s => f (t + s)) (by rw [sub_self]; exact h2)
    simpa using h3
  have h4 := is_const_of_deriv_eq_zero (fun t => (hf t).differentiableAt) (fun t => (hf t).deriv) t 0
  simpa only [f, sc_zero, map_one, mul_one] using h4

private noncomputable def rot (θ : ℝ) : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![Real.cos θ, Real.sin θ; -Real.sin θ, Real.cos θ] (by
    rw [Matrix.det_fin_two_of]; nlinarith [Real.sin_sq_add_cos_sq θ])

private theorem rot_val (θ : ℝ) : (rot θ).val = !![Real.cos θ, Real.sin θ; -Real.sin θ, Real.cos θ] := rfl

private theorem rot_det (θ : ℝ) : (rot θ).val.det = 1 := by
  rw [rot_val, Matrix.det_fin_two_of]; nlinarith [Real.sin_sq_add_cos_sq θ]

private theorem rot_eig (φ : TR.Sm ℚ 2) (z : ℂ) (h : ∀ v, TR.Eop v 0 1 φ - TR.Eop v 1 0 φ = z • φ) (g : GA ℚ 2) (θ : ℝ) :
    φ.1 (g * upR (rot θ)) = Complex.exp (z * θ) * φ.1 g := by
  have := rotEig ℚ φ z h (fun _ => θ) (Matrix.GeneralLinearGroup.map (algebraMap ℝ (TR.Rinf ℚ)) (rot θ)) (by
    ext i j v
    fin_cases i <;> fin_cases j <;> rfl) g
  simpa using! this

private theorem nsl_rot (k : ℕ) (f : ℍ → ℂ) (θ : ℝ) :
    nsl k f (rot θ).val UpperHalfPlane.I = Complex.exp (Complex.I * k * θ) * f UpperHalfPlane.I := by
  have e : (((rot θ).val 1 0 : ℝ) : ℂ) * (UpperHalfPlane.I : ℍ) + ((rot θ).val 1 1 : ℝ) = Complex.exp (-(θ * Complex.I)) := by
    rw [← neg_mul, Complex.exp_mul_I]
    simp [rot_val]
    ring
  have e' : (((rot θ).val 0 0 : ℝ) : ℂ) * (UpperHalfPlane.I : ℍ) + ((rot θ).val 0 1 : ℝ) =
      Complex.I * Complex.exp (-(θ * Complex.I)) := by
    rw [← neg_mul, Complex.exp_mul_I]
    simp [rot_val]
    linear_combination (Complex.sin θ) * Complex.I_mul_I
  simp only [nsl]
  rw [e, e', rot_det, mul_div_cancel_right₀ _ (Complex.exp_ne_zero _), ← Complex.exp_int_mul]
  have : ofComplex Complex.I = UpperHalfPlane.I := ofComplex_apply UpperHalfPlane.I
  simp only [abs_one, Real.one_rpow, sign_one, SignType.coe_one, Complex.ofReal_one, one_mul, this]
  congr 2
  push_cast
  ring

private theorem nsl_aff (k : ℕ) (φ : GA ℚ 2 → ℂ) (y x : ℝ) (hy : 0 < y) :
    nsl k (down k φ) (aff (Units.mk0 y hy.ne') x).val UpperHalfPlane.I = φ (upR (aff (Units.mk0 y hy.ne') x)) := by
  have hv : (aff (Units.mk0 y hy.ne') x).val = !![y, x; 0, 1] := rfl
  have hd : (!![y, x; 0, 1] : Matrix (Fin 2) (Fin 2) ℝ).det = y := by simp
  let z : ℍ := ⟨⟨x, y⟩, hy⟩
  have hz : down k φ z = ((y ^ (-((k : ℝ) / 2)) : ℝ) : ℂ) * φ (upR (aff (Units.mk0 y hy.ne') x)) := rfl
  have e : (y : ℂ) * Complex.I + x = (z : ℂ) := by
    apply Complex.ext <;> simp [z]
  simp only [nsl]
  rw [hv, hd, abs_of_pos hy, sign_pos hy]
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
    Complex.ofReal_zero, Complex.ofReal_one, zero_mul, zero_add, one_zpow, mul_one, div_one, SignType.coe_one, one_mul, coe_I]
  rw [e, ofComplex_apply, hz, ← mul_assoc, ← Complex.ofReal_mul, ← Real.rpow_add hy]
  simp

private theorem iwasawa (h : GL (Fin 2) ℝ) (hh : 0 < h.val.det) :
    ∃ (y : ℝ) (hy : 0 < y) (x θ t : ℝ), h = aff (Units.mk0 y hy.ne') x * rot θ * sc t := by
  set a := h.val 0 0 with ha
  set b := h.val 0 1 with hb
  set c := h.val 1 0 with hc
  set d := h.val 1 1 with hd
  rw [Matrix.det_fin_two, ← ha, ← hb, ← hc, ← hd] at hh
  let w : ℂ := ⟨d, -c⟩
  have hw : w ≠ 0 := by
    intro h0
    have h1 : d = 0 := congrArg Complex.re h0
    have h2 : -c = 0 := congrArg Complex.im h0
    rw [h1, neg_eq_zero.1 h2] at hh
    simp at hh
  have hr : 0 < ‖w‖ := norm_pos_iff.2 hw
  have h1 : ‖w‖ * Real.cos w.arg = d := Complex.norm_mul_cos_arg w
  have h2 : ‖w‖ * Real.sin w.arg = -c := Complex.norm_mul_sin_arg w
  have h3 : ‖w‖ ^ 2 = c ^ 2 + d ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; simp [w]; ring
  have hn : 0 < c ^ 2 + d ^ 2 := h3 ▸ pow_pos hr 2
  refine ⟨(a * d - b * c) / (c ^ 2 + d ^ 2), div_pos hh hn, (a * c + b * d) / (c ^ 2 + d ^ 2), w.arg, Real.log ‖w‖, Units.ext ?_⟩
  rw [Units.val_mul, Units.val_mul, sc_val, rot_val, Real.exp_log hr]
  change _ = !![(a * d - b * c) / (c ^ 2 + d ^ 2), (a * c + b * d) / (c ^ 2 + d ^ 2); 0, 1] * _ * _
  rw [Matrix.eta_fin_two h.val, ← ha, ← hb, ← hc, ← hd, Matrix.mul_fin_two, Matrix.mul_fin_two]
  congr 1
  refine congrArg₂ (fun p q => ![p, q]) (congrArg₂ (fun p q => ![p, q]) ?_ ?_) (congrArg₂ (fun p q => ![p, q]) ?_ ?_)
  · field_simp
    linear_combination (-(a * d - b * c)) * h1 + (a * c + b * d) * h2
  · field_simp
    linear_combination (-(a * d - b * c)) * h2 - (a * c + b * d) * h1
  · linear_combination h2
  · linear_combination -h1

private theorem pos_case (k : ℕ) (φ : TR.Sm ℚ 2) (hφ : IsLow k φ) (h : GL (Fin 2) ℝ) (hh : 0 < h.val.det) :
    φ.1 (upR h) = nsl k (down k φ.1) h.val UpperHalfPlane.I := by
  obtain ⟨y, hy, x, θ, t, rfl⟩ := iwasawa h hh
  have e : (aff (Units.mk0 y hy.ne') x * rot θ * sc t).val = Real.exp t • ((aff (Units.mk0 y hy.ne') x).val * (rot θ).val) := by
    rw [Units.val_mul, Units.val_mul, sc_val]
    ext i j
    fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, mul_comm]
  rw [e, (nslMul k _).2.2.1 _ _ (Real.exp_pos t),
    ← (nslMul k _).1 _ _ (Matrix.isUnits_det_units _).ne_zero (by rw [rot_det]; exact one_pos), nsl_rot, nsl_aff k _ y x hy,
    map_mul, map_mul, sc_inv φ hφ.one, rot_eig φ _ hφ.wt]

private def epsQ : GL (Fin 2) ℚ := ⟨!![-1, 0; 0, 1], !![-1, 0; 0, 1], by simp [Matrix.one_fin_two], by simp [Matrix.one_fin_two]⟩

private theorem toR_epsQ : (toR epsQ).val = eps := by
  ext i j
  show Rat.castHom ℝ (epsQ.val i j) = _
  fin_cases i <;> fin_cases j <;> simp [epsQ, eps]

private theorem toF_epsQ (N : ℕ) : toF epsQ ∈ K1G N := by
  have h : ∀ a b, (toF epsQ).val a b ∈ Ohat ℚ := fun a b => by
    show algebraMap ℚ (Af ℚ) (epsQ.val a b) ∈ _
    fin_cases a <;> fin_cases b <;> simp [epsQ, one_mem, zero_mem]
  refine (memK N _).2 ⟨h, ?_, ⟨0, zero_mem _, ?_⟩, 0, zero_mem _, ?_⟩
  · rw [← map_inv]
    exact h
  · show algebraMap ℚ (Af ℚ) (epsQ.val 1 0) = _
    simp [epsQ]
  · show algebraMap ℚ (Af ℚ) (epsQ.val 1 1) - 1 = _
    simp [epsQ]

end UpperTheory.V.Br.DescentLift

open UpperTheory.V.Br.DescentLift in
theorem UpperTheory.V.Br.downLift :
    UpperTheory.V.Br.DownLift := by
  intro k N _ φ hr hφ hK γ h u hu
  have hfin : ∀ u ∈ K1G N, ∀ g, φ.1 (g * finGL ℚ 2 u) = φ.1 g := fun u hu g =>
    congrFun (congrArg Subtype.val (hK u hu)) g
  rw [hr, hfin u hu]
  rcases lt_or_gt_of_ne (Matrix.isUnits_det_units h).ne_zero with hd | hd
  · have e : (toR epsQ * h).val = eps * h.val := by rw [Units.val_mul, toR_epsQ]
    have hd' : 0 < (toR epsQ * h).val.det := by
      rw [e, Matrix.det_mul]
      simpa [eps, Matrix.det_fin_two_of] using hd
    rw [← (nslMul k _).2.1, ← e, ← pos_case k φ hφ _ hd', ← hr epsQ (upR h), ratGL_eq, mul_assoc, ← upR_comm, ← mul_assoc,
      hfin _ (toF_epsQ N), map_mul]
  · exact pos_case k φ hφ h hd
