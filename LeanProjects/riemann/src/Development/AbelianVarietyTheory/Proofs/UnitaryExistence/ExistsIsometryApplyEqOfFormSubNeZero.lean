import Mathlib
open MeasureTheory Topology Matrix
open scoped ENNReal

namespace GlobalTheory

section Abstract
variable {V : Type*} [AddCommGroup V] [Module ℂ V]

theorem exists_isometry_apply_eq_of_form_sub_ne_zero (B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ)
    (hB : ∀ x y, B y x = (starRingEnd ℂ) (B x y)) (x₀ v : V) (hv : B v v = B x₀ x₀)
    (hc : B x₀ (x₀ - v) ≠ 0) :
    ∃ u : V →ₗ[ℂ] V, (∀ x y, B (u x) (u y) = B x y) ∧ u x₀ = v := by
  set d := x₀ - v with hd
  set c := B x₀ d with hcdef
  have hdd : B d d = c + (starRingEnd ℂ) c := by
    rw [hcdef, ← hB x₀ d, hd]
    simp only [map_sub, LinearMap.sub_apply, hv]
    ring
  have hc' : (starRingEnd ℂ) c ≠ 0 := by simpa using hc
  refine ⟨LinearMap.id - (c⁻¹ • (B.flip d)).smulRight d, ?_, ?_⟩
  · intro x y
    simp only [LinearMap.sub_apply, LinearMap.id_apply, LinearMap.smulRight_apply,
      LinearMap.smul_apply, LinearMap.flip_apply, map_sub, map_smul, map_smulₛₗ, smul_eq_mul,
      map_mul, map_inv₀, hdd, hB y d, RingHom.id_apply]
    field_simp
    ring
  · simp only [LinearMap.sub_apply, LinearMap.id_apply, LinearMap.smulRight_apply,
      LinearMap.smul_apply, LinearMap.flip_apply, smul_eq_mul, ← hcdef, inv_mul_cancel₀ hc,
      one_smul]
    rw [hd]; abel

theorem form_eq_smul_of_const_on_orbit (A B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ)
    (hA : ∀ x y, A y x = (starRingEnd ℂ) (A x y))
    (hB : ∀ x y, B y x = (starRingEnd ℂ) (B x y)) (x₀ : V) (e : ℂ) (he : e ≠ 0)
    (hnd : ∃ y, B x₀ y ≠ 0)
    (h : ∀ u : V →ₗ[ℂ] V, (∀ x y, B (u x) (u y) = B x y) → A (u x₀) (u x₀) = e) :
    ∃ t : ℝ, t ≠ 0 ∧ ∀ x y, A x y = (t : ℂ) * B x y := by
  have reach : ∀ v, B v v = B x₀ x₀ → B x₀ (x₀ - v) ≠ 0 → A v v = e := by
    intro v hv hc
    obtain ⟨u, hu, hx⟩ := exists_isometry_apply_eq_of_form_sub_ne_zero B hB x₀ v hv hc
    rw [← hx]; exact h u hu
  have hBre : ∀ y, ((B y y).re : ℂ) = B y y := fun y => Complex.conj_eq_iff_re.mp (hB y y).symm
  have hAre : ∀ y, ((A y y).re : ℂ) = A y y := fun y => Complex.conj_eq_iff_re.mp (hA y y).symm
  have h0 : A x₀ x₀ = e := h LinearMap.id (fun _ _ => rfl)
  by_cases ha : B x₀ x₀ = 0
  · exfalso
    obtain ⟨y, hy⟩ := hnd
    have hy' : (starRingEnd ℂ) (B x₀ y) ≠ 0 := by simpa using hy
    set w := y + (-(B y y) / (2 * B x₀ y)) • x₀ with hw
    have hww : B w w = 0 := by
      have h2 : (starRingEnd ℂ) 2 = 2 := map_ofNat _ 2
      simp only [hw, map_add, map_smul, map_smulₛₗ, LinearMap.add_apply, LinearMap.smul_apply,
        smul_eq_mul, ha, hB x₀ y, map_div₀, map_neg, map_mul, ← hB y y, h2, RingHom.id_apply]
      field_simp
      ring
    have hxw : B x₀ w = B x₀ y := by
      simp only [hw, map_add, map_smulₛₗ, ha, smul_eq_mul, mul_zero, add_zero]
    have h1 : A w w = e := reach w (by rw [hww, ha]) (by simpa [ha, hxw] using hy)
    have h2 : A (w + w) (w + w) = e := reach (w + w) (by simp [hww, ha])
      (by
        simp only [map_sub, map_add, ha, hxw]
        intro hh
        apply hy
        linear_combination (-1 / 2 : ℂ) * hh)
    simp only [map_add, LinearMap.add_apply, h1] at h2
    apply he
    linear_combination (1 / 3 : ℂ) * h2
  · have reach2 : ∀ v, B v v = B x₀ x₀ → A v v = e := by
      intro v hv
      by_cases hc : B x₀ (x₀ - v) = 0
      · have := reach (-v) (by simpa using hv) (by
          simp only [map_sub, map_neg] at hc ⊢
          intro hh
          apply ha
          linear_combination (1 / 2 : ℂ) * (hh + hc))
        simpa using this
      · exact reach v hv hc
    set a : ℝ := (B x₀ x₀).re with hadef
    have haC : B x₀ x₀ = (a : ℂ) := (hBre x₀).symm
    have ha0 : a ≠ 0 := by
      intro hh; apply ha; rw [haC, hh]; simp
    have ha0C : (a : ℂ) ≠ 0 := by exact_mod_cast ha0
    have reach3 : ∀ v, 0 < a * (B v v).re → (a : ℂ) * A v v = e * B v v := by
      intro v hv
      have hb : (B v v).re ≠ 0 := by
        intro hh; rw [hh] at hv; simp at hv
      have hq : 0 < a / (B v v).re := by
        have : a / (B v v).re = a * (B v v).re / ((B v v).re) ^ 2 := by field_simp
        rw [this]; positivity
      set s : ℝ := Real.sqrt (a / (B v v).re) with hs
      have hss : s * s * (B v v).re = a := by
        rw [hs, Real.mul_self_sqrt hq.le]; field_simp
      have hssC : (s : ℂ) * s * B v v = a := by
        rw [← hBre v]; exact_mod_cast hss
      have := reach2 ((s : ℂ) • v) (by
        simp only [map_smul, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, Complex.conj_ofReal,
          RingHom.id_apply, haC]
        linear_combination hssC)
      simp only [map_smul, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, Complex.conj_ofReal,
          RingHom.id_apply] at this
      rw [← this, ← hssC]; ring
    have diag : ∀ y, (a : ℂ) * A y y = e * B y y := by
      intro y
      have hcont : Continuous fun t : ℝ => a * (B (x₀ + (t : ℂ) • y) (x₀ + (t : ℂ) • y)).re := by
        simp only [map_add, map_smul, map_smulₛₗ, LinearMap.add_apply, LinearMap.smul_apply,
          smul_eq_mul, Complex.conj_ofReal, RingHom.id_apply]
        fun_prop
      have hpos : 0 < (fun t : ℝ => a * (B (x₀ + (t : ℂ) • y) (x₀ + (t : ℂ) • y)).re) 0 := by
        simp only [Complex.ofReal_zero, zero_smul, add_zero]
        exact mul_self_pos.mpr ha0
      have hev := hcont.continuousAt.eventually (lt_mem_nhds hpos)
      obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp hev
      have h1 := reach3 _ (hball (y := ε / 2) (by
        rw [Real.dist_eq, sub_zero, abs_of_pos (by positivity)]; linarith))
      have h2 := reach3 _ (hball (y := -(ε / 2)) (by
        rw [Real.dist_eq, sub_zero, abs_neg, abs_of_pos (by positivity)]; linarith))
      have hεC : ((ε / 2 : ℝ) : ℂ) ≠ 0 := by
        exact_mod_cast (by positivity : (ε / 2 : ℝ) ≠ 0)
      generalize (ε / 2 : ℝ) = t at h1 h2 hεC
      simp only [map_add, map_smul, map_smulₛₗ, LinearMap.add_apply, LinearMap.smul_apply,
          smul_eq_mul, Complex.conj_ofReal, RingHom.id_apply, h0, haC] at h1 h2
      push_cast at h1 h2
      have : (t : ℂ) ^ 2 * ((a : ℂ) * A y y - e * B y y) = 0 := by
        linear_combination (1 / 2 : ℂ) * (h1 + h2)
      have := (mul_eq_zero.mp this).resolve_left (pow_ne_zero 2 hεC)
      exact sub_eq_zero.mp this
    have heC : e = (e.re : ℂ) := by rw [← h0]; exact (hAre x₀).symm
    have he0 : e.re ≠ 0 := by
      intro hh; apply he; rw [heC, hh]; simp
    refine ⟨e.re / a, div_ne_zero he0 ha0, fun x y => ?_⟩
    have h1 := diag (x + y)
    have h2 := diag (x + Complex.I • y)
    have h3 := diag x
    have h4 := diag y
    simp only [map_add, map_smul, map_smulₛₗ, LinearMap.add_apply, LinearMap.smul_apply,
          smul_eq_mul, Complex.conj_I, RingHom.id_apply] at h1 h2
    push_cast
    rw [← heC]
    field_simp
    have hI := Complex.I_mul_I
    linear_combination (1 / 2 : ℂ) * h1 + (Complex.I / 2) * h2 - (1 / 2 + Complex.I / 2) * h3
      - (1 / 2 + Complex.I / 2) * h4
      + ((1 / 2 : ℂ) * ((a : ℂ) * A x y - e * B x y - ((a : ℂ) * A y x - e * B y x))
        + (Complex.I / 2) * ((a : ℂ) * A y y - e * B y y)) * hI

end Abstract

private noncomputable def matForm {r : ℕ} (M : Matrix (Fin r) (Fin r) ℂ) :
    (Fin r → ℂ) →ₗ[ℂ] (Fin r → ℂ) →ₗ⋆[ℂ] ℂ :=
  LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ) (fun x y => x ⬝ᵥ M *ᵥ star y)
    (fun _ _ _ => add_dotProduct _ _ _)
    (fun _ _ _ => by simp [smul_dotProduct])
    (fun _ _ _ => by rw [star_add, mulVec_add, dotProduct_add])
    (fun _ _ _ => by rw [star_smul, mulVec_smul, dotProduct_smul]; rfl)

private theorem matForm_apply {r : ℕ} (M : Matrix (Fin r) (Fin r) ℂ) (x y : Fin r → ℂ) :
    matForm M x y = ∑ k, ∑ l, x k * M k l * (starRingEnd ℂ) (y l) := by
  simp [matForm, dotProduct, mulVec, Finset.mul_sum, mul_assoc]

private theorem matForm_single {r : ℕ} (M : Matrix (Fin r) (Fin r) ℂ) (i j : Fin r) :
    matForm M (Pi.single i 1) (Pi.single j 1) = M i j := by
  simp [matForm_apply, Pi.single_apply, apply_ite]

private theorem matForm_symm {r : ℕ} {M : Matrix (Fin r) (Fin r) ℂ} (hM : M.IsHermitian)
    (x y : Fin r → ℂ) : matForm M y x = (starRingEnd ℂ) (matForm M x y) := by
  simp only [matForm_apply, map_sum, map_mul, Complex.conj_conj]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  have : (starRingEnd ℂ) (M k l) = M l k := hM.apply l k
  rw [this]; ring

private theorem matForm_conj {r : ℕ} (M : Matrix (Fin r) (Fin r) ℂ)
    (u : (Fin r → ℂ) →ₗ[ℂ] (Fin r → ℂ)) (i j : Fin r) :
    ((LinearMap.toMatrix' u)ᵀ * M * (LinearMap.toMatrix' u).map (starRingEnd ℂ)) i j
      = matForm M (u (Pi.single i 1)) (u (Pi.single j 1)) := by
  simp only [matForm_apply, Matrix.mul_apply, transpose_apply, map_apply,
    LinearMap.toMatrix'_apply, Finset.sum_mul]
  rw [Finset.sum_comm]

theorem hermitian_eq_smul_of_const_on_unitary_orbit :
    ∀ (r : ℕ) (A B : Matrix (Fin r) (Fin r) ℂ) (i : Fin r) (e : ℂ), e ≠ 0 → A.IsHermitian → B.IsHermitian → B.det ≠ 0 → (∀ u : Matrix (Fin r) (Fin r) ℂ, uᵀ * B * u.map (starRingEnd ℂ) = B → (uᵀ * A * u.map (starRingEnd ℂ)) i i = e) → ∃ t : ℝ, t ≠ 0 ∧ A = (t : ℂ) • B := by
  intro r A B i e he hA hB hdet h
  obtain ⟨t, ht, hAB⟩ := form_eq_smul_of_const_on_orbit (matForm A) (matForm B)
    (matForm_symm hA) (matForm_symm hB) (Pi.single i 1) e he
    (by
      by_contra hcon
      push_neg at hcon
      apply hdet
      refine Matrix.det_eq_zero_of_row_eq_zero i fun j => ?_
      rw [← matForm_single B i j, hcon])
    (fun u hu => by
      rw [← matForm_conj]
      apply h
      ext j k
      rw [matForm_conj, hu, matForm_single])
  refine ⟨t, ht, ?_⟩
  ext j k
  rw [← matForm_single A j k, hAB, matForm_single, Matrix.smul_apply, smul_eq_mul]

end GlobalTheory
