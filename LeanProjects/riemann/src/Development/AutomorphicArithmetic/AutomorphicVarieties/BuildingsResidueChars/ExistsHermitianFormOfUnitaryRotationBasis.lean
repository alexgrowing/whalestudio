import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.HodgeTateFromSandwich
open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob Matrix

namespace UpperTheory.V.Z.Sym.Glob

variable {K : Type} [Field K] {Δ τ : K}

private def hh (x y : Fin 3 → Lsq K Δ) : Lsq K Δ := ∑ i, x i * star (y i)

private theorem hh_star (x y : Fin 3 → Lsq K Δ) : star (hh x y) = hh y x := by
  simp only [hh, star_sum, star_mul', star_star]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

private theorem hh_unitary {N : Matrix (Fin 3) (Fin 3) (Lsq K Δ)} (hN : N ∈ Matrix.unitaryGroup (Fin 3) (Lsq K Δ))
    (x y : Fin 3 → Lsq K Δ) : hh (N *ᵥ x) (N *ᵥ y) = hh x y := by
  change (N *ᵥ x) ⬝ᵥ star (N *ᵥ y) = x ⬝ᵥ star y
  rw [Matrix.star_mulVec, dotProduct_comm, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, ← Matrix.star_eq_conjTranspose,
    (Matrix.mem_unitaryGroup_iff').1 hN, Matrix.one_mulVec, dotProduct_comm]

private theorem hh_right (x y z : Fin 3 → Lsq K Δ) (r : Lsq K Δ) :
    hh x (r • y - z) = star r * hh x y - hh x z := by
  simp only [hh, Fin.sum_univ_three, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, star_sub, star_mul']
  ring

private theorem hh_left (x y z : Fin 3 → Lsq K Δ) (r : Lsq K Δ) :
    hh (r • y - z) x = r * hh y x - hh z x := by
  simp only [hh, Fin.sum_univ_three, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

private theorem hh_expand (e v w : Fin 3 → Lsq K Δ) (x0 p q y0 r s : Lsq K Δ) :
    hh (x0 • e + p • v + q • w) (y0 • e + r • v + s • w) =
      x0 * star y0 * hh e e + x0 * star r * hh e v + x0 * star s * hh e w +
      p * star y0 * hh v e + p * star r * hh v v + p * star s * hh v w +
      q * star y0 * hh w e + q * star r * hh w v + q * star s * hh w w := by
  simp only [hh, Fin.sum_univ_three, Pi.add_apply, Pi.smul_apply, smul_eq_mul, star_add, star_mul']
  ring

private theorem trace_form (m x y : EL Δ τ) :
    QuadraticAlgebra.trace (m * x * star (sigL y)) =
      x.re * star y.re * (2 * m.re + algebraMap K (Lsq K Δ) τ * m.im) +
      x.re * star y.im * (algebraMap K (Lsq K Δ) τ * (2 * m.re + algebraMap K (Lsq K Δ) τ * m.im)
        - (algebraMap K (Lsq K Δ) τ * m.re + (algebraMap K (Lsq K Δ) τ ^ 2 - 2) * m.im)) +
      x.im * star y.re * (algebraMap K (Lsq K Δ) τ * m.re + (algebraMap K (Lsq K Δ) τ ^ 2 - 2) * m.im) +
      x.im * star y.im * (2 * m.re + algebraMap K (Lsq K Δ) τ * m.im) := by
  simp only [QuadraticAlgebra.trace_def, QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul,
    QuadraticAlgebra.re_star, QuadraticAlgebra.im_star, sigL]
  ring

private theorem gram_unit {M : Matrix (Fin 3) (Fin 3) (Lsq K Δ)} (h : IsUnit M.det) :
    IsUnit (M * Mᴴ).det := by
  rw [Matrix.det_mul, Matrix.det_conjTranspose]
  exact h.mul (h.star)

end UpperTheory.V.Z.Sym.Glob

theorem UpperTheory.exists_hermitian_form_of_unitary_rotation_basis :
    ∀ (K : Type) [Field K] [CharZero K] (Δ τ : K), τ ^ 2 - 4 ≠ 0 → ∀ N : Matrix (Fin 3) (Fin 3) (Lsq K Δ), N ∈ Matrix.unitaryGroup (Fin 3) (Lsq K Δ) →
        ∀ e v : Fin 3 → Lsq K Δ, N *ᵥ e = e → N *ᵥ (N *ᵥ v) = algebraMap K (Lsq K Δ) τ • (N *ᵥ v) - v →
        IsUnit (Matrix.of ![e, v, N *ᵥ v]).det →
        ∃ (c : Kˣ) (m : EL Δ τ), IsUnit m ∧ star (sigL m) = m ∧ ∀ x y : Sp Δ τ,
          herm (c : K) m x y = ∑ i, (x.1 • e + x.2.re • v + x.2.im • (N *ᵥ v)) i * star ((y.1 • e + y.2.re • v + y.2.im • (N *ᵥ v)) i) := by
  intro K _ _ Δ τ hτ N hN e v hNe hNv hdet
  obtain ⟨w, hw⟩ : ∃ w, w = N *ᵥ v := ⟨_, rfl⟩
  rw [← hw] at hNv hdet ⊢
  obtain ⟨t, ht⟩ : ∃ t, t = algebraMap K (Lsq K Δ) τ := ⟨_, rfl⟩
  have hst : star t = t := by
    rw [ht]; ext <;> simp
  obtain ⟨u, hu⟩ : ∃ u, u = algebraMap K (Lsq K Δ) (τ ^ 2 - 4)⁻¹ := ⟨_, rfl⟩
  have hsu : star u = u := by
    rw [hu]; ext <;> simp
  have hut : u * (t ^ 2 - 4) = 1 := by
    have : algebraMap K (Lsq K Δ) ((τ ^ 2 - 4)⁻¹ * (τ ^ 2 - 4)) = 1 := by
      rw [inv_mul_cancel₀ hτ, map_one]
    rw [map_mul, map_sub, map_pow, map_ofNat] at this
    rw [hu, ht]; exact this
  have h2t : IsUnit (2 - t) := by
    refine IsUnit.of_mul_eq_one (-(2 + t) * u) ?_
    linear_combination hut

  have hvw : hh e v = hh e w := by
    conv_lhs => rw [← hh_unitary hN e v, hNe, ← hw]
  have hew0 : hh e w = hh e (t • w - v) := by
    conv_lhs => rw [← hh_unitary hN e w, hNe, hNv, ← ht]
  rw [hh_right, hst] at hew0
  have hew : hh e w = 0 := by
    have : (2 - t) * hh e w = 0 := by linear_combination hew0 - hvw
    exact (h2t.mul_right_eq_zero).1 this
  have hev : hh e v = 0 := hvw.trans hew
  have hwe : hh w e = 0 := by rw [← hh_star, hew, star_zero]
  have hve : hh v e = 0 := by rw [← hh_star, hev, star_zero]
  have hww : hh w w = hh v v := by rw [hw, hh_unitary hN]
  have hsa : star (hh v v) = hh v v := hh_star _ _
  have hsc : star (hh e e) = hh e e := hh_star _ _
  have hb : hh w v = t * hh w w - hh v w := by
    have h := hh_unitary hN w v
    rw [← hw, hNv, ← ht, hh_left] at h
    exact h.symm

  have hG : IsUnit (hh e e * (hh v v * hh v v - hh v w * hh w v)) := by
    have h := gram_unit hdet
    have e1 : (Matrix.of ![e, v, w] * (Matrix.of ![e, v, w])ᴴ) =
        !![hh e e, hh e v, hh e w; hh v e, hh v v, hh v w; hh w e, hh w v, hh w w] := by
      refine Matrix.ext fun i j => ?_
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply, hh, Fin.sum_univ_three, Matrix.conjTranspose_apply]
    rw [e1, Matrix.det_fin_three] at h
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
      Matrix.cons_val_fin_one, hev, hew, hve, hwe, hww] at h
    convert h using 1
    ring
  have hc : IsUnit (hh e e) := isUnit_of_mul_isUnit_left hG
  have hq : IsUnit (hh v v * hh v v - hh v w * hh w v) := isUnit_of_mul_isUnit_right hG

  have him : (hh e e).im = 0 := by
    have h := congrArg QuadraticAlgebra.im hsc
    rw [QuadraticAlgebra.im_star] at h
    have h2 : (2 : K) * (hh e e).im = 0 := by linear_combination -h
    simpa using h2
  have hce : hh e e = algebraMap K (Lsq K Δ) (hh e e).re := by
    ext <;> simp [him]
  have hc0 : (hh e e).re ≠ 0 := by
    intro h0
    rw [hce, h0, map_zero] at hc
    exact not_isUnit_zero hc
  obtain ⟨a, ha⟩ : ∃ a, a = hh v v := ⟨_, rfl⟩
  obtain ⟨b, hb'⟩ : ∃ b, b = hh w v := ⟨_, rfl⟩
  have hvw' : hh v w = t * a - b := by
    rw [hww, ← ha, ← hb'] at hb
    linear_combination hb
  have hsb : star b = t * a - b := by
    rw [hb', hh_star, ← hb', hvw']
  have hsa' : star a = a := by rw [ha, hsa]
  obtain ⟨m, hm⟩ : ∃ m : EL Δ τ, m = ⟨u * ((t ^ 2 - 2) * a - t * b), u * (2 * b - t * a)⟩ := by
    rw [ht]; exact ⟨_, rfl⟩
  subst ht
  have hm0 : m.re = u * (((algebraMap K (Lsq K Δ) τ) ^ 2 - 2) * a - algebraMap K (Lsq K Δ) τ * b) := by rw [hm]
  have hm1 : m.im = u * (2 * b - algebraMap K (Lsq K Δ) τ * a) := by rw [hm]
  have hT0 : 2 * m.re + algebraMap K (Lsq K Δ) τ * m.im = a := by
    rw [hm0, hm1]; linear_combination a * hut
  have hT1 : algebraMap K (Lsq K Δ) τ * m.re + ((algebraMap K (Lsq K Δ) τ) ^ 2 - 2) * m.im = b := by
    rw [hm0, hm1]; linear_combination b * hut
  have hs0 : star m.re = u * (algebraMap K (Lsq K Δ) τ * b - 2 * a) := by
    rw [hm0]
    simp only [star_mul', star_sub, star_pow, hsu, hst, hsa', hsb, star_ofNat]
    ring
  have hs1 : star m.im = u * (algebraMap K (Lsq K Δ) τ * a - 2 * b) := by
    rw [hm1]
    simp only [star_mul', star_sub, hsu, hst, hsa', hsb, star_ofNat]
    ring
  refine ⟨Units.mk0 _ hc0, m, ?_, ?_, ?_⟩
  · rw [QuadraticAlgebra.isUnit_iff_norm_isUnit]
    have hn : (4 - (algebraMap K (Lsq K Δ) τ) ^ 2) * QuadraticAlgebra.norm m = a * a - (algebraMap K (Lsq K Δ) τ * a - b) * b := by
      rw [QuadraticAlgebra.norm_def, hm0, hm1]
      linear_combination (u * ((algebraMap K (Lsq K Δ) τ) ^ 2 - 4) + 1) * (a * a - (algebraMap K (Lsq K Δ) τ * a - b) * b) * hut
    rw [hvw', ← hb', ← ha] at hq
    rw [← hn] at hq
    exact isUnit_of_mul_isUnit_right hq
  · refine QuadraticAlgebra.ext ?_ ?_
    · rw [QuadraticAlgebra.re_star]
      change star m.re + algebraMap K (Lsq K Δ) τ * star m.im = m.re
      rw [hs0, hs1, hm0]
      ring
    · rw [QuadraticAlgebra.im_star]
      change -star m.im = m.im
      rw [hs1, hm1]
      ring
  · intro x y
    change herm _ m x y = hh _ _
    rw [hh_expand, herm, trace_form, hT0, hT1, hev, hew, hve, hwe, hww, hvw', ← ha, ← hb', Units.val_mk0, ← hce]
    ring
