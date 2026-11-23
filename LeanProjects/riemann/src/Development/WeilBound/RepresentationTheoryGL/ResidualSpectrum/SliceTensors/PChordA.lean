import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PExpTwA

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin

namespace PositivityTheory.Rg.Rs.ChordArithmetic

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E]

theorem mulChi_absC_cancel (a : ℕ) (z : ℂ) (ψ : Sm E a) :
    mulChi a (Model.absC E z) (mulChi a (Model.absC E (-z)) ψ) = ψ := by
  refine Subtype.ext (funext fun m => ?_)
  rw [mulChi_apply, mulChi_apply, ExponentTwist.chiDet_absC_val, ExponentTwist.chiDet_absC_val, mul_assoc, ← Complex.exp_add]
  simp

theorem central_twist {a : ℕ} (w e : ℂ) (h : e + w * a * (Module.finrank ℚ E : ℂ) = 0) (ψ : Sm E a)
    (hψ : ∀ (t : ℝ) m, ψ.1 (splitCentre E a t * m) = Complex.exp (e * t) * ψ.1 m) :
    ∀ (t : ℝ) m, (mulChi a (Model.absC E w) ψ).1 (splitCentre E a t * m) = (mulChi a (Model.absC E w) ψ).1 m := by
  intro t m
  rw [mulChi_apply, mulChi_apply, map_mul, Units.val_mul, hψ, ExponentTwist.splitCentre_eq, ExponentTwist.chiDet_aT le_rfl]
  have e1 : Complex.exp (e * t) * Complex.exp (w * a * (Module.finrank ℚ E : ℂ) * t) = 1 := by
    rw [← Complex.exp_add, ← Complex.exp_zero]
    congr 1
    linear_combination (t : ℂ) * h
  linear_combination (ψ.1 m * ((chiDet a (Model.absC E w) m : ℂˣ) : ℂ)) * e1

theorem left_eq (c c₁ : ℂ) (r r₁ d : ℕ) (hr : r ≠ 0) (hd : d ≠ 0) :
    (c₁ - -(c / (r * d)) * r₁ * d).re = c₁.re + (r₁ : ℝ) / r * c.re := by
  have hr' : (r : ℂ) ≠ 0 := by exact_mod_cast hr
  have hd' : (d : ℂ) ≠ 0 := by exact_mod_cast hd
  have e : c₁ - -(c / (r * d)) * r₁ * d = c₁ + (((r₁ : ℝ) / r : ℝ) : ℂ) * c := by
    push_cast
    field_simp
    ring
  rw [e, Complex.add_re, Complex.re_ofReal_mul]

theorem right_eq (c c₂ : ℂ) (s r₂ d : ℕ) (hs : s ≠ 0) (hd : d ≠ 0) :
    (c + (c₂ - -(-c / (s * d)) * r₂ * d)).re = c₂.re + ((s : ℝ) - r₂) / s * c.re := by
  have hs' : (s : ℂ) ≠ 0 := by exact_mod_cast hs
  have hd' : (d : ℂ) ≠ 0 := by exact_mod_cast hd
  have e : c + (c₂ - -(-c / (s * d)) * r₂ * d) = c₂ + ((((s : ℝ) - r₂) / s : ℝ) : ℂ) * c := by
    push_cast
    field_simp
    ring
  rw [e, Complex.add_re, Complex.re_ofReal_mul]

theorem left_arith (r s r₁ d lam x y : ℝ) (hr : 0 < r) (h1 : 0 < r₁) (h2 : r₁ < r) (hlam : 0 < lam)
    (hp : y / d - r * (r + s - r) / 2 = -lam * (r * s))
    (hb : (x + r₁ / r * y) / d - r₁ * (r + s - r₁) / 2 ≤ -lam * (r₁ * (r + s - r₁))) :
    x / d - r₁ * (r - r₁) / 2 < 0 := by
  have hY : y / d = r * s / 2 - lam * (r * s) := by linarith
  have e : (x + r₁ / r * y) / d = x / d + r₁ / r * (y / d) := by ring
  have e2 : r₁ / r * (r * s / 2 - lam * (r * s)) = r₁ * s / 2 - lam * (r₁ * s) := by field_simp
  rw [e, hY, e2] at hb
  nlinarith [mul_pos hlam (mul_pos h1 (sub_pos.2 h2))]

theorem right_arith (r s r₂ d lam x y : ℝ) (hs : 0 < s) (h1 : 0 < r₂) (h2 : r₂ < s) (hlam : 0 < lam)
    (hp : y / d - r * (r + s - r) / 2 = -lam * (r * s))
    (hb : (x + (s - r₂) / s * y) / d - (r + r₂) * (r + s - (r + r₂)) / 2 ≤ -lam * ((r + r₂) * (r + s - (r + r₂)))) :
    x / d - r₂ * (s - r₂) / 2 < 0 := by
  have hY : y / d = r * s / 2 - lam * (r * s) := by linarith
  have e : (x + (s - r₂) / s * y) / d = x / d + (s - r₂) / s * (y / d) := by ring
  have e2 : (s - r₂) / s * (r * s / 2 - lam * (r * s)) = r * (s - r₂) / 2 - lam * (r * (s - r₂)) := by
    field_simp
  rw [e, hY, e2] at hb
  nlinarith [mul_pos hlam (mul_pos h1 (sub_pos.2 h2))]

end PositivityTheory.Rg.Rs.ChordArithmetic
