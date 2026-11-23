import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.StatementC

open PowerSeries

universe u

noncomputable section

namespace Formalism.L2.Th1.A

namespace ISer

variable {R : Type u} [CommRing R]

def subHom (s : R⟦X⟧) (hs : constantCoeff s = 0) : R⟦X⟧ →ₐ[R] R⟦X⟧ :=
  substAlgHom (HasSubst.of_constantCoeff_zero' hs)

theorem subHom_apply (s : R⟦X⟧) (hs : constantCoeff s = 0) (f : R⟦X⟧) :
    subHom s hs f = f.subst s := by
  unfold subHom
  rw [PowerSeries.coe_substAlgHom]

theorem subHom_X (s : R⟦X⟧) (hs : constantCoeff s = 0) : subHom s hs X = s := by
  rw [subHom_apply, PowerSeries.subst_X (HasSubst.of_constantCoeff_zero' hs)]

theorem subHom_C (s : R⟦X⟧) (hs : constantCoeff s = 0) (a : R) : subHom s hs (C a) = C a := by
  have h := (subHom s hs).commutes a
  simpa using h

theorem eq_wSer_subst (hW : WSerSpec.{u}) (W : WeierstrassCurve R) (s v : R⟦X⟧)
    (hs : constantCoeff s = 0) (hv : constantCoeff v = 0)
    (h : v = s ^ 3 + C W.a₁ * s * v + C W.a₂ * s ^ 2 * v + C W.a₃ * v ^ 2 + C W.a₄ * s * v ^ 2
      + C W.a₆ * v ^ 3) : v = (wSer W).subst s := by
  set w := (wSer W).subst s with hw
  obtain ⟨hfix0, hfix⟩ := (hW R W).1
  have hweq : w = s ^ 3 + C W.a₁ * s * w + C W.a₂ * s ^ 2 * w + C W.a₃ * w ^ 2 + C W.a₄ * s * w ^ 2
      + C W.a₆ * w ^ 3 := by
    have h2 := congrArg (subHom s hs) hfix
    simp only [map_add, map_mul, map_pow, subHom_X, subHom_C] at h2
    rw [subHom_apply] at h2
    exact h2
  have hw0 : constantCoeff w = 0 := by
    obtain ⟨q, hq⟩ := PowerSeries.X_dvd_iff.mpr hfix0
    have h3 : w = s * subHom s hs q := by
      rw [hw, ← subHom_apply s hs, hq, map_mul, subHom_X]
    rw [h3, map_mul, hs, zero_mul]
  set E := C W.a₁ * s + C W.a₂ * s ^ 2 + C W.a₃ * (v + w) + C W.a₄ * s * (v + w)
    + C W.a₆ * (v ^ 2 + v * w + w ^ 2) with hE
  have h4 : v - w = (v - w) * E := by
    rw [hE]
    linear_combination h - hweq
  have hd : (v - w) * (1 - E) = 0 := by linear_combination h4
  have hu : IsUnit (1 - E) := by
    rw [PowerSeries.isUnit_iff_constantCoeff]
    have h5 : constantCoeff E = 0 := by
      rw [hE]
      simp [hs, hv, hw0]
    rw [map_sub, map_one, h5, sub_zero]
    exact isUnit_one
  exact sub_eq_zero.mp ((hu.mul_left_eq_zero).mp hd)

end ISer

open ISer in
theorem iSerSpec_of (hW : WSerSpec.{u}) (hF : WSerFactor.{u}) (hU : UnitSpec.{u})
    (hD : FlowU.{u}) (hN : FlowNegUW.{u}) : ISerSpec.{u} := by
  intro R _ W
  obtain ⟨hw3, -, hUx, -, -⟩ := hF R W
  obtain ⟨-, hfo, -, -, -, hq0, hqr⟩ := hU R W
  obtain ⟨hDer, hConst, hFlow, -, -, hom⟩ := hD R W
  have hw0 : constantCoeff (wSer W) = 0 := (hW R W).1.1
  set r : R⟦X⟧ := invOfUnit (iDen W) (-1) with hr
  have hq : iDen W = -1 + C W.a₁ * X + C W.a₃ * wSer W := rfl
  have hi : iSer W = X * r := rfl
  have hr0 : constantCoeff r = -1 := by
    rw [hr, constantCoeff_invOfUnit]; simp
  have hi0 : constantCoeff (iSer W) = 0 := by rw [hi]; simp
  have hi1 : coeff 1 (iSer W) = -1 := by
    rw [hi, show (1 : ℕ) = 0 + 1 from rfl, coeff_succ_X_mul, coeff_zero_eq_constantCoeff_apply,
      hr0]

  have hneg := hN R⟦X⟧ (curveS W) (D W) X (wSer W) r hDer hConst hFlow
    (by
      have : (-1 + (curveS W).a₁ * X + (curveS W).a₃ * wSer W : R⟦X⟧) = iDen W := rfl
      rw [this, mul_comm]; exact hqr)
  obtain ⟨hE, hDi, -⟩ := hneg
  have hwi : (wSer W).subst (iSer W) = wSer W * r := by
    symm
    apply eq_wSer_subst hW W (iSer W) (wSer W * r) hi0 (by simp [hw0])
    exact hE
  set φ := subHom (iSer W) hi0 with hφ
  have φa : ∀ f, f.subst (iSer W) = φ f := fun f => (subHom_apply _ _ f).symm
  have φX : φ X = X * r := subHom_X _ _
  have φC : ∀ a, φ (C a) = C a := subHom_C _ _
  have φw : φ (wSer W) = wSer W * r := by rw [← φa, hwi]
  have φq : φ (iDen W) = r := by
    rw [hq]
    simp only [map_add, map_mul, map_neg, map_one, φX, φC, φw]
    rw [hq] at hqr
    linear_combination hqr
  have φr : φ r = iDen W := by
    have h1 : φ (iDen W) * φ r = 1 := by rw [← map_mul, hqr, map_one]
    rw [φq] at h1
    linear_combination (iDen W) * h1 - (φ r) * hqr
  have hii : φ (iSer W) = X := by
    rw [hi, map_mul, φX, φr]
    linear_combination X * hqr
  have φU : φ (wU W) = wU W * iDen W ^ 2 := by
    have h1 : φ (wSer W) = φ X ^ 3 * φ (wU W) := by rw [← map_pow, ← map_mul, ← hw3]
    rw [φw, φX] at h1
    have h2 : X ^ 3 * (wU W * r) = X ^ 3 * (r ^ 3 * φ (wU W)) := by
      linear_combination h1 - r * hw3
    have h3 := X_pow_mul_cancel h2
    linear_combination (-(iDen W) ^ 3) * h3
      + (wU W * iDen W ^ 2 - φ (wU W) * ((iDen W * r) ^ 2 + iDen W * r + 1)) * hqr
  have φx : φ (xS W) = r ^ 2 * xS W := by
    have h1 : φ (wU W) * φ (xS W) = 1 := by rw [← map_mul, hUx, map_one]
    rw [φU] at h1
    linear_combination (r ^ 2 * xS W) * h1 - φ (xS W) * (iDen W * r) ^ 2 * hUx
      - φ (xS W) * (iDen W * r + 1) * hqr
  have φfw : φ (fw W) = fwAt (curveS W) (X * r) (wSer W * r) := by
    have : fwAt (curveS W) (X * r) (wSer W * r) = 1 - C W.a₁ * (X * r) - C W.a₂ * (X * r) ^ 2
      - 2 * C W.a₃ * (wSer W * r) - 2 * C W.a₄ * (X * r) * (wSer W * r)
      - 3 * C W.a₆ * (wSer W * r) ^ 2 := rfl
    rw [this, fw]
    simp only [map_sub, map_mul, map_pow, map_one, map_ofNat, φX, φC, φw]
  have hDi' : D W (iSer W) = -φ (fw W) := by
    rw [φfw, ← hDi, hi, neg_neg]
  refine ⟨hi0, hi1, ?_, hwi, ?_, ?_, ?_, ?_⟩
  · rw [φa, hii]
  · rw [φa, φx]
  · rw [φa, yS, map_neg, φx]
    rw [hq] at hqr
    linear_combination (r ^ 2 * xS W) * hqr - r ^ 3 * C W.a₃ * xS W * hw3
      - r ^ 3 * C W.a₃ * X ^ 3 * hUx
  · rw [φa, hDi']
  · rw [φa, ← hom, hDi']
    have h1 : φ (fw W) * φ (om W) = 1 := by rw [← map_mul, hfo, map_one]
    linear_combination (-om W) * h1

end Formalism.L2.Th1.A
