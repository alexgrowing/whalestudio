import Mathlib
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ReciprocityTheory.ChartRestriction.G

noncomputable section

namespace ReadsMul

variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}

theorem mConeMap_of_homog {Ω : Type} [Field Ω] (y : Coord n → Ω) {g : MvPolynomial (Coord n) ℤ}
    {d : ι → ℕ} (hg : IsWeightedHomogeneous (coordDeg n) g d) :
    Geo.mConeMap (ι := blockIdx n) y g = C (aeval y g) * ∏ k, (X k : MvPolynomial ι Ω) ^ d k := by
  have hg' := (geoMultiHomog_iff g d).mpr hg
  conv_lhs => rw [g.as_sum]
  conv_rhs => rw [g.as_sum]
  rw [map_sum, map_sum, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hX : ∏ p : Coord n, (X p.1 : MvPolynomial ι Ω) ^ m p = ∏ k, (X k : MvPolynomial ι Ω) ^ d k := by
    rw [Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun k _ => ?_
    show ∏ i, (X k : MvPolynomial ι Ω) ^ m ⟨k, i⟩ = _
    rw [Finset.prod_pow_eq_pow_sum, hg' m hm k]
  simp only [Geo.mConeMap, aeval_monomial]
  rw [Finsupp.prod_fintype _ _ (fun i => by simp), Finsupp.prod_fintype _ _ (fun i => by simp)]
  simp only [mul_pow, Finset.prod_mul_distrib, hX, map_mul, map_prod, map_pow,
    MvPolynomial.algebraMap_apply]
  ring

theorem mem_mCoordIdeal {Ω : Type} [Field Ω] (y : Coord n → Ω) {g : MvPolynomial (Coord n) ℤ}
    {d : ι → ℕ} (hg : IsWeightedHomogeneous (coordDeg n) g d) (h0 : aeval y g = 0) :
    g ∈ Geo.mCoordIdeal (ι := blockIdx n) y := by
  rw [Geo.mCoordIdeal, RingHom.mem_ker, mConeMap_of_homog y hg, h0, map_zero, zero_mul]

theorem proof : ReadsMul.Statement := by
  intro ι _ _ n Ω _ y P a b s s' t t' hP ⟨f, q, δf, δq, hf, hq, hfq, hqP, ht⟩ _ hR hR'
  subst ht
  have hqy : aeval y q ≠ 0 := fun h0 ↦ hqP (hP ▸ mem_mCoordIdeal y hq h0)
  have hqF : P.mkF q ≠ 0 := fun h0 ↦ hqP ((P.mkF_eq_zero_iff q).mp h0)
  have hfy : aeval y f = s * aeval y q :=
    (hR f q δf δq hf hq (fun k ↦ by have := hfq k; omega)).mpr (div_mul_cancel₀ _ hqF).symm
  intro g h δg δh hg hh hd
  have key := hR' (g * q) (f * h) (δg + δq) (δf + δh) (hg.mul hq) (hf.mul hh) (fun k ↦ by
    have h1 := hfq k
    have h2 := hd k
    simp only [Pi.add_apply, Nat.cast_add] at h1 h2 ⊢
    omega)
  rw [map_mul, map_mul, map_mul, map_mul] at key
  have e1 : (aeval y g = s * s' * aeval y h) ↔
      (aeval y g * aeval y q = s' * (aeval y f * aeval y h)) := by
    rw [← mul_left_inj' hqy, hfy, show s * s' * aeval y h * aeval y q =
      s' * (s * aeval y q * aeval y h) by ring]
  have e2 : (P.mkF g = P.mkF f / P.mkF q * t' * P.mkF h) ↔
      (P.mkF g * P.mkF q = t' * (P.mkF f * P.mkF h)) := by
    rw [← mul_left_inj' hqF, show P.mkF f / P.mkF q * t' * P.mkF h * P.mkF q =
      t' * (P.mkF f * P.mkF h) by field_simp]
  exact e1.trans (key.trans e2.symm)

end ReadsMul

end

end GroundTheory.Heights₂.Heights
