import Mathlib
import Formalism.LocalToGlobal.KernelLattices.MuProd
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.PenultimateKernelDiamondInvariant

open NumberField IsDedekindDomain

noncomputable section

namespace Formalism.L2.Ker

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col

section Det

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}

theorem mh_det_norm (γ : UF E n) : ((LinearEquiv.det γ.1 : Eˣ) : E) * star ((LinearEquiv.det γ.1 : Eˣ) : E) = 1 := by
  have e : ∀ i k, LinearMap.toMatrix' γ.1.toLinearMap k i = γ.1 (Pi.single i 1) k := by
    intro i k
    rw [LinearMap.toMatrix'_apply]
    rfl
  have h : (LinearMap.toMatrix' γ.1.toLinearMap).conjTranspose * LinearMap.toMatrix' γ.1.toLinearMap = 1 := by
    ext i j
    have h1 : hStd E n (γ.1 (Pi.single i 1)) (γ.1 (Pi.single j 1)) = hStd E n (Pi.single i 1) (Pi.single j 1) := γ.2 _ _
    have h2 : ∀ x y : Sp E n, hStd E n x y = ∑ k, star (x k) * y k := fun _ _ => rfl
    rw [h2, h2] at h1
    rw [Matrix.mul_apply]
    simp only [Matrix.conjTranspose_apply, e]
    rw [h1, Matrix.one_apply]
    by_cases hij : i = j
    · subst hij
      simp [Pi.single_apply]
    · simp [Pi.single_apply, hij, Ne.symm hij]
  have hd := congrArg Matrix.det h
  rw [Matrix.det_mul, Matrix.det_conjTranspose, Matrix.det_one, LinearMap.det_toMatrix'] at hd
  rw [LinearEquiv.coe_det, mul_comm]
  exact hd

end Det

section H90

theorem mh_exists_ne (X : Fields) (hX : X.Ok) : ∃ a : X.E, star a ≠ a := by
  by_contra hc
  push Not at hc
  have := hX.cplxE
  let w : InfinitePlace X.E := Classical.arbitrary _
  have hw : w.IsComplex := IsTotallyComplex.isComplex w
  rw [InfinitePlace.isComplex_iff] at hw
  apply hw
  rw [ComplexEmbedding.isReal_iff]
  ext x
  rw [ComplexEmbedding.conjugate_coe_eq, ← hX.conjE, hc]

theorem hilbert_ninety_norm_one (X : Fields) (hX : X.Ok) (z : X.E) (hz : z * star z = 1) : ∃ x : X.Eˣ, z = (x : X.E) / star (x : X.E) := by
  by_cases h : z = -1
  · obtain ⟨a, ha⟩ := mh_exists_ne X hX
    have h0 : a - star a ≠ 0 := fun h0 => ha (sub_eq_zero.1 h0).symm
    refine ⟨Units.mk0 (a - star a) h0, ?_⟩
    rw [Units.val_mk0, star_sub, star_star, h, ← neg_sub a (star a), div_neg, div_self h0]
  · have h0 : 1 + z ≠ 0 := fun h0 => h (by linear_combination h0)
    have h1 : star (1 + z) ≠ 0 := fun h1 => h0 (star_eq_zero.1 h1)
    refine ⟨Units.mk0 (1 + z) h0, ?_⟩
    rw [Units.val_mk0, eq_div_iff h1, star_add, star_one, mul_add, mul_one, hz, add_comm]

end H90

section Bridge

variable {E : Type} [Field E] [NumberField E] {P : HeightOneSpectrum (𝓞 E)}

theorem mh_val_unit {u : E} (h : IsUnit (redP P u)) : P.valuation E u = 1 := by
  haveI := P.isMaximal
  letI := Ideal.Quotient.field P.asIdeal
  unfold redP at h
  split_ifs at h with hex
  · obtain ⟨r', s', hs', hrs', hmk⟩ := hex.choose_spec
    have hc0 : hex.choose ≠ 0 := h.ne_zero
    have hr' : r' ∉ P.asIdeal := by
      intro hr
      apply hc0
      have h6 : Ideal.Quotient.mk P.asIdeal s' * hex.choose = 0 := by
        rw [hmk]
        exact Ideal.Quotient.eq_zero_iff_mem.mpr hr
      rcases mul_eq_zero.mp h6 with h' | h'
      · exact absurd (Ideal.Quotient.eq_zero_iff_mem.mp h') hs'
      · exact h'
    have hs1 : P.valuation E (algebraMap (𝓞 E) E s') = 1 := (le_antisymm (P.valuation_le_one s') (not_lt.mp (fun h => hs' ((P.valuation_lt_one_iff_mem s').mp h))))
    have hr1 : P.valuation E (algebraMap (𝓞 E) E r') = 1 := (le_antisymm (P.valuation_le_one r') (not_lt.mp (fun h => hr' ((P.valuation_lt_one_iff_mem r').mp h))))
    have h5 := congrArg (P.valuation E) hrs'
    rw [map_mul, hs1, one_mul, hr1] at h5
    exact h5
  · exact absurd h not_isUnit_zero

theorem mh_val_lt {w : E} (hI : IntAt P w) (h0 : redP P w = 0) : P.valuation E w < 1 := by
  haveI := P.isMaximal
  letI := Ideal.Quotient.field P.asIdeal
  have hex : ∃ c : 𝓞 E ⧸ P.asIdeal, ∃ r s : 𝓞 E, s ∉ P.asIdeal ∧ algebraMap (𝓞 E) E s * w = algebraMap (𝓞 E) E r ∧
      Ideal.Quotient.mk P.asIdeal s * c = Ideal.Quotient.mk P.asIdeal r := by
    obtain ⟨r, s, hs, hrs⟩ := hI
    have hs0 : Ideal.Quotient.mk P.asIdeal s ≠ 0 := fun h => hs (Ideal.Quotient.eq_zero_iff_mem.mp h)
    refine ⟨Ideal.Quotient.mk P.asIdeal r * (Ideal.Quotient.mk P.asIdeal s)⁻¹, r, s, hs, hrs, ?_⟩
    rw [mul_comm, mul_assoc, inv_mul_cancel₀ hs0, mul_one]
  unfold redP at h0
  rw [dif_pos hex] at h0
  obtain ⟨r', s', hs', hrs', hmk⟩ := hex.choose_spec
  rw [h0, mul_zero] at hmk
  have hr' : r' ∈ P.asIdeal := Ideal.Quotient.eq_zero_iff_mem.mp hmk.symm
  have hs1 : P.valuation E (algebraMap (𝓞 E) E s') = 1 := (le_antisymm (P.valuation_le_one s') (not_lt.mp (fun h => hs' ((P.valuation_lt_one_iff_mem s').mp h))))
  have h5 := congrArg (P.valuation E) hrs'
  rw [map_mul, hs1, one_mul] at h5
  rw [h5]
  exact (P.valuation_lt_one_iff_mem r').mpr hr'

theorem mh_val_mem {b : 𝓞 E} : P.valuation E (b : E) < 1 ↔ b ∈ P.asIdeal := P.valuation_lt_one_iff_mem b

theorem mh_val_pow {b : 𝓞 E} (k : ℕ) : P.valuation E (b : E) ≤ WithZero.exp (-(k : ℤ)) ↔ b ∈ P.asIdeal ^ k := by
  rw [show (b : E) = algebraMap (𝓞 E) E b from rfl, HeightOneSpectrum.valuation_of_algebraMap,
    HeightOneSpectrum.intValuation_le_pow_iff_mem]

theorem mh_val_sq {b : 𝓞 E} (h : b ∈ P.asIdeal ^ 2) : P.valuation E (b : E) ≤ WithZero.exp (-2 : ℤ) := by
  have h2 := (mh_val_pow (P := P) 2).mpr h
  simpa using h2

theorem mh_val_unif {b : 𝓞 E} (h1 : b ∈ P.asIdeal) (h2 : b ∉ P.asIdeal ^ 2) : P.valuation E (b : E) = WithZero.exp (-1 : ℤ) := by
  have hb0 : (b : E) ≠ 0 := by
    intro h0
    apply h2
    rw [NumberField.RingOfIntegers.coe_eq_zero_iff.mp h0]
    exact Submodule.zero_mem _
  have hv0 : P.valuation E (b : E) ≠ 0 := (Valuation.ne_zero_iff _).mpr hb0
  have hle1 : P.valuation E (b : E) ≤ WithZero.exp (-((1 : ℕ) : ℤ)) := (mh_val_pow 1).mpr (by simpa using h1)
  have hnle2 : ¬ P.valuation E (b : E) ≤ WithZero.exp (-((2 : ℕ) : ℤ)) := fun h => h2 ((mh_val_pow 2).mp h)
  obtain ⟨m, hm⟩ : ∃ m : ℤ, P.valuation E (b : E) = WithZero.exp m :=
    ⟨WithZero.log _, (WithZero.exp_log hv0).symm⟩
  rw [hm] at hle1 hnle2 ⊢
  rw [WithZero.exp_le_exp] at hle1 hnle2
  congr 1
  push_cast at hle1 hnle2
  omega

theorem mh_ordE_unif {a : E} {n : ℤ} (h : P.valuation E a = WithZero.exp (-n)) : ordE P a = n := by
  unfold ordE
  rw [h, WithZero.log_exp, neg_neg]

end Bridge

end Formalism.L2.Ker
