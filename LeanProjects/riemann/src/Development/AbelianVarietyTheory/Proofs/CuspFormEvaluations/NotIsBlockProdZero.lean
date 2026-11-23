import Mathlib
import Development.AbelianVarietyTheory.Definitions.ThetaValues.IsBlockProd

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.BlockThInhab
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.BlockTh

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (Dw : Datum H) (n : ℕ)

def lead (τ : E →+* ℂ) (i : ℕ) (hi : i ≤ Dw.mult τ) (hn : i ≤ n) (c : ℕ) (hc : 1 ≤ c) : Bk Dw n :=
  ⟨τ, i, hi, c, hc, Fin.castLE hn, Fin.castLE_injective hn⟩

theorem poly_ne_zero (K : Type) [Field K] (B : Bk Dw n) : B.poly K ≠ 0 := by
  classical
  unfold Bk.poly
  refine pow_ne_zero _ ?_
  intro h
  let v : LtN Dw n → K := fun l => if ∃ a : Fin B.i, l = ⟨B.τ, Fin.castLE B.hi a, B.col a⟩ then 1 else 0
  have h2 := congrArg (MvPolynomial.eval v) h
  rw [RingHom.map_det, map_zero] at h2
  have : (MvPolynomial.eval v).mapMatrix (Matrix.of fun a b : Fin B.i => MvPolynomial.X (⟨B.τ, Fin.castLE B.hi a, B.col b⟩ : LtN Dw n)) = 1 := by
    ext a b
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, MvPolynomial.eval_X, v, Matrix.one_apply]
    by_cases hab : a = b
    · subst hab; rw [if_pos ⟨a, rfl⟩, if_pos rfl]
    · rw [if_neg hab, if_neg]
      rintro ⟨d, hd⟩
      simp only [Sigma.mk.injEq, heq_eq_eq, true_and, Prod.mk.injEq] at hd
      have h1 : a = d := Fin.castLE_injective _ hd.1
      have h3 : b = d := B.col_inj hd.2
      exact hab (h1.trans h3.symm)
  rw [this, Matrix.det_one] at h2
  exact one_ne_zero h2

theorem not_isBlockProd_zero (K : Type) [Field K] : ¬ IsBlockProd (0 : MvPolynomial (LtN Dw n) K) := by
  rintro ⟨nb, bs, -, h⟩
  exact Finset.prod_ne_zero_iff.2 (fun j _ => poly_ne_zero Dw n K (bs j)) h.symm

end GlobalTheory.BlockThInhab
