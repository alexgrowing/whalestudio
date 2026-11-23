import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.TorusMatchPf

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open NumberField ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Complex ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped ComplexConjugate

section Inv

attribute [local instance] Classical.propDecidable

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ}
  {U : Unf Xo c σ r} (hU : IsUnf U) (hσ : GoodEmb c σ) {k : U.Comp} {x : (U.X k).dom}
  (W : UnfAt U k x) (A : ReciprocityTheory.ChartRestriction.G.I2.TorusAt (U.X k) x.1)

theorem e_ne_zero (τ : (U.X k).Ψ) (b : Fin r) : A.e τ b ≠ 0 := by
  intro h0
  have := A.e_orth τ b b
  rw [if_pos rfl, h0] at this
  simp only [hermC, Pi.zero_apply, zero_mul, Finset.sum_const_zero] at this
  unfold sgn at this
  split_ifs at this <;> norm_num at this

theorem yf_ne_zero (hx : (U.X k).IsOrtho x.1) (τ : (U.X k).Ψ) (b : Fin r) : yf A τ b ≠ 0 := by
  intro h0
  have := e_mul A hx (fun τ => (x.2 τ).1) τ b
  change A.e τ b = yf A τ b • col (mat x.1 τ) b at this
  rw [h0, zero_smul] at this
  exact e_ne_zero A τ b this

theorem c_pos (τ : (U.X k).Ψ) : 0 < (U.X k).c τ := by
  unfold Data.c
  have : τ.1 (U.X k).ξ0 ≠ 0 := (map_ne_zero τ.1).mpr (U.X k).ξ0_ne
  have := norm_pos_iff.mpr this
  linarith

theorem wt_ne_zero (hx : (U.X k).IsOrtho x.1) (i : ReciprocityTheory.ChartRestriction.G.I2.Idx A.T.dim) : wt hU A i ≠ 0 := by
  unfold wt
  split_ifs with h
  · refine mul_ne_zero ?_ ?_
    · exact_mod_cast (Real.sqrt_pos.mpr (c_pos _)).ne'
    · rw [map_ne_zero]
      exact yf_ne_zero A hx _ _
  · refine mul_ne_zero ?_ (yf_ne_zero A hx _ _)
    exact_mod_cast (Real.sqrt_pos.mpr (c_pos _)).ne'

include hU hσ in

def Linv : ReciprocityTheory.ChartRestriction.G.I2.Vsp A.T.dim →ₗ[ℂ] (Fin W.g → ℂ) where
  toFun v := fun j => v ((letT hU hσ W A).symm j) / wt hU A ((letT hU hσ W A).symm j)
  map_add' v w := by
    funext j
    simp only [PiLp.add_apply, Pi.add_apply, add_div]
  map_smul' a v := by
    funext j
    simp only [PiLp.smul_apply, smul_eq_mul, Pi.smul_apply, RingHom.id_apply, mul_div_assoc]

theorem Linv_Lmap (hx : (U.X k).IsOrtho x.1) (z : Fin W.g → ℂ) : Linv hU hσ W A (Lmap hU hσ W A z) = z := by
  funext j
  show Lmap hU hσ W A z ((letT hU hσ W A).symm j) / wt hU A ((letT hU hσ W A).symm j) = z j
  rw [Lmap_apply, Equiv.apply_symm_apply, mul_div_cancel_left₀ _ (wt_ne_zero hU A hx _)]

theorem Lmap_Linv (hx : (U.X k).IsOrtho x.1) (v : ReciprocityTheory.ChartRestriction.G.I2.Vsp A.T.dim) :
    Lmap hU hσ W A (Linv hU hσ W A v) = v := by
  ext i
  rw [Lmap_apply]
  show wt hU A i * (v ((letT hU hσ W A).symm (letT hU hσ W A i)) / wt hU A ((letT hU hσ W A).symm (letT hU hσ W A i))) = v i
  rw [Equiv.symm_apply_apply, mul_div_cancel₀ _ (wt_ne_zero hU A hx _)]

end Inv

end ReciprocityTheory.ChartRestriction.G.PullbackSections
