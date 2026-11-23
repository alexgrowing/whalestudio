import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
import Formalism.FrobeniusOrbits.RealSubfieldLeCompositum

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH

namespace Formalism.L2.Theta

theorem sigmaOf_sqrtMinusD (D : D7) (g : D.R.GG) (hg : g ∈ D.R.Psi) :
    D.host.sigmaOf g D.host.sqrtMinusD = D.host.sqrtMinusD := by
  have hpsi : g.1.2 = 1 := by
    have h := hg
    simp only [Formalism.HC.Frame.Psi, Formalism.HC.Frame.chD, MonoidHom.mem_ker, MonoidHom.coe_comp,
      Function.comp_apply, MonoidHom.coe_fst, MonoidHom.coe_snd] at h
    exact h
  unfold Formalism.BasicNotions.Host.sigmaOf Formalism.BasicNotions.Host.sqrtMinusD
  rw [D.host.gal_sqd, MulEquiv.apply_symm_apply, hpsi]
  simp

theorem tauE_sqrtMinusD (D : D7) (τ : D.what₂.Tau) :
    tauE D τ D.host.sqrtMinusD = Complex.I * (Real.sqrt D.host.d : ℂ) := by
  have h1 := sigmaOf_sqrtMinusD D (D.eTau τ).1 (D.eTau τ).2
  show D.host.φ₀ ((D.host.sigmaOf (D.eTau τ).1) D.host.sqrtMinusD) = _
  rw [h1]
  exact D.host.φ₀_mem

theorem xi_zero_im_pos (D : D7) (τ : D.what₂.Tau) : 0 < (tauE D τ D.host.xi0).im := by
  have hN : (Ideal.absNorm D.host.ccK : ℝ) ≠ 0 := by
    rw [Nat.cast_ne_zero, Ne, Ideal.absNorm_eq_zero_iff]; exact D.host.ccK_ne_bot
  have hNpos : (0 : ℝ) < Ideal.absNorm D.host.ccK := lt_of_le_of_ne (Nat.cast_nonneg _) (Ne.symm hN)
  have hd : (0 : ℝ) < Real.sqrt D.host.d := Real.sqrt_pos.mpr (by exact_mod_cast D.host.hyp.2.1.pos)
  have hc0 := mul_pos hNpos hd
  unfold Formalism.BasicNotions.Host.xi0
  rw [map_div₀, map_neg, map_one, map_mul, map_natCast, tauE_sqrtMinusD]
  have hc : ((Ideal.absNorm D.host.ccK : ℕ) : ℂ) * (Complex.I * (Real.sqrt D.host.d : ℂ)) =
      Complex.I * (((Ideal.absNorm D.host.ccK : ℝ) * Real.sqrt D.host.d : ℝ) : ℂ) := by
    push_cast; ring
  rw [hc, div_mul_eq_div_div, Complex.div_I, Complex.div_ofReal_im, neg_mul, one_mul, neg_neg,
    Complex.I_im]
  exact div_pos one_pos hc0

end Formalism.L2.Theta

end
