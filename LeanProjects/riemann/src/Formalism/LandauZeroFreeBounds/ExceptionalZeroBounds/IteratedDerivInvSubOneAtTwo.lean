import Formalism.LandauZeroFreeBounds.SameCharacterLFunctionOne

open Complex
open scoped ComplexOrder Nat

noncomputable section

namespace Formalism.ZeroFreeDirichlet

lemma iteratedDeriv_inv_sub_one_at_two (m : ℕ) :
    iteratedDeriv m (fun s : ℂ => (s - 1)⁻¹) 2 = (-1) ^ m * (m ! : ℂ) := by
  have h : (fun s : ℂ => (s - 1)⁻¹) = fun x => (1 * x - 1)⁻¹ := by simp
  rw [iteratedDeriv_eq_iterate, h, iter_deriv_inv_linear_sub]
  norm_num

lemma iteratedDeriv_lseries_at_two {a : ℕ → ℂ} {G : ℂ → ℂ} {lam : ℂ} (hG : Differentiable ℂ G)
    (hFG : ∀ s : ℂ, 1 < s.re → LSeries a s = G s + lam * (s - 1)⁻¹) (m : ℕ) :
    iteratedDeriv m (LSeries a) 2 = iteratedDeriv m G 2 + lam * ((-1) ^ m * (m ! : ℂ)) := by
  have hU : {s : ℂ | 1 < s.re} ∈ nhds (2 : ℂ) :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
  have hev : LSeries a =ᶠ[nhds (2 : ℂ)] fun s => G s + lam * (s - 1)⁻¹ := by
    filter_upwards [hU] with s hs using hFG s hs
  have hinv : ContDiffAt ℂ m (fun s : ℂ => lam * (s - 1)⁻¹) 2 :=
    contDiffAt_const.mul ((contDiffAt_id.sub contDiffAt_const).inv (by norm_num))
  rw [(hev.iteratedDeriv m).eq_of_nhds, iteratedDeriv_fun_add hG.contDiff.contDiffAt hinv,
    iteratedDeriv_const_mul_field, iteratedDeriv_inv_sub_one_at_two]

end Formalism.ZeroFreeDirichlet
