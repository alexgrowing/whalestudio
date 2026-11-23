import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GlobalHeightBoundIffAtGoodPrimes
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf

set_option autoImplicit false

noncomputable section

open MvPolynomial Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions.LatticeTransfer

namespace GlobalTheory.ConsNumber

variable (D : D7) (N : ℕ)

def colVar : Vm D.what₂.Tau N → MvPolynomial (Rt D.what₂.Tau N) ℚ
  | Sum.inl (_, x) => X x
  | Sum.inr (_, k) => C ((Nat.factorial k : ℚ)⁻¹) * ∑ τ : D.what₂.Tau, ∑ i : Fin N, (X (τ, i) ^ k + (-X (τ, i)) ^ k)

def collapseQ : MvPolynomial (Vm D.what₂.Tau N) ℚ →ₐ[ℚ] MvPolynomial (Rt D.what₂.Tau N) ℚ := aeval (colVar D N)

theorem isHomogeneous_colVar (v : Vm D.what₂.Tau N) : (colVar D N v).IsHomogeneous (wt D.what₂.Tau N v) := by
  rcases v with ⟨_, x⟩ | ⟨_, k⟩
  · exact isHomogeneous_X ℚ x
  · refine IsHomogeneous.C_mul (IsHomogeneous.sum _ _ _ fun τ _ => IsHomogeneous.sum _ _ _ fun i _ => ?_) _
    have h : (X (τ, i) : MvPolynomial (Rt D.what₂.Tau N) ℚ).IsHomogeneous 1 := isHomogeneous_X ℚ _
    have h1 := h.pow k
    have h2 := h.neg.pow k
    rw [one_mul] at h1 h2
    exact h1.add h2

theorem isHomogeneous_collapseQ {d : ℕ} {G : MvPolynomial (Vm D.what₂.Tau N) ℚ}
    (hG : G.IsWeightedHomogeneous (wt D.what₂.Tau N) d) : (collapseQ D N G).IsHomogeneous d := by
  classical
  rw [G.as_sum, map_sum]
  refine IsHomogeneous.sum _ _ _ fun m hm => ?_
  have hw : Finsupp.weight (wt D.what₂.Tau N) m = d := hG (mem_support_iff.1 hm)
  rw [collapseQ, aeval_monomial, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul, smul_eq_C_mul]
  refine IsHomogeneous.C_mul ?_ _
  rw [Finsupp.prod]
  have h := IsHomogeneous.prod m.support (fun v => colVar D N v ^ m v) (fun v => wt D.what₂.Tau N v * m v)
    fun v _ => (isHomogeneous_colVar D N v).pow (m v)
  convert h using 1
  rw [← hw, Finsupp.weight_apply, Finsupp.sum]
  exact Finset.sum_congr rfl fun v _ => by rw [smul_eq_mul, mul_comm]

theorem toR_collapseQ (G : MvPolynomial (Vm D.what₂.Tau N) ℚ) : toR (collapseQ D N G) = collapse D N (toR G) := by
  have e : (MvPolynomial.map (algebraMap ℚ ℝ)).comp (collapseQ D N).toRingHom =
      (collapse D N).toRingHom.comp (MvPolynomial.map (algebraMap ℚ ℝ)) := by
    refine MvPolynomial.ringHom_ext (fun a => ?_) fun v => ?_
    · simp [collapseQ]
    · rcases v with ⟨_, x⟩ | ⟨_, k⟩
      · simp [collapseQ, colVar, collapse]
      · simp [collapseQ, colVar, collapse, chTot, map_sum]
  exact RingHom.congr_fun e G

end GlobalTheory.ConsNumber

end
