import Formalism.LocalToGlobal.CharacterGerms.BlockMembershipSelfConjCharts
import Formalism.LocalToGlobal.CharacterGerms.RowTieMemCDeg
import Formalism.LocalToGlobal.CharacterGerms.FinTwoNeOneSub

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds.RF

open Formalism.IncomingBounds Formalism.L2.Pj MvPolynomial

section Chain

variable {C : Type} [Field C] {T Orb : Type} [Fintype Orb] {r : T → ℕ} {tau : Orb → ZMod 2 → T}
  {gm : Orb → ZMod 2 → Matrix (Fin 2) (Fin 2) C} {N n : ℕ} (plc : Fin N × Fin 2 ↪ Fin n)

theorem chain_aeval {σ τ : Type} [Fintype σ] (S : MvPolynomial σ C →ₐ[C] MvPolynomial τ C) (ℓ : τ) (p : MvPolynomial σ C) :
    pderiv ℓ (S p) = ∑ y, S (pderiv y p) * pderiv ℓ (S (X y)) := by
  induction p using MvPolynomial.induction_on with
  | C a =>
    simp [MvPolynomial.algHom_C, MvPolynomial.pderiv_C]
  | add p q hp hq =>
    simp only [map_add, hp, hq, add_mul, Finset.sum_add_distrib]
  | mul_X p i hp =>
    have key : ∀ y, S (pderiv y (p * X i)) = (if i = y then S p else 0) + S (X i) * S (pderiv y p) := by
      intro y
      rw [Derivation.leibniz, pderiv_X]
      by_cases h : i = y
      · subst h
        simp
      · simp [Pi.single_apply, h]
    conv_lhs => rw [map_mul S p (X i), Derivation.leibniz, hp]
    simp only [key, smul_eq_mul, add_mul, Finset.sum_add_distrib, ite_mul, zero_mul, Finset.sum_ite_eq,
      Finset.mem_univ, if_true, Finset.mul_sum, mul_assoc]
    try ring

theorem pderiv_subG_off {p : MvPolynomial (Fin N × WVO fun o (_ : Fin 2) => IIs r tau o) C} {ℓ : Letter T r n}
    (h : ∀ z, ℓ ≠ lam r tau plc z) : pderiv ℓ (subG r tau gm plc p) = 0 := by
  rw [chain_aeval]
  refine Finset.sum_eq_zero fun y _ => ?_
  have hX : pderiv ℓ (subG r tau gm plc (X y)) = 0 := by
    unfold subG
    rw [MvPolynomial.aeval_X, map_sum]
    refine Finset.sum_eq_zero fun col _ => ?_
    rw [Derivation.leibniz, MvPolynomial.pderiv_C, smul_zero, add_zero, MvPolynomial.pderiv_X]
    have hne : (⟨tau y.2.1 y.2.2.2.1, y.2.2.2.2, plc (y.1, col)⟩ : Letter T r n) ≠ ℓ := by
      intro heq
      apply h (((eW r tau N) y).1, col)
      rw [← heq]
      rfl
    simp [Pi.single_apply, hne]
  rw [hX, mul_zero]

private theorem lam_injective_of_tau_injective (inj : Function.Injective fun x : Orb × ZMod 2 => tau x.1 x.2)
    (z z' : AA r tau N × Fin 2) (h : lam r tau plc z = lam r tau plc z') : z = z' := by
  obtain ⟨⟨n1, o1, s1, i1⟩, c1⟩ := z
  obtain ⟨⟨n2, o2, s2, i2⟩, c2⟩ := z'
  injection h with h0 h3
  have h1 : tau o1 s1 = tau o2 s2 := h0
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (@inj (o1, s1) (o2, s2) h1)
  have h4 : (i1, plc (n1, c1)) = (i2, plc (n2, c2)) := eq_of_heq h3
  obtain ⟨rfl, h5⟩ := Prod.mk.inj h4
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (plc.injective h5)
  rfl

private theorem pderiv_lam_subG_X_eq_ite (inj : Function.Injective fun x : Orb × ZMod 2 => tau x.1 x.2)
    (α0 : AA r tau N) (col0 : Fin 2) (y : Fin N × WVO fun o (_ : Fin 2) => IIs r tau o) :
    pderiv (lam r tau plc (α0, col0)) (subG r tau gm plc (X y)) =
      if (eW r tau N y).1 = α0 then MvPolynomial.C (gm y.2.1 y.2.2.2.1 col0 y.2.2.1) else 0 := by
  unfold subG
  rw [MvPolynomial.aeval_X, map_sum]
  have key : ∀ col : Fin 2, pderiv (lam r tau plc (α0, col0))
      (MvPolynomial.C (gm y.2.1 y.2.2.2.1 col y.2.2.1) *
        MvPolynomial.X (⟨tau y.2.1 y.2.2.2.1, y.2.2.2.2, plc (y.1, col)⟩ : Letter T r n)) =
      if ((eW r tau N y).1, col) = (α0, col0) then MvPolynomial.C (gm y.2.1 y.2.2.2.1 col y.2.2.1) else 0 := by
    intro col
    rw [Derivation.leibniz, MvPolynomial.pderiv_C, smul_zero, add_zero, MvPolynomial.pderiv_X]
    have e1 : (⟨tau y.2.1 y.2.2.2.1, y.2.2.2.2, plc (y.1, col)⟩ : Letter T r n) =
        lam r tau plc ((eW r tau N y).1, col) := rfl
    rw [e1, Pi.single_apply]
    by_cases hz : ((eW r tau N y).1, col) = (α0, col0)
    · rw [if_pos (congrArg (lam r tau plc) hz), if_pos hz, smul_eq_mul, mul_one]
    · rw [if_neg (fun h' => hz (lam_injective_of_tau_injective plc inj _ _ h')), if_neg hz, smul_zero]
  simp only [key]
  by_cases ha : (eW r tau N y).1 = α0
  · simp [ha]
  · simp [ha]

theorem pderiv_subG_lam (inj : Function.Injective fun x : Orb × ZMod 2 => tau x.1 x.2) (α0 : AA r tau N) (col0 : Fin 2)
    (p : MvPolynomial (Fin N × WVO fun o (_ : Fin 2) => IIs r tau o) C) :
    pderiv (lam r tau plc (α0, col0)) (subG r tau gm plc p) =
      ∑ g, MvPolynomial.C (Gm r tau gm α0 col0 g) * subG r tau gm plc (pderiv ((eW r tau N).symm (α0, g)) p) := by
  rw [chain_aeval, ← (eW r tau N).symm.sum_comp, Fintype.sum_prod_type, Finset.sum_eq_single α0]
  · refine Finset.sum_congr rfl fun g _ => ?_
    rw [pderiv_lam_subG_X_eq_ite plc inj]
    simp only [Equiv.apply_symm_apply]
    first | rw [if_pos rfl] | skip
    exact mul_comm _ _
  · intro α _ hα
    refine Finset.sum_eq_zero fun g _ => ?_
    rw [pderiv_lam_subG_X_eq_ite plc inj]
    simp only [Equiv.apply_symm_apply]
    first | rw [if_neg hα] | simp [hα]
    first | exact mul_zero _ | simp
  · intro h
    exact absurd (Finset.mem_univ _) h

end Chain

end Formalism.L2.FormalSeriesBounds.RF
