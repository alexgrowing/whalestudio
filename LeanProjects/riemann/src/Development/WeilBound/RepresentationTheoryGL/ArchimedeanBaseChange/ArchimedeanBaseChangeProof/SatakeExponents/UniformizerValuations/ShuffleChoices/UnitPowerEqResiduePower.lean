import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.Choice

noncomputable section

open NumberField IsDedekindDomain Matrix Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcB.One PositivityTheory.Rg.BcB.F.F5
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F.RS PositivityTheory.Rg.BcN.F2 PositivityTheory.Rg.BcB.F.Tail
open scoped Classical TensorProduct
set_option synthInstance.maxHeartbeats 200000

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.BcB.F.Choice

theorem qh_ne_zero' {E : Type} [Field E] [NumberField E] (w : Pl E) : qh w ≠ 0 := by
  unfold qh
  have hq : qV E w ≠ 0 := by
    unfold qV
    exact (Ideal.absNorm_eq_zero_iff).not.2 w.ne_bot
  have hpos : (0 : ℝ) < (qV E w : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hq
  exact Complex.ofReal_ne_zero.2 (Real.sqrt_ne_zero'.2 hpos)

theorem unit_power_eq_residue_power {E : Type} [Field E] [NumberField E] (w : Pl E) (k : ℤ) :
    qU w k = Units.mk0 (qh w) (qh_ne_zero' w) ^ k := by
  unfold qU
  rw [dif_pos (qh_ne_zero' w)]

theorem zpow_finsum' {ι : Type} (u : ℂˣ) (s : Finset ι) (f : ι → ℤ) :
    u ^ (∑ i ∈ s, f i) = ∏ i ∈ s, u ^ f i := by
  refine Finset.induction_on s ?_ ?_
  · simp
  · intro a t ha ih
    rw [Finset.sum_insert ha, Finset.prod_insert ha, _root_.zpow_add, ih]

theorem dl_mul_pw {E : Type} [Field E] [NumberField E] (w : Pl E) {m : ℕ} (ξ : Fin m → ℂˣ) (y : Fin m → ℤ) :
    dl w y * pw ξ y = ((∏ i, (ξ i * qU w ((m : ℤ) - 1 - 2 * (i : ℕ))) ^ y i : ℂˣ) : ℂ) := by
  have hU : ∀ k, qU w k = Units.mk0 (qh w) (qh_ne_zero' w) ^ k := unit_power_eq_residue_power w
  have hdl : dl w y = ((Units.mk0 (qh w) (qh_ne_zero' w) ^
      (∑ i : Fin m, ((m : ℤ) - 1 - 2 * ((i : ℕ) : ℤ)) * y i) : ℂˣ) : ℂ) := by
    rw [Units.val_zpow_eq_zpow_val]
    rfl
  have hpw : pw ξ y = ((∏ i, ξ i ^ y i : ℂˣ) : ℂ) := by
    unfold pw
    rw [Units.coe_prod]
  rw [hdl, hpw, ← Units.val_mul]
  congr 1
  simp only [hU, mul_zpow, Finset.prod_mul_distrib, ← _root_.zpow_mul]
  rw [← zpow_finsum', mul_comm]

theorem chiEval : ChiEval := by
  intro E _ _ _ n w s ξa ξb x
  unfold ev2
  rw [dl_mul_pw, dl_mul_pw, ← Units.val_mul, ← Units.val_mul]
  congr 1
  unfold chiOf
  simp only [mul_zpow, Finset.prod_mul_distrib]
  congr 1
  have h := Equiv.prod_comp s.e (fun k => (Sum.elim (fun i : Fin s.a => ξa i * qU w ((s.a : ℤ) - 1 - 2 * ((i : ℕ) : ℤ)))
    (fun j : Fin s.b => ξb j * qU w ((s.b : ℤ) - 1 - 2 * ((j : ℕ) : ℤ))) (s.e.symm k)) ^ x k)
  rw [← h, Fintype.prod_sum_type]
  simp [resL, resR]
  simp only [mul_zpow, Finset.prod_mul_distrib]

theorem gapRes : GapRes := by
  intro n s x hx
  have hx' : ∀ i j : Fin n, i < j → x j + 2 ≤ x i := hx
  refine ⟨?_, ?_⟩
  · unfold Gap
    intro i j hij
    have := hx' _ _ (s.monoL hij)
    dsimp only at this
    simp only [resL]
    omega
  · unfold Gap
    intro i j hij
    have := hx' _ _ (s.monoR hij)
    dsimp only at this
    simp only [resR]
    omega

end PositivityTheory.Rg.BcB.F.Choice

end
