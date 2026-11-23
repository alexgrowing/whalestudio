import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NormOneAtOne
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.JZeroMulMemLatticeIff
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MulFractionalIdealCompletionSubsetIffMemQuotientStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitIdealCompletionAtPlaceEqIntegralAdelesAtPlac
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.InverseDifferentCompletionIffCharacterDual
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChainFractionalIdealRelations
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (latV Moves MonoAt OrthAt PrimAt idAt intAt grpAt colMul Lat SplitPt GoodBF GluedCore IsSumFrame)
open GlobalTheory.SeeSaw (idV dI FI)
open ValuativeRel
open GlobalTheory.Core.Mi.LatMatch

noncomputable section

namespace GlobalTheory.Core.Mi.LatMatch

open GlobalTheory.SeeSaw.AdaptFBIdeals

theorem primAt_lastAt_of_lines : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (z : Fin S₀.rank → D.host.E) (L : Lat S) (M : Lat S₀) (μ : D.host.E) (v : GlobalTheory.FinPl.Pl D), μ ≠ 0 → LineAt z μ M v → (∀ i : Fin ρ, ∀ a ∈ idAt D (· = v), colMul d.jX i a ∈ latV S L (· = v) ↔ incA D μ * a ∈ idV (dI D ^ (ρ - i.1)) v) → PrimAt ψ d L v ∧ LastAt ψ d z L M v := by
  intro D ψ hψ S S₀ ρ d z L M μ v hμ hline hcol
  have hdI : dI D ≠ 0 := (GlobalTheory.SeeSaw.ChainIdeals.host_ne_zero D).2.2.2
  have hu : incA D μ⁻¹ * incA D μ = 1 := by rw [← map_mul, inv_mul_cancel₀ hμ, map_one]
  have key : ∀ 𝔞 𝔟 : FI D, 𝔞 ≠ 0 → 𝔟 ≠ 0 → 𝔟 * 𝔞⁻¹ = dI D → ∀ s ∈ idAt D (· = v),
      ((∀ a ∈ idAt D (· = v), incA D μ * a ∈ idV 𝔞 v → incA D μ * (s * a) ∈ idV 𝔟 v) ↔
        ∀ o ∈ intAt D (· = v), psiE ψ (s * o) = 1) := by
    intro 𝔞 𝔟 h𝔞 h𝔟 hq s hs
    rw [← GlobalTheory.SeeSaw.DiffDual.idV_dI_iff D ψ hψ v s hs, ← hq, ← GlobalTheory.T.mul_fractionalIdealCompletion_subset_iff_mem_quotient D v 𝔞 𝔟 h𝔞 h𝔟 s hs]
    constructor
    · intro h b hb
      have hbAt := idV_supp 𝔞 v hb
      have ha : incA D μ⁻¹ * b ∈ idAt D (· = v) := Ideal.mul_mem_left _ _ hbAt
      have hb' : incA D μ * (incA D μ⁻¹ * b) = b := by rw [← mul_assoc, mul_comm (incA D μ), hu, one_mul]
      have h2 := h _ ha (by rw [hb']; exact hb)
      rwa [mul_left_comm, hb'] at h2
    · intro h a _ hma
      rw [mul_left_comm]
      exact h _ hma
  constructor
  · intro i j hij s hs
    have hq : dI D ^ (ρ - i.1) * (dI D ^ (ρ - j.1))⁻¹ = dI D := by
      have he : ρ - i.1 = (ρ - j.1) + 1 := by have := j.2; omega
      rw [he, pow_succ, mul_comm, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ hdI), one_mul]
    rw [← key (dI D ^ (ρ - j.1)) (dI D ^ (ρ - i.1)) (pow_ne_zero _ hdI) (pow_ne_zero _ hdI) hq s hs]
    constructor
    · intro h a ha hma
      exact (hcol i (s * a) (Ideal.mul_mem_left _ _ ha)).1 (h a ((hcol j a ha).2 hma))
    · intro h a ha
      have haAt := supp_of_colMul d L v j a ha
      exact (hcol i (s * a) (Ideal.mul_mem_left _ _ haAt)).2 (h a haAt ((hcol j a haAt).1 ha))
  · intro i hi s hs
    rw [← key 1 (dI D) one_ne_zero hdI (by rw [inv_one, mul_one]) s hs]
    have hρi : ρ - i.1 = 1 := by omega
    constructor
    · intro h a ha hma
      rw [GlobalTheory.SeeSaw.idV_one_eq_intAt] at hma
      have h2 := (hcol i (s * a) (Ideal.mul_mem_left _ _ ha)).1 (h a ha ((hline a ha).2 hma))
      rwa [hρi, pow_one] at h2
    · intro h a ha hz
      have h2 := h a ha ((GlobalTheory.SeeSaw.idV_one_eq_intAt D v _).2 ((hline a ha).1 hz))
      exact (hcol i (s * a) (Ideal.mul_mem_left _ _ ha)).2 (by rwa [hρi, pow_one])

end GlobalTheory.Core.Mi.LatMatch

end
