import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ProdDat
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TensorOneApply
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilCharacterSplitPlaceExistsContinuousNontrivia
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceCharacterConductorIntegers
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CoreIffCollapsesWith
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.LocMod GlobalTheory.SplitWeil ValuativeRel

noncomputable section

namespace GlobalTheory.SplitWeilChar

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem splitPlace_polarisationDatum_inv_integral (q : SplitPt D k) (hU : q.UnitAA) : q.pr (incA D D.host.xi0⁻¹) ∈ 𝒪[k] := by
  obtain ⟨η, hη, h0, h⟩ := GlobalTheory.SplitCharCond.exists_idem q
  have hm : (pairA D.host.F 0 η ⊗ₜ[D.host.F] (1 : D.host.E) : AE D) ∈ intAt D (· = q.v) := by
    refine ⟨⟨?_, ?_⟩, AddSubgroup.subset_closure ⟨η, hη, 1, rfl⟩⟩
    · change (0 : Ainf D.host.F) ⊗ₜ[D.host.F] (1 : D.host.E) = 0
      exact TensorProduct.zero_tmul _ _
    · refine Ideal.mem_iInf.2 fun w => ?_
      change evalV D.host.F w.1 η ⊗ₜ[D.host.F] (1 : D.host.E) = 0
      rw [h0 w.1 w.2, TensorProduct.zero_tmul]
  have := GlobalTheory.SplitCharCond.pr_int q (hU.1 _ hm).2.2
  rwa [map_mul, GlobalTheory.SplitCharCond.pr_pair_tmul q h, map_one, map_one, mul_one] at this

theorem valuation_pr_incA_xi0_eq_one_of_unitAA (q : SplitPt D k) (hU : q.UnitAA) : valuation k (q.pr (incA D D.host.xi0)) = 1 := by
  have h1 := (Valuation.mem_integer_iff _ _).1 (GlobalTheory.SplitCharCond.xi_zero_projection_integral q hU)
  have h2 := (Valuation.mem_integer_iff _ _).1 (splitPlace_polarisationDatum_inv_integral q hU)
  have hm : q.pr (incA D D.host.xi0) * q.pr (incA D D.host.xi0⁻¹) = 1 := by
    rw [← map_mul, ← map_mul, mul_inv_cancel₀ (GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D), map_one, map_one]
  have h3 := congrArg (valuation k) hm
  rw [map_mul, map_one] at h3
  by_contra hne
  have hlt : valuation k (q.pr (incA D D.host.xi0)) < 1 := lt_of_le_of_ne h1 hne
  have : valuation k (q.pr (incA D D.host.xi0)) * valuation k (q.pr (incA D D.host.xi0⁻¹)) < 1 :=
    mul_lt_one_of_lt_of_le hlt h2
  rw [h3] at this
  exact lt_irrefl _ this

end GlobalTheory.SplitWeilChar

namespace GlobalTheory.SplitWeilChar

theorem weil_char_conductor_one : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : SplitPt D k) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → q.UnitAA → ∃ ψk : AddChar k Circle, (ofSplit q).IsChar ψ ψk ∧ HasConductor ψk 1 := by
  intro D k _ _ _ _ q ψ hψ hU
  obtain ⟨⟨ψk, hk⟩, -⟩ := GlobalTheory.LocChar.weil_char_split D k (ofSplit q) ψ hψ
  set u : k := q.pr (incA D D.host.xi0) with hu
  have hv : valuation k u = 1 := valuation_pr_incA_xi0_eq_one_of_unitAA q hU
  have hu0 : u ≠ 0 := fun h => by rw [h, map_zero] at hv; exact zero_ne_one hv
  let χ : AddChar k Circle := ψk.mulShift u⁻¹
  have hχ : q.IsChar ψ χ := by
    intro a
    have e1 : (χ a : ℂ) = psiE ψ (incA D D.host.xi0 * q.sec (u⁻¹ * a)) := hk (u⁻¹ * a)
    have e2 := GlobalTheory.SplitCharCond.sec_mul_pr q (u⁻¹ * a) (incA D D.host.xi0)
    rw [← hu, show u⁻¹ * a * u = a by field_simp] at e2
    rw [e1, ← e2]
  have hc1 : HasConductor χ 1 := GlobalTheory.SplitCharCond.hasConductor_one D k q ψ χ hψ hχ hU
  have hcu : HasConductor χ (Units.mk0 u hu0) := by
    intro x
    rw [Units.val_mk0, hv]
    have := hc1 x
    rwa [Units.val_one, map_one] at this
  have he : ψk = χ.mulShift ((Units.mk0 u hu0 : kˣ) : k) := by
    ext x
    simp only [χ, AddChar.mulShift_apply, Units.val_mk0]
    rw [← mul_assoc, inv_mul_cancel₀ hu0, one_mul]
  refine ⟨ψk, hk, ?_⟩
  rw [he]
  exact GlobalTheory.CollapseCompare.hasConductor_mulShift hcu

end GlobalTheory.SplitWeilChar
end
