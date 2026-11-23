import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.PsiVNeOneOfTrace
import Development.AbelianVarietyTheory.Proofs.HeightProofs.SymplecticValTauCompat

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl ValuativeRel NumberField
open IsDedekindDomain

namespace GlobalTheory.FinPl.CharNontriv

theorem exists_psiV_ne_one (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsStdChar D ψ (-1))
    (v : HeightOneSpectrum (𝓞 D.host.F)) : ∃ y, ψ (pairA D.host.F 0 (singleV D.host.F v y)) ≠ 1 := by
  have h := hψ.1
  have h' : IsCharAF D.host.F ψ⁻¹ := by
    refine ⟨h.1.comp continuous_neg, fun x => h.2.1 _, fun a => ?_, ?_⟩
    · rw [AddChar.inv_apply, ← map_neg]; exact h.2.2.1 _
    · obtain ⟨x, hx⟩ := h.2.2.2
      exact ⟨-x, by rwa [AddChar.inv_apply, neg_neg]⟩
  obtain ⟨y, hy⟩ := GlobalTheory.StdCharTotReal.psiV_ne_one_of_trace h' (fun a => by
    rw [← GlobalTheory.StdRat.stdChar_fin_rat D ψ hψ, GlobalTheory.StdRat.char_fin_rat ψ h, psiInf, psiInf, AddChar.inv_apply,
      map_neg (algebraMap D.host.F (Ainf D.host.F))]
    refine congrArg ψ (Prod.ext rfl ?_)
    exact neg_zero) v
  refine ⟨y, fun h1 => hy ?_⟩
  rw [psiV, AddChar.inv_apply', h1, inv_one]

theorem algebraMap_injective (D : D7) : Function.Injective (algebraMap (AF D.host.F) (AE D)) :=
  Algebra.TensorProduct.includeLeft_injective (S := D.host.F) (algebraMap D.host.F D.host.E).injective

theorem exists_psiE_sec_ne_one : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∃ a : k, GlobalTheory.MixPer.psiE ψ (p.sec a) ≠ 1 := by
  intro D k _ _ _ _ p ψ hψ
  obtain ⟨y, hy⟩ := exists_psiV_ne_one D ψ hψ p.v
  obtain ⟨ε, ⟨α, rfl, h1, -⟩, he⟩ := p.above
  have ht : Algebra.trace (AF D.host.F) (AE D) p.e = pairA D.host.F 0 α :=
    algebraMap_injective D ((GlobalTheory.FockCompare.SymplVal.trace_AE D p.e).trans he)
  refine ⟨p.pr (algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 (singleV D.host.F p.v y))), ?_⟩
  rw [p.sec_pr, GlobalTheory.MixPer.psiE, mul_comm, ← Algebra.smul_def, map_smul, ht, smul_eq_mul]
  have h2 : pairA D.host.F 0 (singleV D.host.F p.v y) * pairA D.host.F 0 α =
      pairA D.host.F 0 (singleV D.host.F p.v y) := by
    refine Prod.ext (zero_mul _) ?_
    show singleV D.host.F p.v y * α = singleV D.host.F p.v y
    have h3 : α p.v = 1 := h1
    rw [GlobalTheory.StdCharTotReal.single_mul, h3, mul_one]
  rwa [h2]

end GlobalTheory.FinPl.CharNontriv
