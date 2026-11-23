import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.WeightKernels.GoodSet
import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.SplitComp
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivOfIsSubquotient
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DiscreteSpectrumOfResidual

noncomputable section

open NumberField IsDedekindDomain ValuativeRel Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil
open UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict
open UpperTheory.V.W (Plc Lp)
open scoped Matrix

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.V.Z.Sym.Ga.galEx2 :
    Af.Hypotheses₂ → Af.GalUnitary → ∀ (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ), l ≠ 2 → Unr L → ∀ (n : ℕ), 1 ≤ n → ∀ σ : Submodule ℂ (UA L n → ℂ), IsAutRepU σ → ∃ (r : G L Ω →* GL (Fin n) (Qbar l)) (HT : (L →+* Qbar l) → Multiset ℤ), Ga.GalOf ι σ r ∧ IsSSRep r ∧ HasHT r HT ∧ (∀ (τ : L →+* Qbar l) lam, HasWeightAt σ (ι.toRingHom.comp τ) lam → (HT τ).map (fun k : ℤ => (k : ℂ)) = (infOfWeight lam).map fun z => ((n : ℂ) - 1) / 2 - z) ∧ (IsIrr r → IsAutC ι r) := by
  intro P hG L Ω _ _ _ _ _ _ l _ ι hl hE n hn σ hσ
  obtain ⟨r, HT, hc, hs, -, hHT, hwt, hLG, hp, hi⟩ := hG L Ω hE l hl ι n hn σ hσ
  obtain ⟨Pw, hbc⟩ := UpperTheory.BaseChangeIdentities.splitComp
    (GlobalTheory.BcSpeh.bcSpeh_of_baseChange (GlobalTheory.BaseChangeBridge.main P.litN.aut.bc P.litN.loc.bern)
      (GlobalTheory.SpehInfChar.discreteSpectrumGL_of_residual P.litN.aut.mw)) L hE n hn σ hσ
  refine ⟨r, HT, ⟨hc, fun w hw => ⟨Pw w hw, hbc w hw⟩, hLG, hp⟩, hs, hHT, hwt, fun h => ?_⟩
  obtain ⟨π, h1, -, h2, -⟩ := hi h
  exact ⟨π, h1, h2⟩
