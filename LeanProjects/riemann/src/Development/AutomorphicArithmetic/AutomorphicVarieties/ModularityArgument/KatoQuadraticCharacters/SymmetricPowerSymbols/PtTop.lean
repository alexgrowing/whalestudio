import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.UniformizerIntegrality.IsoEx
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.UniformizerIntegrality.TopUnit
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.UniformizerIntegrality.ValComapLtOne
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.UniformizerIntegrality.TopPtAlt
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.UniformizerIntegrality.TopPt
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ContinuousToK

open GlobalTheory.KZ GlobalTheory.K4 UpperTheory.V.Z.Kato.Sym UpperTheory.V.Z.Kato.Sym.PT

attribute [local instance] algMdl

theorem UpperTheory.V.Z.Kato.Sym.ptTop :
    UpperTheory.V.Z.Kato.Sym.PtTop := by
  intro Ω _ _ _ ε X l n M hl hM hd u v hu hv huF hvF
  obtain ⟨e, he⟩ := isoEx Ω ε X M
  obtain ⟨h1, h2⟩ := TopEta.spec_of_units X hM.ne' hl.ne_zero hd (isTopUnit X M hu huF) (isTopUnit X M hv hvF)
  have hη := isTopEta_topEta X M h1
  refine ⟨_, ptIs Ω ε X l n M hl hM hd u v hu hv huF hvF e he _ hη, ptGam Ω ε X l n M hl hM hd u v hu hv huF hvF e he _ hη,
    fun s hs => ?_⟩
  have hw := h2 (topLift X M s)⁻¹
  have h0 : wGen X M l n u v s ≠ 0 := fun h => hw.1 (Subtype.ext h)
  exact ⟨Units.mk0 _ h0, rfl, ptGal Ω ε X l n M hl hM hd u v hu hv huF hvF e he _ hη s hs _ hw _ rfl⟩
