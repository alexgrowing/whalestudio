import Development.AutomorphicArithmetic.Foundations.LocalLanglands.RecTTransport
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.Multi
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LanglandsExtensionUniqueOnCuspidal
import Development.DiscreteGroups.GlobalIrreducibility.DzLCusp
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.ArtEx
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.CuspEx
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.ExtDim
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.RcTwOfSegments
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.ExtDual
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.ExtInj
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.ExtDepth
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.TypeIff
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.ClBasic

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.Zero.LLC.recTExists :
    UpperTheory.Zero.LLC.RecTExists := by
  intro E Ω _ _ _ _ _ A w h
  obtain ⟨a, ha, -⟩ := UpperTheory.Zero.LLC.artEx E Ω A w h
  obtain ⟨r, hr⟩ := UpperTheory.Zero.LLC.cuspEx E Ω A w h a ha
  obtain ⟨⟨rc, hrc⟩, hcu⟩ :=
    GlobalTheory.LocLanglands.exists_isLExt UpperTheory.Zero.LLC.Pr.exh UpperTheory.Zero.LLC.Pr.multi E Ω A w h r
  have hcusp : ∀ x : IrrGL (HeightOneSpectrum.adicCompletion E w), x.IsCusp → rc x = r x :=
    hcu rc hrc
  have hD := UpperTheory.Zero.LLC.extDim E Ω A w h a ha r rc hr hrc
  have hT := UpperTheory.Zero.LLC.extTw E Ω A w h a ha r rc hr hrc
  refine ⟨rc, a, ha, ?_⟩
  refine
    { dim := fun x => (hD x).1.1
      one := fun χ hχ => (hcusp _ (IrrGL.isCusp_ofChar χ hχ)).trans (hr.one χ hχ)
      langlands := ?_
      cusp := ?_
      nu := hT.1
      absCentral := fun x ω hω σ => ((hD x).2 ω hω σ).1
      twist := ?_
      central := fun x ω hg hω σ => ((hD x).2 ω hω σ).2 hg
      dual := UpperTheory.Zero.LLC.extDual E Ω A w h a ha r rc hr hrc
      inj := UpperTheory.Zero.LLC.extInj E Ω A w h a ha r rc hr hrc
      depth := fun x hg hx => UpperTheory.Zero.LLC.extDepth E Ω A w h a ha r rc hr hrc x hg hx
      type := ?_ }
  · intro l x hl
    rw [hrc l x hl]
    unfold GlobalTheory.LocLanglands.segSum
    congr 1
    refine List.map_congr_left ?_
    intro Δ _
    rw [hcusp _ Δ.isCusp_first]
  · intro x hx
    rw [hcusp x hx]
    exact hr.irr x hx
  · intro x χ hχ hg
    rw [hcusp _ (IrrGL.isCusp_ofChar χ hχ), hr.one χ hχ]
    exact hT.2 x χ hχ hg
  · refine (UpperTheory.Zero.LLC.typeIff E Ω A w h rc).2 ?_
    intro x
    unfold UpperTheory.Zero.LLC.TypeAt
    intro g _ i hi n hn D R hR θ hθ τ hτ hN σ hσ hinf
    have hx : x.IsCusp := by
      subst hσ
      exact IrrGL.isCusp_of.2 ⟨hn, DiscreteGroups.sglob.DzLc.isCuspidal_of_inflates i hi τ hτ σ hinf⟩
    rw [hcusp x hx]
    exact hr.type x hx g i hi n hn D R hR θ hθ τ hτ hN σ hσ hinf
