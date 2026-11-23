import Development.AutomorphicArithmetic.Foundations.LocalLanglands.RecTTransport
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.TypeEx
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.NameLaws
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.ExtEx
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.FinrankK
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.TameUniq
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.DetByType
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.ClBasic

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.Zero.LLC.parUniq :
    UpperTheory.Zero.LLC.ParUniq := by
  intro E Ω _ _ _ _ _ A w h a ha g _ i hi y hy hdz V hV
  obtain ⟨n, c⟩ := y
  have hn : 0 < n := hy.1
  have hcl : GlobalTheory.LocLanglands.cls c.rep = (⟨n, c⟩ : IrrGL (HeightOneSpectrum.adicCompletion E w)) :=
    IrrGL.of_rep ⟨n, c⟩
  obtain ⟨D⟩ := UpperTheory.Zero.LLC.extEx E Ω A w h g i hi n hn
  obtain ⟨⟨R, hR⟩, hRT⟩ := UpperTheory.Zero.LLC.resEx E Ω A w h g i hi n hn D
  have hT := hRT R hR
  obtain ⟨τ, hτ, hinf⟩ := (UpperTheory.Zero.LLC.typeEx E Ω A w h g i hi n hn c.rep).1
    (by rw [hcl]; exact hy) (by rw [hcl]; exact hdz)
  obtain ⟨hNex, -, hNchar, -⟩ := UpperTheory.Zero.LLC.nameLaws g n hn D.K hT.rank
  obtain ⟨θ, hθ, hθτ⟩ := hNex τ hτ
  have hIF : ∀ W : WD h, UpperTheory.Zero.LLC.Par a ⟨n, c⟩ W → UpperTheory.Zero.LLC.InFor g n R θ W :=
    fun W hW => (hW.type g i hi n hn D R hR θ hθ τ hτ hθτ c.rep hcl hinf).2
  obtain ⟨ω, -, hω, -⟩ := (UpperTheory.Zero.LLC.clBasic _ (⟨n, c⟩ : IrrGL _)).1
  obtain ⟨-, hθu, hVu⟩ := UpperTheory.Zero.LLC.tameUniq E Ω A w h g n D.K R hT θ hθ V (hIF V hV)
  refine ⟨fun V' hV' => hVu V' hV.irr hV'.irr hV.tame hV'.tame (hIF V' hV')
    (fun s => by rw [hV.central ω hω s, hV'.central ω hω s]), ?_⟩
  rintro ⟨m, c'⟩ hy' hdz' hV'
  have hm : m = n := hV'.dim.symm.trans hV.dim
  subst m
  have hcl' : GlobalTheory.LocLanglands.cls c'.rep = (⟨n, c'⟩ : IrrGL (HeightOneSpectrum.adicCompletion E w)) :=
    IrrGL.of_rep ⟨n, c'⟩
  obtain ⟨τ', hτ', hinf'⟩ := (UpperTheory.Zero.LLC.typeEx E Ω A w h g i hi n hn c'.rep).1
    (by rw [hcl']; exact hy') (by rw [hcl']; exact hdz')
  obtain ⟨θ', hθ', hθτ'⟩ := hNex τ' hτ'
  have hIF' : UpperTheory.Zero.LLC.InFor g n R θ' V :=
    (hV'.type g i hi n hn D R hR θ' hθ' τ' hτ' hθτ' c'.rep hcl' hinf').2
  obtain ⟨j, -, rfl⟩ := hθu θ' hIF'
  have hch : τ'.character = τ.character := hNchar τ τ' θ j hτ hτ' hθ hθτ hθτ'
  obtain ⟨ω', -, hω', -⟩ := (UpperTheory.Zero.LLC.clBasic _ (⟨n, c'⟩ : IrrGL _)).1
  have hωω : ω' = ω := by
    ext z
    obtain ⟨s, rfl⟩ := ha.surj z
    exact (hV'.central ω' hω' s).symm.trans (hV.central ω hω s)
  subst ω'
  have hdet := UpperTheory.Zero.LLC.detByType E Ω A w h g i hi n hn c.rep c'.rep τ τ' ω hτ hch hinf hinf' hω hω'
  exact hcl'.symm.trans (hdet.trans hcl)
