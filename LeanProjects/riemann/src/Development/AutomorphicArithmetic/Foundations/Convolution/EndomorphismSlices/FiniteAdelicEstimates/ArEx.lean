import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.SphComm2
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.HyperbolicEntryBounds.ArchFinal

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.Desc
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf TypeB TypeH)
open UpperTheory.V.Z.Tf.GlobalTraceComparison
open UpperTheory.V.Af.Bc (cPl)
open scoped Classical

set_option synthInstance.maxHeartbeats 200000

attribute [local instance] borelG borelF borelA borelH

theorem UpperTheory.Zero.ConvolutionTheory.EB.arEx :
    UpperTheory.Zero.ConvolutionTheory.EB.ArEx := by
  intro E _ _ _ a b l₁ l₂ D
  haveI : BorelSpace (G a) := ⟨rfl⟩
  haveI : BorelSpace (G b) := ⟨rfl⟩
  haveI : BorelSpace (Hf E a b) := ⟨rfl⟩
  haveI : LocallyCompactSpace (G a) := lc_G a
  haveI : LocallyCompactSpace (G b) := lc_G b
  let μa : Measure (G a) := Measure.haar
  let μb : Measure (G b) := Measure.haar
  have ha : μa.IsHaarMeasure := inferInstance
  have hb : μb.IsHaarMeasure := inferInstance
  obtain ⟨ν, hν, hν', hcomp⟩ := compatEx E a b D μa μb
  obtain ⟨-, -, ca, hca0, hca⟩ := GlobalTheory.CompanionTheory.Growth.size_facts E a
  obtain ⟨-, -, cb, hcb0, hcb⟩ := GlobalTheory.CompanionTheory.Growth.size_facts E b
  obtain ⟨bump, T, hT, hbump, hone⟩ := PositivityTheory.Rg.BcB.F.F0.bump_one (InfinitePlace E ⊕ InfinitePlace E)
    (Sum.elim (fun v => cas (UpperTheory.Zero.ConvolutionTheory.EB.chi l₁ v)) fun v => cas (UpperTheory.Zero.ConvolutionTheory.EB.chi l₂ v))
    (fun i => by cases i <;> exact PositivityTheory.Rg.BcB.F.F0.cas_infOf_im _)
  obtain ⟨_, hKa⟩ := PositivityTheory.RgBcC.wave_existence_speed_multiplicity.2.2.1 a
  obtain ⟨_, hKb⟩ := PositivityTheory.RgBcC.wave_existence_speed_multiplicity.2.2.1 b
  let Ma := UpperTheory.Zero.ConvolutionTheory.EB.Ml l₁
  let Mb := UpperTheory.Zero.ConvolutionTheory.EB.Ml l₂
  exact ⟨{
    μa := μa
    μb := μb
    ν := ν
    ha := ha
    hb := hb
    hν := hν
    hν' := hν'
    compat := hcomp
    c := max ca cb
    c_nonneg := le_max_of_le_left hca0
    ca := fun g h => (hca g h).trans (by gcongr; exact le_max_left _ _)
    cb := fun g h => (hcb g h).trans (by gcongr; exact le_max_right _ _)
    bump := bump
    T := T
    T_nonneg := hT
    isBump := hbump
    ka := fun w v => ((hKa μa (Ma v)).1 w bump T hbump).choose
    kb := fun w v => ((hKb μb (Mb v)).1 w bump T hbump).choose
    kera := fun w v => ((hKa μa (Ma v)).1 w bump T hbump).choose_spec
    kerb := fun w v => ((hKb μb (Mb v)).1 w bump T hbump).choose_spec
    one := by simpa [Fintype.prod_sum_type] using hone }⟩
