import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.BocksteinBaseChangeP
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.Development
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.GammaIndependence.PhiMain
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.AdmissibleMinors.admitted
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.AdicTorsionCup.DualOf
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.SmoothGaloisGeometry.Geo
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.BocksteinSheafHomotopy.Bock
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.BocksteinSheafHomotopy.EqZeroOfCast
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.BocksteinSheafHomotopy.SecMapZero

set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TensorProduct
open GroundTheory.PAdicHodge Formalism.Per6 DeRhamPotentiallySemistable.DRPst

namespace CrystallineSemistableComparison

theorem zIn (h : FormalIn) (h4 : GlobalTheory.EtC.E4) (h8 : GlobalTheory.EtC.E8) : ZIn :=
  ⟨h.a6nat, h.a6ring, h.a9, h.et.a11, h4, h8, bock h, root h, sum h⟩

theorem etSide : EtaleSideSmoothAndSemistable := fun h l _ K _ =>
  ⟨adic h l K _ (fun _ hM => hM.1) (comp l K).1 fun M hM => geo l K M hM.1,
    adic h l K _ (fun _ hM => hM) (comp l K).2 fun M hM => geo l K M hM⟩

structure Chapters : Prop where
  rin : ∀ (l : ℕ) [Fact l.Prime], E.RIn l
  et : ∀ (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l)), E.EtMap l K
  uniq : E.FirstChernUniqueEtale
  main : ∀ (l : ℕ) [Fact l.Prime], B.Main l
  compat : ∀ (l : ℕ) [Fact l.Prime], B.Compat l
  compatH : ∀ (l : ℕ) [Fact l.Prime], B.CompatH l
  c1 : ∀ (l : ℕ) [Fact l.Prime], B.FirstChernCompatible l
  p : BocksteinBaseChangeP

def CstSmooth : Prop := SmoothModelCrystalline ∧ DeRhamComparisonSmooth ∧ CrysPhi

theorem cstSmooth_of (gL : GlueL) (gE : GlueE) (gB : GlueB) (hF : PeriodRingFacts) (hR : BcrisRegularPeriodRing) (hC : BcrisPeriodFacts) (hX : ResEx)
    (hI : ZIn) (h : Chapters) : CstSmooth := by
  have hS : SeamS := by
    intro l _ K _
    obtain ⟨Amp, h1, h2, h3, h4⟩ := h.p l K
    obtain ⟨β, β₁, e⟩ := gB l K Amp (h.main l) (h.compat l) (h.c1 l)
    obtain ⟨r⟩ := hX l K
    obtain ⟨F⟩ := h4 r
    refine ⟨dat Amp, ⟨gL l K Amp (h.compatH l) (h.rin l) h.uniq h1 h2, gE l K Amp (h.et l K), ⟨β⟩, h3⟩, ?_⟩
    rw [← e] at F
    have := fac l K _ _ _ _ _ β β₁ F
    rwa [(hC l K r).2] at this
  obtain ⟨h1, h2⟩ := smooth_of hF hR pre inj adm etSide hI hS
  refine ⟨h1, h2, ?_⟩
  intro l _ K _ r
  obtain ⟨Amp, h1, h2, ⟨κ⟩, h4⟩ := h.p l K
  obtain ⟨β, β₁, e⟩ := gB l K Amp (h.main l) (h.compat l) (h.c1 l)
  obtain ⟨F⟩ := h4 r
  obtain ⟨ε⟩ := gE l K Amp (h.et l K)
  rw [← e] at F
  exact phi l K _ _ _ _ _ (hF l K) (hC l K r).1 (etSide hI l K).1 (gL l K Amp (h.compatH l) (h.rin l) h.uniq h1 h2) ε β β₁ κ F

end CrystallineSemistableComparison
