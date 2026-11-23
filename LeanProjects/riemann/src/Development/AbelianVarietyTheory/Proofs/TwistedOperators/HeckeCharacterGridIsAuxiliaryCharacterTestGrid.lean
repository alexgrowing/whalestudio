import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NodeAgree
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
import Formalism.LocalToGlobal.IndefiniteReal.LinksLemmas
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DiscreteSeriesUpqExistsIffDsExists
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeCharIsUnitaryOfUnitaryInfinityTypeStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.ChiGrid GlobalTheory.GridJoin
open scoped Pointwise TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Grid

theorem heckeCharacterGrid_isAuxiliaryCharacter_testGrid_alt : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {sc : GlobalTheory.ChiGrid.Consts}, GlobalTheory.Grid.gap D = GlobalTheory.ChiGrid.gap D 1 → sc.cGap = 1 → ∀ {G' : GlobalTheory.ChiGrid.GridData R.toLevCh sc} (Z : GlobalTheory.Grid.PlaceDat D), Z.S0 R.Pg = G'.pl.S0 → (∀ w, w ∈ R.Pg ∨ w ∈ Z.Wd → w.under (𝓞 D.host.F) ∈ GlobalTheory.ChiGrid.S1 D) → (∀ w ∈ Z.Wd, Formalism.L2.Host.OverP D.host D.host.pde w ∨ Formalism.L2.Host.OverP D.host D.host.pde' w) → Z.w0 = G'.pl.w G'.pl.v0 → ∀ i, 1 ≤ i → i ≤ D.R.m → Z.IsGridPlaceAuxiliaryHeckeCharacter R.Pg (fun τ => GlobalTheory.Grid.cen D τ i) (G'.ch.chiH i) := by
  intro D Γ _ _ Pl0 T A Ks _ _ _ R sc hgap hc G' Z hS0 hS1 hwd hw0 i hi1 hi2
  have hcen : ∀ τ, GlobalTheory.Grid.cen D τ i = GlobalTheory.ChiGrid.cen D sc.cGap τ i := by
    intro τ
    rw [hc]
    unfold GlobalTheory.Grid.cen GlobalTheory.ChiGrid.cen GlobalTheory.Grid.gridOf
    rw [hgap]
    rfl
  have hunit : (G'.ch.chiH i).IsUnitary := GlobalTheory.T.heckeChar_isUnitary_of_unitary_infinityType _ _ _ _ (G'.ch.inf i hi1 hi2)
  refine ⟨hunit, G'.ch.triv i hi1 hi2, ?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨fun τ => 2 * GlobalTheory.ChiGrid.cen D sc.cGap τ i, fun τ => ?_, G'.ch.inf i hi1 hi2⟩
    show ((2 * GlobalTheory.ChiGrid.cen D sc.cGap τ i : ℤ) : ℚ) = 2 * ((GlobalTheory.Grid.cen D τ i : ℤ) : ℚ)
    rw [hcen τ]; push_cast; ring
  · intro w hw
    rw [hS0] at hw
    exact G'.ch.unr i hi1 hi2 w hw
  · intro w hw
    exact G'.ch.lev1 i hi1 hi2 w (hS1 w hw)
  · intro w hw x hx
    exact G'.ch.wild i hi1 hi2 w (hwd w hw) x hx
  · have hu : Z.w0.under (𝓞 D.host.F) = G'.pl.v0 := by
      rw [hw0]; exact G'.pl.under_w (G'.pl.mem_S0_of_sum_eq.2 (Or.inl rfl))
    exact G'.ch.lev0 i hi1 hi2 Z.w0 hu

end GlobalTheory.Grid

end
