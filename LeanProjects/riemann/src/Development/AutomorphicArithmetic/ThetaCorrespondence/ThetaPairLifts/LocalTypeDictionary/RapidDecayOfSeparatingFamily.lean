import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LevelTowerRapidDecay
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LevelTowerRapidDecayStatement

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.SepRows.RowRapidPf
theorem separating_family_rapid_decay : _root_.GlobalTheory.FunPr.ThetaLocalInputs → RowTower → RowRapid := by
  intro hP hT D hq hs T L μ0 hL sc hc G W M hM M₀ hM₀ t ht w
  have ht' : t ∈ MultT W.θ M₀ ∅ 1 := multT_le_empty W.θ M₀ _ _ ht
  have key : ∀ ρ Φ n (h : n ≤ D.R.m),
      PathConv W M (rowPath T 0 n) (rowFam 0 n fun i => W.datum ρ Φ (Fin.castLE h i)) (t w) ∧
        RapidDec (G.V (.grid n 0)) (part W M ρ Φ (t w) n h) := by
    intro ρ Φ n h
    obtain ⟨S, MB, -, -, vec, hv⟩ := hT D hq hs T L μ0 hL sc hc G W M hM M₀ hM₀ n h
    obtain ⟨F', hF', hF⟩ := hv t ht' Φ
    obtain ⟨hcv, heq⟩ := hF ρ w
    refine ⟨hcv, ?_⟩
    rw [heq]
    exact (GlobalTheory.ChainOnto.MultRapid.multT_apply_rapidDec hP.cuspRapidDecay D _ S MB W.θ W.θ_is ∅ 1 F' hF' (vec ρ w)).2.2
  exact ⟨fun ρ Φ n h => (key ρ Φ n h).2, fun ρ Φ => (key ρ Φ D.R.m le_rfl).1⟩
end GlobalTheory.SepRows.RowRapidPf
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rapid_decay_of_separating_family : _root_.GlobalTheory.FunPr.ThetaLocalInputs → RowTower → RowRapid := by
  first | exact @_root_.GlobalTheory.SepRows.RowRapidPf.separating_family_rapid_decay | exact _root_.GlobalTheory.SepRows.RowRapidPf.separating_family_rapid_decay | (intros; apply _root_.GlobalTheory.SepRows.RowRapidPf.separating_family_rapid_decay <;> assumption)
end
