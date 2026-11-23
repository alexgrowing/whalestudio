import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LevelTowerConvergence
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LevelTowerConvergenceStatement

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.RowConvAll
theorem separating_family_converges : _root_.GlobalTheory.FunPr.ThetaLocalInputs → RowTower → RowConv := by
  intro hP hT D hq hS T L μ0 hL sc hc G W M hM M₀ hM₀ t ht w ρ ξ Ψ hΨ Φ
  obtain ⟨S, MB, -, -, vec, hv⟩ := hT D hq hS T L μ0 hL sc hc G W M hM M₀ hM₀ D.R.m le_rfl
  obtain ⟨F', hF', hF⟩ := hv t (multT_le_empty _ _ _ _ ht) Φ
  obtain ⟨hconv, hpart⟩ := hF ρ w
  have hrow : (fun i : Fin D.R.m => W.datum ρ Φ (Fin.castLE (le_refl D.R.m) i)) = W.datum ρ Φ := by
    funext i; simp
  rw [hrow] at hconv
  have hth : thetaChi W M ρ Φ (t w) = F' (vec ρ w) := hpart
  refine ⟨hconv, ?_⟩
  rw [hth]
  have hA := (GlobalTheory.ChainOnto.MultRapid.multT_apply_rapidDec hP.cuspRapidDecay D _ S MB W.θ W.θ_is ∅ 1 F' hF' (vec ρ w)).1
  exact GlobalTheory.RowBplus.bplusConv_col W M hM ξ Ψ hΨ _ hA.toIsAutFun
end GlobalTheory.RowConvAll
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.convergence_of_separating_family : _root_.GlobalTheory.FunPr.ThetaLocalInputs → RowTower → RowConv := by
  first | exact @_root_.GlobalTheory.RowConvAll.separating_family_converges | exact _root_.GlobalTheory.RowConvAll.separating_family_converges | (intros; apply _root_.GlobalTheory.RowConvAll.separating_family_converges <;> assumption)
end
