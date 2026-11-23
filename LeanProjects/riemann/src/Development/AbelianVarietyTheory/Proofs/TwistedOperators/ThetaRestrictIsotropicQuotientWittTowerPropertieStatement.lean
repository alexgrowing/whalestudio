import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaRestrictIsotropicQuotientWittTowerPropertie
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.AdjointIsotropicDecomposition
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaRestrictIsotropicQuotient_wittTower_properties : ∀ (D : D7) (V V' W : HSp D) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), IsIsoSplit V V' C B → ∀ (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (μ : Measure (Mx D W.rank r)) (𝓨 : Set (Mx D W.rank r)), IsCovolOne (ratMx D W.rank r) μ 𝓨 → (∀ f, IsThetaFunO ψ V W f → (∀ x, IntegrableOn (fun y => f (isoPart V W C y + midPart V V' W B x)) 𝓨 μ) ∧ IsThetaFunO ψ V' W (res V V' W C B μ 𝓨 f) ∧ (∀ x, res V V' W C B μ 𝓨 (heisO ψ V W (midPart V V' W B x) f) = heisO ψ V' W x (res V V' W C B μ 𝓨 f)) ∧ ∀ y, res V V' W C B μ 𝓨 (heisO ψ V W (isoPart V W C y) f) = res V V' W C B μ 𝓨 f) ∧ ∃ f, IsThetaFunO ψ V W f ∧ res V V' W C B μ 𝓨 f ≠ 0 := by
  first | exact @GlobalTheory.TowerRestrict.res_theta | exact GlobalTheory.TowerRestrict.res_theta | (intros; apply GlobalTheory.TowerRestrict.res_theta <;> assumption)
