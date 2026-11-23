import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HaarAverageFundamentalDomainDescent
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockMatrixTwoByTwoFinTranspose
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Doubling GlobalTheory.MixModel GlobalTheory.SWLit
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (UA incM ratU)
open GlobalTheory.WeilM (Darboux symp schA thetaSum UG)
open GlobalTheory.SiegelFormula (coord)
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SWLink

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.haar_average_fundamental_domain_descent : ∀ (D : D7) (V : HSp D) (ι : UD D (-V.gram) ≃ₜ* GA D V), (∀ h, h ∈ ratU D.sp.cm.sig (-V.gram) ↔ ι h ∈ GQ V) → ∀ ν : Measure (GA D V), ν.IsHaarMeasure → ∃ (ν' : Measure (UD D (-V.gram))) (𝓕 : Set (UD D (-V.gram))), ν'.IsHaarMeasure ∧ IsFundamentalDomain (ratU D.sp.cm.sig (-V.gram)) 𝓕 ν' ∧ ∀ f : GA D V → ℂ, LeftInv (GQ V) f → ⨍ h in 𝓕, f (ι h) ∂ν' = ⨍ q, descend (GQ V) f q ∂autMeasure V ν := by
  first | exact @GlobalTheory.SWLink.exists_fundDom_mean | exact GlobalTheory.SWLink.exists_fundDom_mean | (intros; apply GlobalTheory.SWLink.exists_fundDom_mean <;> assumption)
