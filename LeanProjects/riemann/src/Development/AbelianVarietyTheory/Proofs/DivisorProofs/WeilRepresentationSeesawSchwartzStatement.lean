import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationSeesawSchwartz
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
theorem _root_.GlobalTheory.T.weil_representation_seesaw_schwartz : ∀ (D : D7) (n : ℕ) (V : HSp D) (ψ : AddChar (AF D.host.F) ℂ) (χ : (AE D)ˣ →* Circle) (θ : InfFam D), IsInfFam θ → ∀ (μ : Measure (Mx D V.rank n)) (𝓕 : Set (Mx D V.rank n)), IsCovolOne (ratMx D V.rank n) μ 𝓕 → ∀ ω : GlobalTheory.StdUnn.G D n →* Module.End ℂ (schwartzA θ V.rank n), GlobalTheory.StdUnn.IsWeilSch ψ χ θ V μ ω → ∀ (J₂ : Matrix (Fin (n + n)) (Fin (n + n)) D.host.E) (d : ℕ) (ε : Module.Basis (Fin d) D.host.F D.host.E) (ι : UD D (-V.gram) ≃ₜ* GA D V) (κ : UD D J₂ ≃* GlobalTheory.StdUnn.G D n), ∃ om, IsTrans ε ι κ ω om := by
  first | exact @GlobalTheory.SWTrans.exists_isTrans | exact GlobalTheory.SWTrans.exists_isTrans | (intros; apply GlobalTheory.SWTrans.exists_isTrans <;> assumption)
