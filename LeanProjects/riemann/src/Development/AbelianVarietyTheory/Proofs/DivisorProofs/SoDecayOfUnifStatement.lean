import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SoDecayOfUnif
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTorusUOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThKSoDecay
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.soDecay_of_prints_of_soDecayUnif : GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.ThKSoDecay.SoDecayUnif → GlobalTheory.ThK.SoDecay := by
  first | exact @GlobalTheory.ThKSoSpan.soDecay_of_unif | exact GlobalTheory.ThKSoSpan.soDecay_of_unif | (intros; apply GlobalTheory.ThKSoSpan.soDecay_of_unif <;> assumption)
