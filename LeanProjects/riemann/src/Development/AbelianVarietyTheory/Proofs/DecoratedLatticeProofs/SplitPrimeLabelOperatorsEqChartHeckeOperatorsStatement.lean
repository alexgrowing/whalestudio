import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPrimeLabelOperatorsEqChartHeckeOperators
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TransferOn
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsPairingSingleNe
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep
open GlobalTheory.FinZeta (Gv embV Kv VacFin IsLocKer KerU)
open GlobalTheory.SphTheta (IsStd CayleyRule intMat liftPar)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke IsCommensurated Tj SatU ordL Ov)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (opOf hyp)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.split_prime_label_operators_eq_chart_hecke_operators : ∀ (D : D7) (V : HSp D) (v : HeightOneSpectrum (𝓞 D.host.F)) (w : HeightOneSpectrum (𝓞 D.host.E)) (h : w.under (𝓞 D.host.F) = v), IsSplit (E := D.host.E) v → ∀ e, IsSplitChart D.sp.cm.sig V.gram (frameLat V) h e → ∀ (M : Type) [AddCommGroup M] [Module ℂ M] (π : GA D V →* Module.End ℂ M) (u : M), (∀ k ∈ Kv V v, π (embV V v k) u = u) → ∀ ϖ, IsUnifV D.host.E w ϖ → ∀ k ≤ V.rank, opOf π w (Finsupp.single (splitLab V.rank k) 1) u = heckeVec ((π.comp (embV V v)).comp e.symm.toMonoidHom) (KGL w V.rank) (fun g => Tj ℂ V.rank (Ov D.host.E w) ϖ k g⁻¹) u ∧ opOf π w (Finsupp.single (dualLab (splitLab V.rank k)) 1) u = heckeVec ((π.comp (embV V v)).comp e.symm.toMonoidHom) (KGL w V.rank) (Tj ℂ V.rank (Ov D.host.E w) ϖ k) u := by
  first | exact @GlobalTheory.ChainOnto.LabChart.split_label_ops | exact GlobalTheory.ChainOnto.LabChart.split_label_ops | (intros; apply GlobalTheory.ChainOnto.LabChart.split_label_ops <;> assumption)
