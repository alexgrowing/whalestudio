import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalUnitaryGroupIsoGL
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaOn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndicatorIntMMemSB
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.Doubling GlobalTheory.ThK.Bot
open Formalism.L2.Host (aboveF)
open Formalism.UG (IsUnifV qV)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_unitary_group_iso_GL : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n : ℕ) (Y : Spc F E n), IsCMExt F E σ → IsHermND σ Y.J → Y.L.IsLattice E →
    ∀ v : Pl F, IsSelfDualAt σ Y.Jᵀ Y.L v → ∀ K : Subgroup (UA σ Y.J), IsStab B K →
    ∀ (t : E →ₐ[F] Fv F v) (b : GL (Fin n) (Fv F v)), IsSplitBasis t Y.L b →
    ∃ e : UAtSub σ Y (evFin F v) ≃ₜ* GL (Fin n) (Fv F v), (∀ g, e g = GlobalTheory.KSplit.locMat t b g.1) ∧ ∀ g, g.1 ∈ K ↔ e g ∈ KGL v n := by
  first | exact @GlobalTheory.SplitChart.chart | exact GlobalTheory.SplitChart.chart | (intros; apply GlobalTheory.SplitChart.chart <;> assumption)
