import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMinorProductTranslateJointLowestWeight
import Formalism.LocalToGlobal.IndefiniteReal.ConcretePkgSpec
import Formalism.LocalRingCardinality.DataExtra
import Formalism.LocalRingCardinality.DataTies
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsHolRepOfIsTau
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.JointHarm
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_minorProduct_translate_jointLowestWeight : ∀ (D : D7) (m n : ℕ) (ε : D.what₂.Tau → Fin m → Bool) (p q : D.what₂.Tau → ℕ) (ap am : D.what₂.Tau → ℕ → ℕ) (x₁ x₂ x₃ : D.what₂.Tau → ℤ), m ≤ n → (∀ τ, p τ + q τ = m) → (∀ τ a, ε τ a = decide ((a : ℕ) < p τ)) → (∀ τ a b, a ≤ b → b < p τ → ap τ b ≤ ap τ a) → (∀ τ a b, a ≤ b → b < q τ → am τ b ≤ am τ a) → ∃ (κ : D.what₂.Tau → Matrix (Fin m) (Fin m) ℂ) (Δ' : PolF D m n), (∀ τ, κ τ ∈ Formalism.REAL.Kset (ε τ)) ∧ fact ε x₁ x₂ x₃ κ 1 Δ' = delta p q ap am ∧ IsBotFam ε (factK n ε x₁ x₂ x₃) (fun τ a => -(wtK (p τ) (ap τ) (am τ) (x₁ τ) (x₂ τ) a : ℝ)) Δ' ∧ IsBotFam (fun _ => allPos n) (factU ε x₁ x₂ x₃) (fun τ j => (wtU (p τ) (q τ) (ap τ) (am τ) (x₃ τ) j : ℝ)) Δ' := by
  first | exact @GlobalTheory.JointHarm.MinorBottom.exists_joint_bottom | exact GlobalTheory.JointHarm.MinorBottom.exists_joint_bottom | (intros; apply GlobalTheory.JointHarm.MinorBottom.exists_joint_bottom <;> assumption)
