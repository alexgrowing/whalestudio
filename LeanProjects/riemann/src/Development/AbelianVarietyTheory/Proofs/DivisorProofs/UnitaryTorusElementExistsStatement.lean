import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryTorusElementExists
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MajINonneg
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThKSoDecay GlobalTheory.ThKTorus
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_torus_element_exists : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n : ℕ) (X : Spc F E n) (r s : ℕ), B.IsGood σ → X.IsHerm σ B r s → ∀ (q : ℕ) (x y : Fin q → Fin n → E),
    IsFrameU σ X.J x y → ∀ t : Fin q → ℝ, (∀ i, 0 < t i) → ∃ a : UA σ X.J, IsTorusU x y t a := by
  first | exact @GlobalTheory.FrameTorus.exists_isTorusU | exact GlobalTheory.FrameTorus.exists_isTorusU | (intros; apply GlobalTheory.FrameTorus.exists_isTorusU <;> assumption)
