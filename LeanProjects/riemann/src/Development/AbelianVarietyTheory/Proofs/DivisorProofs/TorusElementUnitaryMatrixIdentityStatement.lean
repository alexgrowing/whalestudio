import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusElementUnitaryMatrixIdentity
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTorusUOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThKSoDecay
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torus_element_unitary_matrix_identity : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), (∀ i j, σ (J j i) = J i j) →
    ∀ (q : ℕ) (Xf Yf : Matrix (Fin n) (Fin q) E) (t : Fin q → ℝ) (a : GAd σ ((1 : E) • J.map σ)),
      GlobalTheory.SiegelSet.IsTorusElt σ ((1 : E) • J.map σ) Xf Yf t a →
      ∀ a' : UA σ J, (a' : GL (Fin n) (AE F E)) = HA.mat (AF F) σ ((1 : E) • J.map σ) a →
      IsTorusU (fun i k => Xf k i) (fun i k => Yf k i) t a' := by
  first | exact @GlobalTheory.TorusTranslate.isTorusU_of_isTorusElt | exact GlobalTheory.TorusTranslate.isTorusU_of_isTorusElt | (intros; apply GlobalTheory.TorusTranslate.isTorusU_of_isTorusElt <;> assumption)
