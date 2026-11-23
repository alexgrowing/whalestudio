import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteFreeLocalChart
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaOn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompReixMemAdm
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.Doubling GlobalTheory.ThK.Bot GlobalTheory.DblBox
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weil_doubled_darboux_coordinates : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (a b : ℕ) (JA : Matrix (Fin a) (Fin a) E) (JB : Matrix (Fin b) (Fin b) E) (ε : ℤˣ), (∀ i j, σ (JB j i) = ((ε : ℤ) : E) * JB i j) → JB.det ≠ 0 →
    ∀ (ψ : AddChar (AF F) ℂ), IsStd ψ → ∀ (κ : Type) [Fintype κ]
      (dd : Darboux (symp (R := AF F) (cA σ) (-1) (incM F JA) (GlobalTheory.WeilM.dbl (incM F JB))) κ)
      (omd omd₁ : UG (cA σ) (GlobalTheory.WeilM.dbl (incM F JB)) →* Module.End ℂ ((κ → AF F) → ℂ)),
    IsSplitting (adeleClass F) ψ dd (actB (cA σ)) omd → IsContOn (adeleClass F) omd →
    IsSplitting (adeleClass F) ψ dd (actB (cA σ)) omd₁ → IsContOn (adeleClass F) omd₁ →
    ∀ l : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ, (∃ φ ∈ schA F κ, l φ ≠ 0) →
    (∀ (p : UG (cA σ) (GlobalTheory.WeilM.dbl (incM F JB))) (t : GL (Fin b) (AE F E)),
      (p.1.1 : Matrix _ _ (AE F E)) * diagCols (Fin b) = diagCols (Fin b) * t.1 → ∀ φ ∈ schA F κ, l (omd p φ) = l (omd₁ p φ)) →
    ∀ p, ∀ φ ∈ schA F κ, omd p φ = omd₁ p φ := by
  first | exact @GlobalTheory.SplitUnique.splitting_unique | exact GlobalTheory.SplitUnique.splitting_unique | (intros; apply GlobalTheory.SplitUnique.splitting_unique <;> assumption)
