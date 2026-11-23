import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DarbouxCoordinatesDiagonalVanishing
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaOn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompReixMemAdm
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.Doubling GlobalTheory.ThK.Bot GlobalTheory.DblBox
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.darboux_coordinates_diagonal_vanishing : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (J : Matrix (Fin n) (Fin n) E) (X₂ : Spc F E (n + n)), X₂.J = dblGram finSumFinEquiv J →
    ∀ (W : Spc F E d) (co : Darboux (symp (R := AF F) (cA σ) (-1) (incM F X₂.J) (incM F W.J)) (Fin (n + n) × Fin d)),
    (∀ u, (∀ j, uᵀ j ∈ diagSub (AE F E) finSumFinEquiv) → (co.e u).1 = 0) →
    ∀ (χ₁ χ : Chr F E) (om₂ : Rep σ X₂ W), IsUWeilPair (cA σ) (adeleClass F) B.ψ (-1) (incM F X₂.J) (incM F W.J) co χ₁ χ om₂ →
    (∀ p : siegelOf finSumFinEquiv (UG (cA σ) (incM F X₂.J)).subtype, ∀ φ ∈ schA F (Fin (n + n) × Fin d),
      om₂ ((p : UA σ X₂.J), 1) φ 0 = (χ (aOf finSumFinEquiv (UG (cA σ) (incM F X₂.J)).subtype p) : ℂ) *
        GlobalTheory.Doubling.npow (absE F E (aOf finSumFinEquiv (UG (cA σ) (incM F X₂.J)).subtype p)) ((d : ℂ) / 2) * φ 0) ∧
    ∀ K : Subgroup (UA σ X₂.J), ∀ Φ ∈ schA F (Fin (n + n) × Fin d),
      FiniteDimensional ℂ (Submodule.span ℂ {Ψ | ∃ k ∈ K, Ψ = om₂ (k, 1) Φ}) →
      (fun g => om₂ (g, 1) Φ 0) ∈ degPSOf finSumFinEquiv (UG (cA σ) (incM F X₂.J)).subtype (absE F E) K χ (((d : ℂ) - (n : ℂ)) / 2) := by
  first | exact @GlobalTheory.DblEvalLeft.siegel_law_and_mem_degPSOf | exact GlobalTheory.DblEvalLeft.siegel_law_and_mem_degPSOf | (intros; apply GlobalTheory.DblEvalLeft.siegel_law_and_mem_degPSOf <;> assumption)
