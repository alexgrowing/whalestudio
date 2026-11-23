import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DarbouxSymplecticDoubledHermitian
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAut
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegFamOfContinuousAt
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling GlobalTheory.ThK.DblKer
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.darboux_symplectic_doubled_hermitian : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ B : Base F E, IsCharAF F B.ψ → ∀ (n m : ℕ) (W : Spc F E n), (∀ i j, σ (W.J j i) = -W.J i j) →
    ∀ W₂ : Spc F E (n + n), W₂.J = dblGram finSumFinEquiv W.J →
    ∀ X : Spc F E m, (∀ i j, σ (X.J j i) = X.J i j) →
    ∀ co : Darboux (symp (R := AF F) (cA σ) (-1) (incM F X.J) (incM F W₂.J)) (Fin m × Fin (n + n)),
      (∀ x : Matrix (Fin m) (Fin (n + n)) E, ∃ y z : Fin m × Fin (n + n) → F,
        co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
      (∀ u, (∀ i, u i ∈ diagSub (AE F E) finSumFinEquiv) → (co.e u).1 = 0) →
      (∀ u, (∀ i, u i ∈ antiSub (AE F E) finSumFinEquiv) → (co.e u).2 = 0) →
    ∀ χ : Chr F E, IsHecke F E χ → ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χ m →
    ∀ om₂ : Rep σ X W₂, IsUWeilPair (cA σ) (adeleClass F) B.ψ (-1) (incM F X.J) (incM F W₂.J) co χ 1 om₂ →
    ∀ K : Subgroup (UA σ W₂.J), IsStab B K → IwasawaOf finSumFinEquiv (UG (cA σ) (incM F W₂.J)).subtype (absE F E) K →
    ∀ Φ ∈ schA F (Fin m × Fin (n + n)), FiniteDimensional ℂ (Submodule.span ℂ {Ψ | ∃ k ∈ K, Ψ = om₂ (1, k) Φ}) →
      (fun g => om₂ (1, g) Φ 0) ∈ degPSOf finSumFinEquiv (UG (cA σ) (incM F W₂.J)).subtype (absE F E) K χ
        (((m : ℂ) - (n : ℂ)) / 2) := by
  first | exact @GlobalTheory.DblEvalLaw.apply_mem_degPSOf | exact GlobalTheory.DblEvalLaw.apply_mem_degPSOf | (intros; apply GlobalTheory.DblEvalLaw.apply_mem_degPSOf <;> assumption)
