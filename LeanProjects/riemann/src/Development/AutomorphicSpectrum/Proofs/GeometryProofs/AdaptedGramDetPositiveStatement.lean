import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.AdaptedGramDetPositive
import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsAdapted
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GramDetNeZeroOfIndep
open NumberField TensorProduct Matrix GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adapted_gram_det_positive : ∀ (E L Ψ : Type) [Field E] [NumberField E] [Field L] [NumberField L] (V : Type) [AddCommGroup V] [Module L V] [Module (𝓞 L) V] [IsScalarTower (𝓞 L) L V] (A : LinPt E L Ψ V) (s : Ψ ⊕ Ψ) (r k : ℕ) (v : Fin r → V) (q : Fin k → A.Λ), IsOFamily A.ρ A.I v → A.IsAdapted s v q → (∀ i, (q i : V) ∈ A.eig s) → ∀ e : L →+* ℂ, 0 < A.gramDet e q := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.gramDet_pos_of_adapted | exact GlobalTheory.CompanionTheory.Ar.Cusp.gramDet_pos_of_adapted | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.gramDet_pos_of_adapted <;> assumption)
