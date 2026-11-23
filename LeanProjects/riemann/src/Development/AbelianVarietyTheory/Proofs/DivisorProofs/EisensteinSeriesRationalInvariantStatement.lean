import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisensteinSeriesRationalInvariant
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisAtMinusRho
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocUnifSum
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eisenstein_series_rational_invariant : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
    {J : Matrix (Fin n) (Fin n) E} (K : Subgroup (UA σ J)) (x : Fin n → E) (Eis : ℂ → UA σ J → ℂ),
    GlobalTheory.ConeSmall.IsEisSer K x Eis → ∀ s : ℂ, ((n : ℝ) - 1) / 2 < s.re → ∀ γ ∈ ratU σ J, ∀ g, Eis s (γ * g) = Eis s g := by
  first | exact @GlobalTheory.ConeSmall.eis_rat_left_invariant | exact GlobalTheory.ConeSmall.eis_rat_left_invariant | (intros; apply GlobalTheory.ConeSmall.eis_rat_left_invariant <;> assumption)
