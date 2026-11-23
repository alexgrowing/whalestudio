import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaStabilizerExistsStatement
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open Classical

namespace GlobalTheory.StabCpt

theorem isCompact_of_isStab : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n : ℕ) (X : Spc F E n) (r s : ℕ) (K : Subgroup (UA σ X.J)),
    B.IsGood σ → X.IsHerm σ B r s → IsStab B K → IsCompact (K : Set (UA σ X.J)) := by
  intro hKP F E _ _ _ _ _ σ B n X r s K hB hX hK
  obtain ⟨K', _, _, hK', hc, -, -⟩ := GlobalTheory.T.theta_stabilizer_exists hKP.base F E σ B n X r s hB hX
  have e : K = K' := by
    ext g
    rw [hK g, hK' g]
  subst e
  exact hc

end GlobalTheory.StabCpt
