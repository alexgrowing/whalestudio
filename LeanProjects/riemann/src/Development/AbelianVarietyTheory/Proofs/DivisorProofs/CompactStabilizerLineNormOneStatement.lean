import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompactStabilizerLineNormOne
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConeFinIntEq
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.compact_stabilizer_line_norm_one : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ)
    (X : Spc F E n) (x₀ : Fin n → E) (K : Subgroup (UA σ X.J)), IsCompact (K : Set (UA σ X.J)) → x₀ ≠ 0 →
    ∀ (v : Pl F) (k : UA σ X.J), k ∈ KAt K (evFin F v) → ∀ l : (AE F E)ˣ,
      mat k *ᵥ incV F x₀ = (l : AE F E) • incV F x₀ → absE F E l = 1 := by
  first | exact @GlobalTheory.ConeNZ.absE_eq_one_of_eigen | exact GlobalTheory.ConeNZ.absE_eq_one_of_eigen | (intros; apply GlobalTheory.ConeNZ.absE_eq_one_of_eigen <;> assumption)
