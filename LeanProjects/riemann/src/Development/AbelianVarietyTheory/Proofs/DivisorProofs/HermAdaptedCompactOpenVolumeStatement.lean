import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermAdaptedCompactOpenVolume
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
theorem _root_.GlobalTheory.T.herm_adapted_compact_open_volume : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n n₁ : ℕ) (X : Spc F E n) (X₁ : Spc F E n₁) (r s : ℕ) (H : Plane E n n₁) (j₀ j₁ : ℕ) (K : Subgroup (UA σ X.J)),
    B.IsGood σ → X.IsHerm σ B r s → H.IsAdapted σ B X X₁ j₀ j₁ → IsCompact (K : Set (UA σ X.J)) →
    ∀ (v : Pl F) (Ω : Set (KAt K (evFin F v) × idelesAt E (evFin F v))), IsOpen Ω →
      (∀ p : KAt K (evFin F v) × idelesAt E (evFin F v), mat p.1.1 *ᵥ incV F H.x = (p.2.1 : AE F E) • incV F H.x → p ∈ Ω) →
      ∃ U ∈ 𝓝 (0 : Fin n → Fv F v ⊗[F] E), ∃ C : Set (idelesAt E (evFin F v)), IsCompact C ∧
        ∀ p : KAt K (evFin F v) × idelesAt E (evFin F v), GlobalTheory.ConeBump.disp v H.x p.1.1 p.2.1 ∈ U → p ∈ Ω ∧ p.2 ∈ C := by
  first | exact @GlobalTheory.ConeBump.disp_proper_near | exact GlobalTheory.ConeBump.disp_proper_near | (intros; apply GlobalTheory.ConeBump.disp_proper_near <;> assumption)
