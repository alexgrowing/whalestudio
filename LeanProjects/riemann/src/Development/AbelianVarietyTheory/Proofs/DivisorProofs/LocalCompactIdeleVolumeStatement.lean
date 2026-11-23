import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalCompactIdeleVolume
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
theorem _root_.GlobalTheory.T.local_compact_idele_volume : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ)
    (X : Spc F E n) (x₀ : Fin n → E) (K : Subgroup (UA σ X.J)) (v : Pl F) (μK : Measure (KAt K (evFin F v)))
    (μ : Measure (idelesAt E (evFin F v))), IsNormK K (evFin F v) μK → IsNormE E v μ →
    ∀ V : Set (Fin n → Fv F v ⊗[F] E), IsOpen V → IsClosed V → (0 : Fin n → Fv F v ⊗[F] E) ∈ V →
    ∀ C : Set (idelesAt E (evFin F v)), IsCompact C →
      (∀ p : KAt K (evFin F v) × idelesAt E (evFin F v), GlobalTheory.ConeBump.disp v x₀ p.1.1 p.2.1 ∈ V → p.2 ∈ C) →
      (∫ k, ∫ l, V.indicator (fun _ => (1 : ℂ)) (GlobalTheory.ConeBump.disp v x₀ k.1 l.1) ∂μ ∂μK) ≠ 0 := by
  first | exact @GlobalTheory.ConeBump.integral_indicator_disp_ne_zero | exact GlobalTheory.ConeBump.integral_indicator_disp_ne_zero | (intros; apply GlobalTheory.ConeBump.integral_indicator_disp_ne_zero <;> assumption)
