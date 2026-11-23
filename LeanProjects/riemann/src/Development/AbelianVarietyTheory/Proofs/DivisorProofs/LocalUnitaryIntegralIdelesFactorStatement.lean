import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalUnitaryIntegralIdelesFactor
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_unitary_integral_ideles_factor : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {n : ℕ} {X : Spc F E n} (K : Subgroup (UA σ X.J)), IsClosed (K : Set (UA σ X.J)) → ∀ (v : Pl F) (μK : Measure (KAt K (evFin F v))), IsNormK K (evFin F v) μK → ∀ (μE : Measure (idelesAt E (evFin F v))), IsNormE E v μE → ∀ (g : UA σ X.J × (AE F E)ˣ → ℝ) (r : idelesAt E (evFin F v) → ℝ), (∀ k ∈ KAt K (evFin F v), ∀ (l : (AE F E)ˣ) (hl : l ∈ idelesAt E (evFin F v)), g (k, l) = r ⟨l, hl⟩) → ∫ q, g q ∂((μK.map Subtype.val).prod (μE.map Subtype.val)) = ∫ l, r l ∂μE := by
  first | exact @GlobalTheory.ThK.EulerUnr.integral_KAt_idelesAt_snd | exact GlobalTheory.ThK.EulerUnr.integral_KAt_idelesAt_snd | (intros; apply GlobalTheory.ThK.EulerUnr.integral_KAt_idelesAt_snd <;> assumption)
