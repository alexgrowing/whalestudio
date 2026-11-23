import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemStabLocalizedStdLatticeIffIntegralGL
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExtXCastAdd
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RootExchangeUnipotentHaarAndModulus
open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.VolBridge
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_stabLocalizedStdLattice_iff_integralGL : ∀ {E k : Type} [Field E] [NumberField E] [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (P : HeightOneSpectrum (𝓞 E)) (ι : E →+* k), (∀ a, ι a ∈ 𝒪[k] ↔ IntAt P a) → ∀ {A : Type} [Fintype A] [DecidableEq A] {M : ℕ} (e : A ≃ Fin M) (x : Sp E M ≃ₗ[E] Sp E M), x ∈ stabL E M (stdAt E M P) ↔ locHom ι e x ∈ KO k A := by
  first | exact @GlobalTheory.VolBridge.mem_stabL_stdAt_iff_locHom_mem_KO | exact GlobalTheory.VolBridge.mem_stabL_stdAt_iff_locHom_mem_KO | (intros; apply GlobalTheory.VolBridge.mem_stabL_stdAt_iff_locHom_mem_KO <;> assumption)
