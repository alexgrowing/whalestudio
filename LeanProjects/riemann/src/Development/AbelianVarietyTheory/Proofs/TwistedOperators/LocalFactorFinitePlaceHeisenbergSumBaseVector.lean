import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RestrictedTensorBasePointNormSq
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsIntOv
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HasDerivAtZeroAndIsTheta
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisThetaLaws
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaInnerProductHermitianStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LocalFactorMemSpanLocalHeisenbergTranslatesStatement

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PlaceTensorFin

theorem isLocOp_of_mem_span {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {μ : Measure (WO S T)} {𝓕 : Set (WO S T)}
    (hψ : IsStdChar D ψ (-1)) (hμ : IsCovolOne (ratL T S) μ 𝓕) {f₀ : WO S T → ℂ} (h₀ : IsThetaFunO ψ S T f₀) (p : Place D)
    {x : WO S T → ℂ} (hx : x ∈ Submodule.span ℂ (Set.range fun w : WO S T => heisO ψ S T (wAt p w) f₀)) :
    IsThetaFunO ψ S T x ∧ IsLocOp ψ S T μ 𝓕 f₀ p x := by
  have hh := (GlobalTheory.HeisThetaLaws.heis_theta_laws D ψ hψ S T).1
  have ip := GlobalTheory.T.theta_inner_product_hermitian D ψ S T μ 𝓕 hψ hμ
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨w, rfl⟩ := hy
    exact ⟨hh _ _ h₀, fun φ => φ w, fun _ _ => rfl, fun f hf => ⟨_, hh (wAt p w) f hf, fun _ _ => rfl⟩, fun _ _ => rfl⟩
  | zero =>
    have hz : ∀ g, ipO μ 𝓕 (0 : WO S T → ℂ) g = 0 := fun g => by simp [ipO]
    exact ⟨GlobalTheory.WeilVacMove.isTheta_zero, fun _ => 0, fun _ _ => by simp,
      fun f _ => ⟨0, GlobalTheory.WeilVacMove.isTheta_zero, fun g _ => hz g⟩, fun g _ => hz g⟩
  | add y z _ _ hy hz =>
    obtain ⟨ty, L, L1, L2, L3⟩ := hy
    obtain ⟨tz, M, M1, M2, M3⟩ := hz
    refine ⟨GlobalTheory.WeilVacMove.isTheta_add ty tz, fun φ => L φ + M φ, fun c φ => ?_, fun f hf => ?_, fun g hg => ?_⟩
    · simp only [L1, M1, mul_add]
    · obtain ⟨a, ta, ha⟩ := L2 f hf
      obtain ⟨b, tb, hb⟩ := M2 f hf
      refine ⟨a + b, GlobalTheory.WeilVacMove.isTheta_add ta tb, fun g hg => ?_⟩
      rw [((ip a g ta hg).2.2.2.1 b tb).1, ha g hg, hb g hg]
    · rw [((ip y g ty hg).2.2.2.1 z tz).1, L3 g hg, M3 g hg]
  | smul c y _ hy =>
    obtain ⟨ty, L, L1, L2, L3⟩ := hy
    refine ⟨GlobalTheory.WeilVacMove.isTheta_smul c ty, fun φ => c * L φ, fun d φ => ?_, fun f hf => ?_, fun g hg => ?_⟩
    · simp only [L1]
      ring
    · obtain ⟨a, ta, ha⟩ := L2 f hf
      refine ⟨c • a, GlobalTheory.WeilVacMove.isTheta_smul c ta, fun g hg => ?_⟩
      rw [((ip a g ta hg).2.2.1 c).1, ha g hg]
    · rw [((ip y g ty hg).2.2.1 c).1, L3 g hg]

theorem isLocOp_of_isLocal_fin : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (f₀ : WO S T → ℂ) (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsBase ψ θ S T sS sT ΛS ΛT f₀ → IsCovolOne (ratL T S) μ 𝓕 → ∀ (v : FinPl D) (x : WO S T → ℂ), IsLocal ψ θ S T sS sT ΛS ΛT (.inl v) x → IsLocOp ψ S T μ 𝓕 f₀ (.inl v) x :=
  fun D ψ θ S T sS sT ΛS ΛT f₀ _ _ hb hμ v x hx =>
    (isLocOp_of_mem_span (base_std hb) hμ (base_theta hb) (.inl v)
      (GlobalTheory.T.localFactor_mem_span_localHeisenbergTranslates D ψ θ S T sS sT ΛS ΛT f₀ hb v x hx)).2

end GlobalTheory.PlaceTensorFin
