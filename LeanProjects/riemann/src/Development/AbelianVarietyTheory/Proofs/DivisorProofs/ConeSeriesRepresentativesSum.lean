import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisAtMinusRho
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocUnifSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemCtIntSub
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DisjointLineMid
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NeOfReNe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsShear
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HaarStabilizerPeriodCaseBThird
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open GlobalTheory.ConeSmallMidJB

noncomputable section

namespace GlobalTheory.ConeSmallSerInt

open GlobalTheory.ConeSmallSer GlobalTheory.ConeSmallCT

theorem summable_norm_le_of_distinct : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ)
    (J : Matrix (Fin n) (Fin n) E) (x : Fin n → E) (T : Set (UA σ J)), GlobalTheory.ConeSmallCT.IsReps T x →
    ∀ f : UA σ J → ℂ, (∀ p ∈ ratU σ J, GlobalTheory.ConeSmallSer.StabLn x p → ∀ h, f (p * h) = f h) →
    ∀ (S : Type) (φ : S → UA σ J), (∀ s, φ s ∈ ratU σ J) → (∀ s s', GlobalTheory.ConeSmallSer.StabLn x (φ s * (φ s')⁻¹) → s = s') →
    ∀ (g : UA σ J) (C : ℝ), Summable (fun t : T => ‖f (t.1 * g)‖) → ∑' t : T, ‖f (t.1 * g)‖ ≤ C →
      Summable (fun s => ‖f (φ s * g)‖) ∧ ∑' s, ‖f (φ s * g)‖ ≤ C := by
  intro F E _ _ _ _ _ σ n J x T hT f hinv S φ hφ hdist g C hsum hC
  have hr : ∀ s, ∃ t, t ∈ T ∧ StabLn x (φ s * t⁻¹) := fun s => (hT.2 _ (hφ s)).exists
  choose r hrT hrs using hr
  let ρ : S → T := fun s => ⟨r s, hrT s⟩
  have hinj : Function.Injective ρ := by
    intro s₁ s₂ h
    have h' : r s₁ = r s₂ := congrArg Subtype.val h
    have h3 := stabLn_mul (hrs s₁) (stabLn_inv (hrs s₂))
    have e : φ s₁ * (r s₁)⁻¹ * (φ s₂ * (r s₂)⁻¹)⁻¹ = φ s₁ * (φ s₂)⁻¹ := by rw [h']; group
    rw [e] at h3
    exact hdist s₁ s₂ h3
  have heq : (fun s => ‖f (φ s * g)‖) = (fun t : T => ‖f (t.1 * g)‖) ∘ ρ := by
    funext s
    have e : φ s * g = (φ s * (r s)⁻¹) * (r s * g) := by group
    simp only [Function.comp_apply, ρ]
    rw [e, hinv _ (mul_mem (hφ s) (inv_mem (hT.1 (hrT s)))) (hrs s)]
  have hs : Summable ((fun t : T => ‖f (t.1 * g)‖) ∘ ρ) := hsum.comp_injective hinj
  have hle : ∑' s, ((fun t : T => ‖f (t.1 * g)‖) ∘ ρ) s ≤ ∑' t : T, ‖f (t.1 * g)‖ :=
    hs.tsum_le_tsum_of_inj ρ hinj (fun _ _ => norm_nonneg _) (fun _ => le_rfl) hsum
  rw [heq]
  exact ⟨hs, hle.trans hC⟩

end GlobalTheory.ConeSmallSerInt

end
