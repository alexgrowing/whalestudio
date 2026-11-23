import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

noncomputable section

namespace GlobalTheory.ThKLin

theorem I_linear : GlobalTheory.ThK.WeilConv → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d)
    (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' → d + 2 * min r s < 2 * n ∨ min r s = 0 →
    ∀ h, ∀ Φ ∈ schA F (Fin n × Fin d), ∀ Ψ ∈ schA F (Fin n × Fin d), ∀ c : ℂ, M.I om (c • Φ + Ψ) h = c * M.I om Φ h + M.I om Ψ h := by
  intro hW F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP hr h Φ hΦ Ψ hΨ c
  have hC := (hW F E σ B n d X W M χX χW om r s r' s' hP hr).1
  have hpres : ∀ x, ∀ Φ₀ ∈ schA F (Fin n × Fin d), om x Φ₀ ∈ schA F (Fin n × Fin d) :=
    hP.weil.isUSplitting.pres
  have e : ∀ g, theta om (c • Φ + Ψ) g h = c * theta om Φ g h + theta om Ψ g h := by
    intro g
    have hA := summable_of_mem_schA F (hpres (g, h) Φ hΦ)
    have hB := summable_of_mem_schA F (hpres (g, h) Ψ hΨ)
    simp only [theta, map_add, map_smul, thetaSum, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [(hA.mul_left c).tsum_add hB, tsum_mul_left]
  simp only [Model.I, e]
  rw [integral_add (((hC Φ hΦ).1 h).const_mul c) ((hC Ψ hΨ).1 h), integral_const_mul]

end GlobalTheory.ThKLin
