import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

namespace GlobalTheory.SiegelSet

theorem rapidDecay_qht : GlobalTheory.Published.SiegelSetUnitary → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (c₀ : E), c₀ ≠ 0 → IsHermND σ (c₀ • J.map σ) →
    ∀ (φ : UA σ J → ℂ) (φ' : GAd σ (c₀ • J.map σ) → ℂ), (∀ (g : UA σ J) (g' : GAd σ (c₀ • J.map σ)), g.1 = g'.1 → φ' g' = φ g) →
    GlobalTheory.SiegelSet.IsSmoothModerate σ (c₀ • J.map σ) φ' → GlobalTheory.SiegelSet.IsCuspidal σ (c₀ • J.map σ) φ' →
    ∀ N : ℕ, ∃ C : ℝ, ∀ h, ‖φ h‖ * (qht h : ℝ) ^ N ≤ C := by
  intro hP F E _ _ _ _ _ σ hCM n J c₀ hc₀ hJ' φ φ' hφ hsm hcusp N
  obtain ⟨S, -, hcov, -, -, hφS⟩ := exists_cover (J := c₀ • J.map σ) hP hCM hJ'
  obtain ⟨C, hC⟩ := (hφS φ' hsm hcusp N).1
  refine ⟨C, fun h => ?_⟩
  have heq : UG (cA σ) (incM F J) = HR (AF F) σ (c₀ • J.map σ) := ug_eq_hr (sigma_sigma hCM) hc₀
  let g' : GAd σ (c₀ • J.map σ) := ⟨h.1, heq.le h.2⟩
  obtain ⟨γ, hγ, s, hs, hgs⟩ := hcov g'
  have h1 : φ h = φ' s := by
    rw [← hφ h g' rfl, hgs, hsm.left γ hγ s]
  obtain ⟨u, -, hu⟩ := hγ
  let δ : UA σ J := ⟨(γ⁻¹).1, heq.ge (γ⁻¹).2⟩
  have hδ : δ ∈ ratU σ J := by
    show (γ⁻¹).1 ∈ (Matrix.GeneralLinearGroup.map (n := Fin n) (inclR (F := F) (E := E) (AF F))).range
    refine ⟨u⁻¹, ?_⟩
    rw [map_inv]
    show _ = (γ.1)⁻¹
    exact congrArg (·⁻¹) hu
  have h2 : (δ * h).1 = s.1 := by
    show (γ⁻¹).1 * h.1 = s.1
    have : h.1 = (γ * s).1 := congrArg Subtype.val hgs
    rw [this]
    exact inv_mul_cancel_left γ.1 s.1
  have h3 : qht h ≤ height σ (c₀ • J.map σ) s := by
    refine (ciInf_le (OrderBot.bddBelow _) ⟨δ, hδ⟩).trans (le_of_eq ?_)
    show heightGL F (δ * h).1 = heightGL F ((matHom (AF F) σ (c₀ • J.map σ)) s)
    rw [h2]; rfl
  rw [h1]
  refine le_trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (NNReal.coe_nonneg _) (NNReal.coe_le_coe.2 h3) N)
    (norm_nonneg _)) (hC s hs)

end GlobalTheory.SiegelSet
