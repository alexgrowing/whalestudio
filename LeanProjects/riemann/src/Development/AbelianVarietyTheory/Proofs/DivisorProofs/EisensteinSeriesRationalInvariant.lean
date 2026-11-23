import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisAtMinusRho
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocUnifSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConeRepresentatives

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

namespace GlobalTheory.ConeSmall

theorem eis_rat_left_invariant : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} {n : ℕ}
    {J : Matrix (Fin n) (Fin n) E} (K : Subgroup (UA σ J)) (x : Fin n → E) (Eis : ℂ → UA σ J → ℂ),
    GlobalTheory.ConeSmall.IsEisSer K x Eis → ∀ s : ℂ, ((n : ℝ) - 1) / 2 < s.re → ∀ γ ∈ ratU σ J, ∀ g, Eis s (γ * g) = Eis s g := by
  intro F E _ _ _ _ _ σ n J K x Eis hE s hs γ₀ hγ₀ g
  obtain ⟨hf, -, -, hsum⟩ := hE
  obtain ⟨T, hTsub, hT⟩ := GlobalTheory.ConeSmallCT.exists_isReps F E σ n J x
  let T' : Set (UA σ J) := (· * γ₀) '' T
  have hT'sub : T' ⊆ ratU σ J := by
    rintro _ ⟨t, ht, rfl⟩
    exact mul_mem (hTsub ht) hγ₀
  have hT' : ∀ γ ∈ ratU σ J, ∃! t, t ∈ T' ∧ ∃ l : (AE F E)ˣ,
      mat (γ * t⁻¹) *ᵥ incV F x = l.1 • incV F x := by
    intro γ hγ
    obtain ⟨t, ⟨htT, hl⟩, huniq⟩ := hT (γ * γ₀⁻¹) (mul_mem hγ (inv_mem hγ₀))
    refine ⟨t * γ₀, ⟨⟨t, htT, rfl⟩, ?_⟩, ?_⟩
    · have e1 : γ * (t * γ₀)⁻¹ = γ * γ₀⁻¹ * t⁻¹ := by group
      rw [e1]
      exact hl
    · rintro _ ⟨⟨u, huT, rfl⟩, hu⟩
      have e2 : γ * (u * γ₀)⁻¹ = γ * γ₀⁻¹ * u⁻¹ := by group
      rw [e2] at hu
      rw [huniq u ⟨huT, hu⟩]
  have h1 := hsum T hTsub hT s hs (γ₀ * g)
  have h2 := hsum T' hT'sub hT' s hs g
  let e : T ≃ T' := Equiv.Set.image (· * γ₀) T (mul_left_injective γ₀)
  have h3 : HasSum (fun t : T' => (hf (t.1 * g) : ℂ) ^ (s + ((n : ℂ) - 1) / 2)) (Eis s (γ₀ * g)) := by
    rw [← e.hasSum_iff]
    convert h1 using 3 with t
    show ((hf ((t.1 * γ₀) * g) : ℝ) : ℂ) ^ (s + ((n : ℂ) - 1) / 2) = _
    rw [mul_assoc]
  exact h3.unique h2

end GlobalTheory.ConeSmall

end
