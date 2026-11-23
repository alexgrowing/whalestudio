import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsAuxiliaryHeckeCharacter
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ToricPropertiesAllOfBound

noncomputable section

open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.MainNotions Formalism.FrobeniusOrbits Formalism.L2.Host GlobalTheory.CMVal GlobalTheory.ToricDenom GlobalTheory.LamTie

namespace GlobalTheory.ToricValue

theorem exists_heckeL_toricSum : ∀ (R : Ranks) (H : Formalism.BasicNotions.Host R) (I : Type) [Fintype I] (φ : I → H.E →+* ℂ) (s : ℕ) (κ : I → ℕ) (𝔣 : Ideal (OF H.E)) (χ : Formalism.L2.Host.HChar H.E), IsHostDatum H φ s κ 𝔣 χ → ∃ Λ : ℂ → ℂ, IsHeckeL χ Λ ∧ Λ s ≠ 0 ∧ ∀ T : ℂ, IsToricSum φ s κ 𝔣 χ T ↔ T = Λ s := by
  intro R H I _ φ s κ 𝔣 χ hD
  have : IsCMField H.E := H.isCMField_hostE
  obtain ⟨hφ, -, hs, -, hb, hχ⟩ := hD
  have hn := GlobalTheory.ToricAssembly.not_isNormPow hb hχ
  obtain ⟨Λ, hΛ⟩ := GlobalTheory.HeckeOne.entire_of_not_normPow hχ.1 hn
  have h0 : Λ s ≠ 0 := GlobalTheory.HeckePartial.IsHeckeL.ne_zero_of_one_le hχ.1 hn hΛ (by exact_mod_cast hs)
  obtain ⟨P₀⟩ : Nonempty (HeightOneSpectrum (𝓞 H.E)) := by
    obtain ⟨M, hM⟩ := Ideal.exists_maximal (𝓞 H.E)
    exact ⟨⟨M, hM.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hM (RingOfIntegers.not_isField _)⟩⟩
  have t1 := GlobalTheory.ToricAssembly.toricSumFormula _ I φ hφ s κ 𝔣 ∅ χ (fun _ => P₀) Λ (GlobalTheory.ToricDenomBridge.host_unramFin H) hs hb
    (fun _ h => absurd h (Finset.notMem_empty _)) hχ (fun _ h => absurd h (Finset.notMem_empty _)) hΛ
  rw [Finset.filter_empty, Finset.prod_empty, mul_one] at t1
  have e : condQ 𝔣 ∅ = 𝔣 := by simp [condQ]
  rw [e] at t1
  exact ⟨Λ, hΛ, h0, fun T => ⟨fun h => h.unique t1, fun h => h ▸ t1⟩⟩

end GlobalTheory.ToricValue
