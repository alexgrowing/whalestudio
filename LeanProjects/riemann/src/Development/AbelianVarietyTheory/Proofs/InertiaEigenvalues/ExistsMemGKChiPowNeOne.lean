import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Development.AbelianVarietyTheory.Definitions.Foundations.HTBasis
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExpStar
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinrankCyclotomicExtAndCyclotomicCharSurjective

namespace GlobalTheory.Cyc

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation TensorProduct

private lemma norm_one_add_prime_padic (l : ℕ) [Fact l.Prime] : ‖(1 : ℚ_[l]) + l‖ = 1 := by
  have h1 : ‖(l : ℚ_[l])‖ < 1 := Padic.norm_p_lt_one
  have hne : ‖(1 : ℚ_[l])‖ ≠ ‖(l : ℚ_[l])‖ := by rw [norm_one]; exact ne_of_gt h1
  first
  | rw [padicNormE.add_eq_max_of_ne hne, norm_one]; exact max_eq_left h1.le
  | rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hne, norm_one]; exact max_eq_left h1.le

private lemma zmod_pow_ne_one_of_pow_mod_ne_one (l : ℕ) [Fact l.Prime] (n : ℕ) (hn : 0 < n) :
    ((1 : ℚ_[l]) + l) ^ n ≠ 1 := by
  have hl : 2 ≤ l := (Fact.out : l.Prime).two_le
  have key : (1 + l) ^ n ≠ 1 := (Nat.one_lt_pow (by omega) (by omega)).ne'
  intro h
  apply key
  exact_mod_cast h

theorem exists_mem_GK_chi_pow_ne_one : ∀ (l : ℕ) [Fact l.Prime] (χ : GQ l →* ℚ_[l]ˣ), IsCyc χ →
    ∀ (K : FinExt l) (e : ℕ), 0 < e → ∃ g ∈ GK K, (χ g : ℚ_[l]) ^ e ≠ 1 := by
  intro l _ χ hχ K e he

  obtain ⟨σ, -, hσ⟩ := exists_chi_eq K χ hχ _ (norm_one_add_prime_padic l)
  have hK : FiniteDimensional ℚ_[l] ↥K.1 := K.2

  let f : ℕ → (↥K.1 →ₐ[ℚ_[l]] Om l) := fun n =>
    (AlgEquiv.toAlgHom (σ ^ n : Om l ≃ₐ[ℚ_[l]] Om l)).comp (IntermediateField.val K.1)
  obtain ⟨i, j, hij, hfij⟩ := Finite.exists_ne_map_eq_of_infinite f

  have key : ∀ a b : ℕ, a < b → f a = f b → ∃ g ∈ GK K, (χ g : ℚ_[l]) ^ e ≠ 1 := by
    intro a b hab hfab
    refine ⟨σ ^ (b - a), ?_, ?_⟩
    · unfold GK
      rw [IntermediateField.mem_fixingSubgroup_iff]
      intro x hx
      have h1 : (σ ^ a) x = (σ ^ b) x :=
        congrArg (fun φ : ↥K.1 →ₐ[ℚ_[l]] Om l => φ ⟨x, hx⟩) hfab
      have hb : σ ^ b = σ ^ a * σ ^ (b - a) := by
        rw [← pow_add]
        congr 1
        omega
      rw [hb, AlgEquiv.mul_apply] at h1
      exact ((σ ^ a).injective h1).symm
    · rw [map_pow, Units.val_pow_eq_pow_val, hσ, ← pow_mul]
      exact zmod_pow_ne_one_of_pow_mod_ne_one l _ (Nat.mul_pos (by omega) he)
  rcases lt_or_gt_of_ne hij with h | h
  · exact key i j h hfij
  · exact key j i h hfij.symm

end GlobalTheory.Cyc
