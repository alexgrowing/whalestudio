import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LocallyCompactSpaceAxis
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EisensteinResidueLine
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeightFunctionScalingParabolicStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviNormalizesUnipotentRadicalBisStatement

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.StdPar GlobalTheory.ResLine
open GlobalTheory.Doubling (absE)

namespace GlobalTheory.ResLine

theorem exists_equiv_reps {G : Type} [Group G] (Γ Λ : Subgroup G) (T : Set Γ)
    (hT : ∀ γ : Γ, ∃! t, t ∈ T ∧ ((γ * t⁻¹ : Γ) : G) ∈ Λ) (γ : Γ) :
    ∃ π : T ≃ T, ∀ i : T, ((i.1 * γ * (π i).1⁻¹ : Γ) : G) ∈ Λ := by
  choose ρ hρ hu using hT
  have key : ∀ (a b : Γ), a * b = 1 → ∀ i : T, ρ (ρ (i.1 * a) * b) = i.1 := by
    intro a b hab i
    symm
    refine hu _ _ ⟨i.2, ?_⟩
    have := Λ.inv_mem (hρ (i.1 * a)).2
    have e : ρ (i.1 * a) * b * i.1⁻¹ = (i.1 * a * (ρ (i.1 * a))⁻¹)⁻¹ := by
      rw [eq_inv_of_mul_eq_one_right hab]; group
    rw [e, Subgroup.coe_inv]
    exact this
  exact ⟨⟨fun i => ⟨ρ (i.1 * γ), (hρ _).1⟩, fun i => ⟨ρ (i.1 * γ⁻¹), (hρ _).1⟩,
    fun i => Subtype.ext (key γ γ⁻¹ (mul_inv_cancel _) i), fun i => Subtype.ext (key γ⁻¹ γ (inv_mul_cancel _) i)⟩,
    fun i => (hρ _).2⟩

theorem reps_perm : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (r : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E) (L : Submodule (𝓞 E) (Fin n → E)) (a : GL (Fin n) (AF F ⊗[F] E)) (h : GAd σ J → ℝ), Data σ J X Y L a h → ∀ T, IsReps σ J (col X) T → (∀ γ ∈ ratPts σ J, ∃ π : T ≃ T, ∀ (i : T) g, h (i.1.1 * (γ * g)) = h ((π i).1.1 * g)) ∧ (∃ i : T, ∀ g, h (i.1.1 * g) = h g) ∧ (∀ γ ∈ (ratPts σ J ⊓ lineGrp σ J (col X)), ∀ g, h (γ * g) = h g) ∧ ∀ γ : ratPts σ J, ∃! t, t ∈ T ∧ ((γ * t⁻¹ : ratPts σ J) : GAd σ J) ∈ (ratPts σ J ⊓ lineGrp σ J (col X)) := by
  intro F E _ _ _ _ _ σ n J r X Y L a h D T hT
  have h3 : ∀ γ ∈ (ratPts σ J ⊓ lineGrp σ J (col X)), ∀ g, h (γ * g) = h g := by
    rintro γ ⟨hγ, l, hl⟩ g
    rw [(GlobalTheory.T.height_function_scaling_parabolic F E σ n J r X Y L a h D).2 γ l hl g,
      (GlobalTheory.T.levi_normalizes_unipotent_radical_bis F E σ n J r X Y D.cm D.herm D.witt).2.2.2.2.2 γ hγ l hl]
    simp
  have h4 : ∀ γ : ratPts σ J, ∃! t, t ∈ T ∧ ((γ * t⁻¹ : ratPts σ J) : GAd σ J) ∈ (ratPts σ J ⊓ lineGrp σ J (col X)) := by
    intro γ
    obtain ⟨t, ⟨ht, hl⟩, hu⟩ := hT γ
    exact ⟨t, ⟨ht, (γ * t⁻¹).2, hl⟩, fun s hs => hu s ⟨hs.1, hs.2.2⟩⟩
  refine ⟨fun γ hγ => ?_, ?_, h3, h4⟩
  · obtain ⟨π, hπ⟩ := exists_equiv_reps _ _ T h4 ⟨γ, hγ⟩
    refine ⟨π, fun i g => ?_⟩
    rw [← h3 _ (hπ i) ((π i).1.1 * g)]
    congr 1
    simp [mul_assoc]
  · obtain ⟨t, ⟨ht, hl⟩, -⟩ := h4 1
    refine ⟨⟨t, ht⟩, fun g => ?_⟩
    rw [← h3 _ hl (t.1 * g)]
    congr 1
    simp

end GlobalTheory.ResLine
