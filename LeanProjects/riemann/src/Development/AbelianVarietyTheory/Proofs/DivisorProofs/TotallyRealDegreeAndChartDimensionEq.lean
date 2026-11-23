import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TamagawaSpecialUnitary
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PhaseFrame
open NumberField MeasureTheory Matrix Filter Topology GlobalTheory.SUVol GlobalTheory.RiemConst ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates
open scoped ENNReal

namespace GlobalTheory.ChartCount

theorem card_strictLower (r : ℕ) : Fintype.card {p : Fin r × Fin r // p.2 < p.1} = r * (r - 1) / 2 := by
  rw [Fintype.card_congr (Equiv.subtypeProdEquivSigmaSubtype (fun (a b : Fin r) => b < a)),
    Fintype.card_sigma]
  have h : ∀ a : Fin r, Fintype.card {b : Fin r // b < a} = (a : ℕ) := by
    intro a
    rw [Fintype.card_subtype]
    have : Finset.univ.filter (fun b : Fin r => b < a) = Finset.Iio a := by ext; simp
    rw [this, Fin.card_Iio]
  simp only [h]
  rw [Fin.sum_univ_eq_sum_range (fun i => i) r, Finset.sum_range_id]

theorem two_mul_card_Psi {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r) :
    2 * X.Ψ.card = Module.finrank ℚ E := by
  classical
  have cc2 : ∀ τ : E →+* ℂ, ComplexEmbedding.conjugate (ComplexEmbedding.conjugate τ) = τ :=
    fun τ => star_star τ
  have hinj : Function.Injective (ComplexEmbedding.conjugate : (E →+* ℂ) → (E →+* ℂ)) := by
    intro a b h
    rw [← cc2 a, h, cc2]
  have hc : (X.Ψ)ᶜ = X.Ψ.map ⟨ComplexEmbedding.conjugate, hinj⟩ := by
    ext τ
    simp only [Finset.mem_compl, Finset.mem_map, Function.Embedding.coeFn_mk]
    constructor
    · intro h
      refine ⟨ComplexEmbedding.conjugate τ, ?_, cc2 τ⟩
      rw [X.cmType, cc2]
      exact h
    · rintro ⟨σ, hσ, rfl⟩
      exact (X.cmType σ).1 hσ
  have h1 := Finset.card_compl X.Ψ
  rw [hc, Finset.card_map, NumberField.Embeddings.card] at h1
  have h2 : X.Ψ.card ≤ Module.finrank ℚ E := by
    rw [← NumberField.Embeddings.card E ℂ]; exact Finset.card_le_univ _
  omega

theorem fdeg_and_nd : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r),
    fdeg E = X.Ψ.card ∧ nd X = X.Ψ.card * (r * (r - 1) / 2) := by
  intro E _ _ _ r X
  refine ⟨?_, ?_⟩
  · have h := two_mul_card_Psi X
    unfold fdeg
    omega
  · unfold nd
    rw [Fintype.card_prod, Fintype.card_coe, card_strictLower]

end GlobalTheory.ChartCount
