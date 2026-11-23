import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.BudgetAt
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.EightDvdNCol
import Development.AbelianVarietyTheory.Definitions.Divisors.QuoIff
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsTauZeroNonzeroAll
import Development.AbelianVarietyTheory.Definitions.TorusSections.IsTorusOf
import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
import Development.AbelianVarietyTheory.Definitions.Divisors.UnifOfSpaceEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSelfDualTr
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.FundSetMeasStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.CovHt

namespace GlobalTheory.ModelWtGap

def colRot (p q : ℕ) (a : Fin (p + q)) : Fin (p + q) :=
  if h : (a : ℕ) < q then ⟨p + a, by omega⟩ else ⟨a - q, by omega⟩

theorem colRot_val (p q : ℕ) (a : Fin (p + q)) :
    (colRot p q a : ℕ) = if (a : ℕ) < q then p + a else a - q := by
  unfold colRot
  split_ifs <;> rfl

theorem colRot_bijective (p q : ℕ) : Function.Bijective (colRot p q) := by
  refine Finite.injective_iff_bijective.1 fun a b h => ?_
  have h1 := congrArg Fin.val h
  rw [colRot_val, colRot_val] at h1
  have := a.2
  have := b.2
  apply Fin.ext
  split_ifs at h1 <;> omega

theorem model_weight_gap_l1_card : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r), GoodEmb c σ → IsUnf U → 1 ≤ Dw.p → 1 ≤ Dw.q → ∀ (u1 : GlobalTheory.AllWt.Weight Dw) (g : ℝ), (∀ τ (a b : Fin (Dw.p + Dw.q)), (b : ℕ) = a + 1 → g ≤ (u1 τ a : ℝ) - u1 τ b) → ∀ k : U.Comp, (∀ τ (a b : Fin r), (b : ℕ) = a + 1 → (b : ℕ) ≠ (U.X k).p0 → g ≤ (modelWt U (wtOf Dw u1 0) k τ a : ℝ) - modelWt U (wtOf Dw u1 0) k τ b) ∧ (∀ τ (a b : Fin r), (a : ℕ) = 0 → (b : ℕ) = r - 1 → g ≤ (modelWt U (wtOf Dw u1 0) k τ b : ℝ) - modelWt U (wtOf Dw u1 0) k τ a) ∧ (∑ τ, ∑ a, |(modelWt U (wtOf Dw u1 0) k τ a : ℝ)|) = GlobalTheory.CovHt.l1 u1 ∧ (U.X k).Ψ.card = Nat.card (GlobalTheory.AllWt.Psi H) := by
  intro E _ _ _ H Dw l Xo c σ r U hσ hU hp hq u1 g hg k
  obtain rfl := hU.1
  obtain ⟨hp0, hΨ⟩ := hU.2.1 k
  have hσ0 : σ ⟨H.rt0, c.le (baseKA l).ρ.2⟩ = H.rt0 := hσ
  have hrel : ∀ ρ : E →+* ℂ, ρ (H.rt : E) = H.rt0 → relab c σ ρ (H.rt : E) = H.rt0 := fun ρ h =>
    (congrArg σ (Subtype.ext h)).trans hσ0
  let e : Psi H → (U.X k).Ψ := fun ρ => ⟨relab c σ ρ.1, (hΨ _).2 (hrel _ ρ.2)⟩
  have hsurj : Function.Surjective (relab (E := E) c σ) := Finite.injective_iff_surjective.1 (relab_injective σ)
  have he : Function.Bijective e := by
    refine ⟨fun a b h => Subtype.ext (relab_injective σ (congrArg Subtype.val h)), fun τ => ?_⟩
    obtain ⟨ρ, hρ⟩ := hsurj τ.1
    have hρΨ : ρ (H.rt : E) = H.rt0 := by
      by_contra hn
      have h3 := hrel _ (GlobalTheory.AllWt.conj_mem hn)
      rw [relab_conj, hρ] at h3
      exact GlobalTheory.AllWt.conj_not_mem ⟨τ.1, (hΨ _).1 τ.2⟩ h3
    exact ⟨⟨ρ, hρΨ⟩, Subtype.ext hρ⟩
  have hval : ∀ (ρ : Psi H) (a : Fin (Dw.p + Dw.q)),
      modelWt U (wtOf Dw u1 0) k (e ρ) a = u1 ρ (colRot Dw.p Dw.q a) := by
    rintro ρ ⟨a, ha⟩
    by_cases h : a < Dw.q
    · rw [modelWt_wtOf_small U u1 0 k hp0 ρ (e ρ).2 a h ha]
      congr 1
      apply Fin.ext
      rw [colRot_val]
      simp [h]
    · obtain ⟨i, rfl⟩ : ∃ i, a = Dw.q + i := ⟨a - Dw.q, by omega⟩
      rw [modelWt_wtOf_big U u1 0 k hp0 ρ (e ρ).2 i (by omega) ha]
      congr 1
      apply Fin.ext
      rw [colRot_val]
      simp
  refine ⟨fun τ a b hab hb => ?_, fun τ a b ha hb => ?_, ?_, ?_⟩
  · obtain ⟨ρ, rfl⟩ := he.2 τ
    rw [hval, hval]
    apply hg
    rw [colRot_val, colRot_val]
    rw [hp0] at hb
    split_ifs <;> omega
  · obtain ⟨ρ, rfl⟩ := he.2 τ
    rw [hval, hval]
    apply hg
    rw [colRot_val, colRot_val]
    split_ifs <;> omega
  · unfold GlobalTheory.CovHt.l1
    rw [← he.sum_comp]
    refine Finset.sum_congr (by congr) fun ρ _ => ?_
    simp only [hval]
    exact (colRot_bijective Dw.p Dw.q).sum_comp fun i => |(u1 ρ i : ℝ)|
  · rw [Nat.card_eq_of_bijective e he, Nat.card_eq_fintype_card, Fintype.card_coe]

end GlobalTheory.ModelWtGap
