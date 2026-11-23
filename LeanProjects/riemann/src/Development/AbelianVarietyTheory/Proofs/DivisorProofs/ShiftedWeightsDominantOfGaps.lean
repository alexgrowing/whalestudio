import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GrothendieckDeformation
import Development.AbelianVarietyTheory.Definitions.Divisors.CovolXOfCovol
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
import Development.AbelianVarietyTheory.Definitions.Divisors.WellChosen
import Development.AbelianVarietyTheory.Definitions.Divisors.MeanLogLeOfBounds
import Development.AbelianVarietyTheory.Definitions.Divisors.WedgeNrmLeOfWedgeNormLe
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomWeightHomWeight
import Development.AbelianVarietyTheory.Definitions.Divisors.MemLevEigenIffTransl
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LogMeanShares.LogMeanStatements.HSClaim
import Development.AbelianVarietyTheory.Definitions.Divisors.GenRatios
import Development.AbelianVarietyTheory.Definitions.Divisors.BadElt
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct

namespace GlobalTheory.CompHS.WtPar

theorem antitone_of_step {N : ℕ} (f : Fin N → ℤ) (h : ∀ a b : Fin N, (b : ℕ) = a + 1 → f b ≤ f a) :
    Antitone f := by
  rintro ⟨i, hi⟩ ⟨j, hj⟩ hij
  simp only [Fin.mk_le_mk] at hij
  induction j, hij using Nat.le_induction with
  | base => exact le_rfl
  | succ k hik ih => exact (h ⟨k, by omega⟩ ⟨k + 1, hj⟩ rfl).trans (ih (by omega))

theorem shifted_dominant : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} (Dw : Datum H) (P : WtPar Dw),
    0 ≤ P.c₀ → 2 * (Dw.p + Dw.q) + CompHt.dimFlag Dw ≤ P.T →
    (∀ (τ : Psi H) (a b : Fin (Dw.p + Dw.q)), (b : ℕ) = a + 1 →
      ((b : ℕ) ≠ Dw.p → ((P.T : ℤ) + CompHt.dimFlag Dw + 2) * ((P.T : ℤ) + CompHt.dimFlag Dw + 2 + 2 * ((Dw.p + Dw.q : ℕ) : ℤ)) ≤
        P.u τ a - P.u τ b + 2) ∧
      ((b : ℕ) = Dw.p → ((P.T : ℤ) + P.c₀) * ((P.T : ℤ) + CompHt.dimFlag Dw + 1) + P.c₀ + 2 * ((Dw.p + Dw.q : ℕ) : ℤ) - 2 ≤
        P.u τ a - P.u τ b)) →
    ∀ s : ℕ, s ≤ 3 → ∀ τ : Psi H, Antitone (P.uMinus τ + (s * P.c₀) • hodgeWt Dw τ) ∧
      Antitone (((P.T + CompHt.dimFlag Dw + (if s = 0 then 3 else 4) : ℕ) : ℤ) • P.u₁ τ - (P.uMinus τ + (s * P.c₀) • hodgeWt Dw τ)) := by
  intro E _ _ _ H Dw P hc hT hgap s hs τ
  have hD : (CompHt.dimFlag Dw : ℤ) = (FlagTan.dimFlag Dw : ℤ) := by exact_mod_cast dimFlag_eq Dw
  have hw : ∀ i : Fin (Dw.p + Dw.q), hodgeWt Dw τ i = if (i : ℕ) < Dw.p then 0 else -1 := fun i => rfl
  have hX : ∀ i, (P.uMinus τ + ((s : ℤ) * P.c₀) • hodgeWt Dw τ) i =
      P.u τ i + ((s : ℤ) * P.c₀ - P.c₀) * hodgeWt Dw τ i := by
    intro i
    simp only [uMinus, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hsc : (s : ℤ) * P.c₀ ≤ 3 * P.c₀ := mul_le_mul_of_nonneg_right (by exact_mod_cast hs) hc
  have hsc0 : 0 ≤ (s : ℤ) * P.c₀ := mul_nonneg (by positivity) hc
  have hT0 : (0 : ℤ) ≤ P.T := by positivity
  have hD0 : (0 : ℤ) ≤ CompHt.dimFlag Dw := by positivity
  constructor
  · refine antitone_of_step _ fun a b hab => ?_
    rw [hX, hX, hw, hw]
    obtain ⟨h1, h2⟩ := hgap τ a b hab
    by_cases hb : (b : ℕ) = Dw.p
    · have h := h2 hb
      have hb' : ¬ (b : ℕ) < Dw.p := by omega
      have ha' : (a : ℕ) < Dw.p := by omega
      simp only [hb', ha', if_true, if_false]
      have : 0 ≤ ((P.T : ℤ) + P.c₀) * ((P.T : ℤ) + CompHt.dimFlag Dw + 1) := by positivity
      have : (2 : ℤ) ≤ ((Dw.p + Dw.q : ℕ) : ℤ) := by have := b.2; push_cast; omega
      linarith
    · have h := h1 hb
      have : 2 ≤ ((P.T : ℤ) + CompHt.dimFlag Dw + 2) * ((P.T : ℤ) + CompHt.dimFlag Dw + 2 + 2 * ((Dw.p + Dw.q : ℕ) : ℤ)) := by
        have h2 : (0 : ℤ) ≤ ((Dw.p + Dw.q : ℕ) : ℤ) := by positivity
        nlinarith
      by_cases ha : (a : ℕ) < Dw.p
      · have hb' : (b : ℕ) < Dw.p := by omega
        simp only [hb', ha, if_true]; linarith
      · have hb' : ¬ (b : ℕ) < Dw.p := by omega
        simp only [hb', ha, if_false]; linarith
  · refine antitone_of_step _ fun a b hab => ?_
    obtain ⟨h1, h2⟩ := hgap τ a b hab
    have hk : (a : ℕ) + 1 < Dw.p + Dw.q := hab ▸ b.2
    have hg1 := P.gap_u₁ τ hk
    rw [P.gap_uMinus_sub_kap τ hk, gap_eq _ hab, gap_eq _ hab] at hg1
    set G := P.u τ a - P.u τ b + (if (a : ℕ) + 1 = Dw.p then -P.c₀ - (2 * ((Dw.p + Dw.q : ℕ) : ℤ) - 2) else 2) with hG
    have hT₁ : P.T₁ = (P.T : ℤ) + CompHt.dimFlag Dw + 1 := by rw [WtPar.T₁, hD]
    have hT₁0 : 0 < P.T₁ := by rw [hT₁]; positivity
    set g := G / P.T₁ with hgdef
    have hdiv : P.T₁ * g + G % P.T₁ = G := by rw [Int.emod_def]; ring
    have hr0 : 0 ≤ G % P.T₁ := Int.emod_nonneg _ hT₁0.ne'
    have hr1 : G % P.T₁ < P.T₁ := Int.emod_lt_of_pos _ hT₁0
    have hu : P.u₁ τ a = P.u₁ τ b + g := by rw [← hg1]; ring
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hX, hw, hu]
    rw [hT₁] at hdiv hr1
    have hTz : 2 * ((Dw.p + Dw.q : ℕ) : ℤ) + CompHt.dimFlag Dw ≤ P.T := by exact_mod_cast hT
    have hN : (2 : ℤ) ≤ ((Dw.p + Dw.q : ℕ) : ℤ) := by
      have := b.2; push_cast; omega
    have hK : ∀ c : ℕ, ((P.T + CompHt.dimFlag Dw + c : ℕ) : ℤ) = (P.T : ℤ) + CompHt.dimFlag Dw + c := by
      intro c; push_cast; ring
    by_cases hb : (b : ℕ) = Dw.p
    · have h := h2 hb
      have hb' : ¬ (b : ℕ) < Dw.p := by omega
      have ha' : (a : ℕ) < Dw.p := by omega
      have hG' : G = P.u τ a - P.u τ b - P.c₀ - (2 * ((Dw.p + Dw.q : ℕ) : ℤ) - 2) := by
        rw [hG, if_pos (by omega)]; ring
      have hgl : (P.T : ℤ) + P.c₀ ≤ g := by
        rw [hgdef, Int.le_ediv_iff_mul_le hT₁0, hT₁]; linarith
      simp only [hb', ha', if_true, if_false]
      by_cases hs0 : s = 0
      · subst hs0
        simp only [if_true, hK, Nat.cast_zero, zero_mul]
        push_cast
        linarith
      · simp only [hs0, if_false, hK]
        push_cast
        linarith
    · have h := h1 hb
      have hG' : G = P.u τ a - P.u τ b + 2 := by
        rw [hG, if_neg (by omega)]
      have hgl : (P.T : ℤ) + CompHt.dimFlag Dw + 2 + 2 * ((Dw.p + Dw.q : ℕ) : ℤ) ≤ g := by
        rw [hgdef, Int.le_ediv_iff_mul_le hT₁0, hT₁]; linarith
      have hsame : hodgeWt Dw τ a = hodgeWt Dw τ b := by
        rw [hw, hw]
        by_cases ha : (a : ℕ) < Dw.p
        · rw [if_pos ha, if_pos (by omega)]
        · rw [if_neg ha, if_neg (by omega)]
      simp only [← hw, hsame]
      split_ifs <;> simp only [hK] <;> push_cast <;> linarith

end GlobalTheory.CompHS.WtPar
