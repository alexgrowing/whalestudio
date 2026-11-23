import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeLFunctionBottomPairStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BottomPairNormNeZeroStatement

open Finset
open GlobalTheory.SqTop GlobalTheory.FunObj.SqNum
open GlobalTheory.NormSum (Pair)
open GlobalTheory.CMVal (IsHeckeL)

namespace GlobalTheory.NormBigProof

theorem squareBottomHalfRankSum_le_halfRank (D : Formalism.BasicNotions.D7) (i j : ℕ) : h0 D i j ≤ halfRank D i j := by
  unfold h0 halfRank botBig botSmall
  exact Nat.div_le_div_right (Nat.add_le_add (Nat.sub_le _ _) (Nat.sub_le _ _))

theorem normBig : GlobalTheory.FunPr.Hypotheses₂ → (∀ D, GlobalTheory.NormSum.Inp D) → LNe → NormBig := by
  intro hP hI hL
  obtain ⟨a1, k1⟩ := hL
  obtain ⟨a2, k2⟩ := GlobalTheory.T.hecke_l_function_bottom_pair hP hI ⟨a1, k1⟩
  obtain ⟨a3, k3⟩ := GlobalTheory.T.bottom_pair_norm_ne_zero hP hI ⟨a1, k1⟩
  refine ⟨max a1 (max a2 a3), fun ε CF hCF => ?_⟩
  obtain ⟨c1, x1, l1⟩ := k1 ε CF (le_trans (le_max_left _ _) hCF)
  obtain ⟨c2, x2, l2⟩ := k2 ε CF (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hCF)
  obtain ⟨c3, x3, l3⟩ := k3 ε CF (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hCF)
  refine ⟨max c1 (max c2 c3), max x1 (max x2 x3), fun C hC D large₂ he hx hRec T Lc μ₀ hμ G => ?_⟩
  have hl := l1 C (le_trans (le_max_left _ _) hC) D large₂ he (le_trans (le_max_left _ _) hx) hRec T Lc μ₀ hμ G
  have hr := l2 C (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hC) D large₂ he
    (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx) hRec T Lc μ₀ hμ G
  have hz := l3 C (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hC) D large₂ he
    (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hx) hRec T Lc μ₀ hμ G
  intro δ t0 i j
  by_cases hex : ∃ (t : T) (Q : ℕ) (P P' : Pair D ⊤ δ t0 Q), IsBottom G t i j (modT G t) P P'
  · obtain ⟨t₀, Q₀, P₀, P₀', hb₀⟩ := hex
    obtain ⟨Λ₀, hΛ₀, hne⟩ := (hl i j).1 t₀
    have hprod : ∏ s ∈ Icc (1 - (e0 D i j : ℤ)) (h0 D i j : ℤ), Λ₀ s ≠ 0 :=
      prod_ne_zero_iff.2 fun s hs => hne s (mem_Icc.1 hs).1
        (le_trans (mem_Icc.1 hs).2 (by exact_mod_cast squareBottomHalfRankSum_le_halfRank D i j))
    have hn₀ : (P₀.norm : ℂ) ≠ 0 := by exact_mod_cast hz δ t0 i j t₀ Q₀ P₀ P₀' hb₀
    refine ⟨(P₀.norm : ℂ) / ∏ s ∈ Icc (1 - (e0 D i j : ℤ)) (h0 D i j : ℤ), Λ₀ s, div_ne_zero hn₀ hprod,
      fun t Q P P' Λ hb hΛ => ?_⟩
    have e := hr δ t0 i j t t₀ Q Q₀ P P' P₀ P₀' Λ Λ₀ hb hb₀ hΛ hΛ₀
    rw [div_mul_eq_mul_div, eq_div_iff hprod, e]
  · exact ⟨1, one_ne_zero, fun t Q P P' Λ hb _ => absurd ⟨t, Q, P, P', hb⟩ hex⟩

end GlobalTheory.NormBigProof
