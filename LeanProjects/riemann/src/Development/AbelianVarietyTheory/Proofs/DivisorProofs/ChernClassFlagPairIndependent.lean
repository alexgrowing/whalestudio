import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GlobalHeightBoundIffAtGoodPrimes
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Adj
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagPairSameStepsPointEqStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagPairTwoStepExchangeStatement
open CategoryTheory Limits AlgebraicGeometry IsLocalRing MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.DV Formalism.DegreeFormula Formalism.MainNotions.LatticeTransfer Formalism.MainNotions.WeightThresholdDefs
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Vert GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.MixedLocalChains

set_option autoImplicit false

namespace GlobalTheory.AdjRankTwo

theorem sameStep_zero {X : Scheme.{0}} {E : X.Modules} {N : ℕ} (fl fl' : Vert.Flag E N) :
    fl.SameStep fl' 0 :=
  ⟨(GlobalTheory.VB.isVB_zero_iff.1 (fl.isVB 0)).iso (GlobalTheory.VB.isVB_zero_iff.1 (fl'.isVB 0)),
    (GlobalTheory.VB.isVB_zero_iff.1 (fl.isVB 0)).eq_of_src _ _⟩

theorem sameStep_last {X : Scheme.{0}} {E : X.Modules} {N : ℕ} (fl fl' : Vert.Flag E N) :
    fl.SameStep fl' (Fin.last N) :=
  ⟨asIso (fl.ι _) ≪≫ (asIso (fl'.ι _)).symm, by simp⟩

theorem sum_eq_of_two {r : ℕ} (f g : Fin r → ℚ) (a b : Fin r) (hab : a ≠ b)
    (h : ∀ i, i ≠ a → i ≠ b → f i = g i) (h2 : f a + f b = g a + g b) : ∑ i, f i = ∑ i, g i := by
  have hb : b ∈ (Finset.univ.erase a) := Finset.mem_erase.2 ⟨hab.symm, Finset.mem_univ _⟩
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ a), ← Finset.add_sum_erase _ _ hb,
    ← Finset.add_sum_erase _ g (Finset.mem_univ a), ← Finset.add_sum_erase _ g hb, ← add_assoc,
    ← add_assoc, h2]
  congr 1
  refine Finset.sum_congr rfl fun i hi => ?_
  obtain ⟨hib, hi⟩ := Finset.mem_erase.1 hi
  exact h i (Finset.mem_erase.1 hi).1 hib

end GlobalTheory.AdjRankTwo

set_option linter.overlappingInstances false in

theorem GlobalTheory.AdjRankTwo.ck_eq_of_adj : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (p : ℕ) [Fact p.Prime] [CharZero O] [CharP (ResidueField O) p] (B : GlobalTheory.Vert.Model O), GlobalTheory.IsNormalScheme B.X → (∀ (W W' : B.X.Modules) (ψ : B.GenIso W W') (R R' : GlobalTheory.Vert.Model.FlagPair ψ 2) (k : ℕ) (Q : PicSym B.X), ck (R.toFPair p) k Q = ck (R'.toFPair p) k Q) → ∀ (E E' : B.X.Modules) (φ : B.GenIso E E') (r : ℕ) (P P' : GlobalTheory.Vert.Model.FlagPair φ r), GlobalTheory.Vert.Model.FlagPair.Adj P P' → ∀ (k : ℕ) (Q : PicSym B.X), ck (P.toFPair p) k Q = ck (P'.toFPair p) k Q := by
  intro O _ _ _ p _ _ _ B _hB H E E' φ r P P' hadj k Q
  obtain ⟨j, hj⟩ := hadj
  have hs : ∀ i : Fin (r + 1), ((i : ℕ) = 0 ∨ (i : ℕ) = r ∨ i ≠ j) →
      P.fl.SameStep P'.fl i ∧ P.fl'.SameStep P'.fl' i := by
    intro i hi
    rcases hi with h | h | h
    · obtain rfl : i = 0 := Fin.ext h
      exact ⟨GlobalTheory.AdjRankTwo.sameStep_zero _ _, GlobalTheory.AdjRankTwo.sameStep_zero _ _⟩
    · obtain rfl : i = Fin.last r := Fin.ext h
      exact ⟨GlobalTheory.AdjRankTwo.sameStep_last _ _, GlobalTheory.AdjRankTwo.sameStep_last _ _⟩
    · exact hj i h
  have good : ∀ i : Fin r, ((i : ℕ) + 1 ≠ j ∨ (j : ℕ) = r) → ((i : ℕ) ≠ j ∨ (j : ℕ) = 0) →
      (P.toFPair p).x i = (P'.toFPair p).x i ∧ (P.toFPair p).x' i = (P'.toFPair p).x' i ∧
        (P.toFPair p).Dv i = (P'.toFPair p).Dv i := by
    intro i h1 h2
    have a1 := hs i.castSucc (by
      by_cases hi : (i : ℕ) = 0
      · exact Or.inl hi
      · exact Or.inr (Or.inr fun e => by have := congrArg Fin.val e; simp at this; omega))
    have a2 := hs i.succ (by
      by_cases hi : (i : ℕ) + 1 = r
      · exact Or.inr (Or.inl hi)
      · exact Or.inr (Or.inr fun e => by have := congrArg Fin.val e; simp at this; omega))
    exact GlobalTheory.T.flag_pair_same_steps_point_eq O p B E E' φ r P P' i a1.1 a2.1 a1.2 a2.2
  unfold ck
  by_cases hj0 : (j : ℕ) = 0 ∨ (j : ℕ) = r
  · refine Finset.sum_congr rfl fun i _ => ?_
    obtain ⟨e1, e2, e3⟩ := good i (by omega) (by omega)
    rw [e1, e2, e3]
  · have hjr := j.isLt
    obtain ⟨m, hm⟩ : ∃ m, (j : ℕ) = m + 1 := ⟨(j : ℕ) - 1, by omega⟩
    have hmr : m + 2 ≤ r := by omega
    have s0 := hs ⟨m, by omega⟩ (Or.inr (Or.inr fun e => by rw [← e] at hm; simp at hm))
    have s2 := hs ⟨m + 2, by omega⟩ (Or.inr (Or.inr fun e => by rw [← e] at hm; simp at hm))
    obtain ⟨W, W', ψ, R, R', ⟨r1, r2, r3, r4, r5, r6⟩, ⟨q1, q2, q3, q4, q5, q6⟩⟩ :=
      GlobalTheory.T.flag_pair_two_step_exchange O p B E E' φ r m hmr P P' s0.1 s2.1 s0.2 s2.2
    have hR := H W W' ψ R R' k Q
    unfold ck at hR
    rw [Fin.sum_univ_two, Fin.sum_univ_two, r1, r2, r3, r4, r5, r6, q1, q2, q3, q4, q5, q6] at hR
    refine GlobalTheory.AdjRankTwo.sum_eq_of_two _ _ ⟨m, by omega⟩ ⟨m + 1, by omega⟩
      (fun e => by simp [Fin.ext_iff] at e) (fun i h1 h2 => ?_) hR
    obtain ⟨e1, e2, e3⟩ := good i (Or.inl fun e => h1 (Fin.ext (by simp; omega)))
      (Or.inl fun e => h2 (Fin.ext (by simp; omega)))
    rw [e1, e2, e3]
