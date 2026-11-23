import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.AtypicalPathSmallWeight

noncomputable section

open MvPolynomial

namespace Formalism.MainNotions.SelectionLemmas.Pf

open Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas Formalism.MainNotions.SelectionLemmas.Pf.T

def LetterDictionaryBounds (C₀ : ℝ) : Prop :=
  ∀ (p n' r K : ℕ) [NeZero n'] [NeZero r] [NeZero K] (X : Dat n' r),
    X.Hyp p K → C₀ ≤ X.CLa → C₀ ≤ X.Ck →
    ∀ (j : ℤ) (b : ℤ → ℕ), X.AdmLL p K j b →
    ∃ (n0 : ℕ) (od : Fin (segN X.F j) → Fin (segN X.F j)),
      HypT (segN X.F j) n0 r K (segLL X.F j) (fun i => X.Bdeg p K j (X.restr j b) (segE X.F j i)) od
        (fun i => X.a / (p : ℝ) ^ (X.F.dist j (segE X.F j i) + X.Rj p K j)) X.a X.La p ∧
      (∀ μ dd, X.IsPATH p K j (X.restr j b) μ dd ↔
        IsPATHa (segLL X.F j) n0 (fun i => X.Bdeg p K j (X.restr j b) (segE X.F j i)) μ dd) ∧
      (∀ μ : Fin (segN X.F j + 1) → Fin (r + K) → ℤ,
        GoodA (segLL X.F j) (fun i => X.Bdeg p K j (X.restr j b) (segE X.F j i)) od
          (fun i => X.a / (p : ℝ) ^ (X.F.dist j (segE X.F j i) + X.Rj p K j)) X.La p μ →
        X.IsGood p K j (X.restr j b) μ) ∧
      ((rkA r K n0 (fun i => X.Bdeg p K j (X.restr j b) (segE X.F j i)) : ℕ) : ℝ) =
        (∏ x ∈ X.F.LLset j, ((Nat.choose (b x + (r + K) - 1) (r + K - 1) : ℕ) : ℝ)) *
        (∏ i : Fin r, ((Nat.choose ((X.Bw p K j (X.F.fr (j - 1) i.val) - (X.m0 K : ℤ)).toNat + (r + K) - 1)
          (r + K - 1) : ℕ) : ℝ)) ∧
      Real.exp (11 * ((segN X.F j : ℕ) : ℝ) ^ 2 * ell0 (segN X.F j) X.a - min X.La ((r + K : ℕ) : ℝ) / 32) ≤
        1 / X.a ^ (X.Ns ^ 2)

theorem good_path_weight_of_parts (C₀ : ℝ) (ha : PathWeightEqRank) (hT : LemT) (he : LetterDictionaryBounds C₀) : GoodPathWeight C₀ := by
  intro p n' r K _ _ _ X hX hCLa hCk j b hb
  obtain ⟨n0, od, hH, hPATH, hGood, hrk, hexp⟩ := he p n' r K X hX hCLa hCk j b hb
  obtain ⟨hfin, hcard⟩ := hT (segN X.F j) n0 r K (segLL X.F j) _ od _ X.a X.La p hH
  obtain ⟨hfinA, -⟩ := ha (segN X.F j) n0 r K (segLL X.F j) _ od _ X.a X.La p hH
  let S : Set ((Fin (segN X.F j + 1) → Fin (r + K) → ℤ) × (ℤ → Finset (Fin K))) :=
    {q | ∃ dd, X.IsPATH p K j (X.restr j b) q.1 dd ∧ X.IsGood p K j (X.restr j b) q.1 ∧ IsSt (tanPart q.1) q.2}
  have hSA : S ⊆ SAll (r := r) (K := K) (segLL X.F j) n0
      (fun i => X.Bdeg p K j (X.restr j b) (segE X.F j i)) := by
    rintro q ⟨dd, hp, -, hs⟩
    exact ⟨⟨dd, (hPATH q.1 dd).mp hp⟩, hs⟩
  have hGS : SGood (r := r) (K := K) (segLL X.F j) n0 (fun i => X.Bdeg p K j (X.restr j b) (segE X.F j i)) od
      (fun i => X.a / (p : ℝ) ^ (X.F.dist j (segE X.F j i) + X.Rj p K j)) X.La p ⊆ S := by
    rintro q ⟨⟨dd, hp⟩, hg, hs⟩
    exact ⟨dd, (hPATH q.1 dd).mpr hp, hGood q.1 hg, hs⟩
  have hSfin : S.Finite := hfinA.subset hSA
  have hTS : Nat.card (X.Tset p K j (X.restr j b)) = S.ncard := Nat.card_coe_set_eq S
  refine ⟨hSfin.to_subtype, ?_⟩
  rw [hTS]
  have h1 : ((SGood (r := r) (K := K) (segLL X.F j) n0 (fun i => X.Bdeg p K j (X.restr j b) (segE X.F j i)) od
      (fun i => X.a / (p : ℝ) ^ (X.F.dist j (segE X.F j i) + X.Rj p K j)) X.La p).ncard : ℝ) ≤ S.ncard := by
    exact_mod_cast Set.ncard_le_ncard hGS hSfin
  rw [mul_assoc, ← hrk]
  refine le_trans ?_ (le_trans hcard h1)
  exact mul_le_mul_of_nonneg_right (by linarith) (Nat.cast_nonneg _)

end Formalism.MainNotions.SelectionLemmas.Pf
