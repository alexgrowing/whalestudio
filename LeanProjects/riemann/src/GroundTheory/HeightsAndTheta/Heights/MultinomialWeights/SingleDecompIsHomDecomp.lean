import Mathlib
import GroundTheory.HeightsAndTheta.Heights.MultinomialWeights.StatementsEnd
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.TheoremB

open MvPolynomial Finset Filter Topology

def singleDecomp (d : IndexData) (τ : Fin d.f) (Q : XPoly d) : ℕ → Fin d.f → XPoly d :=
  fun k σ => if k = 1 then (if σ = τ then Q else 0) else 0

theorem singleDecomp_isHomDecomp (d : IndexData) (τ : Fin d.f) (Q : XPoly d)
    (hQ : Q.IsHomogeneous d.D) :
    IsHomDecomp d (RestTerms.blockPowerSum d.f d.N 1 τ * Q) (singleDecomp d τ Q) := by
  refine ⟨?_, ?_, ?_⟩
  · have hp : (RestTerms.blockPowerSum d.f d.N 1 τ).IsHomogeneous 1 := by
      unfold RestTerms.blockPowerSum
      exact IsHomogeneous.sum _ _ _ (fun i _ => by simpa using isHomogeneous_X ℚ (τ, i))
    simpa [add_comm] using hp.mul hQ
  · intro k hk σ
    unfold singleDecomp
    split_ifs with h1 h2
    · subst h1; simpa using hQ
    · exact isHomogeneous_zero _ _ _
    · exact isHomogeneous_zero _ _ _
  · unfold RestTerms.IsPowerSumDecomposition singleDecomp
    have h1 : 1 ∈ Icc 1 d.N := by
      have := d.two_le_N
      simp; omega
    rw [Finset.sum_eq_single_of_mem 1 h1]
    · simp
    · intro k _ hk
      simp [hk]

theorem restTot_singleDecomp (d : IndexData) (S : EndSystem d) (B0 : ℕ) (τ : Fin d.f)
    (Q : XPoly d) : restTot S B0 (singleDecomp d τ Q) = 0 := by
  unfold restTot rest₂
  have h : ∀ (p : ℕ) (σ : Fin d.f), ∑ k ∈ Icc 2 d.N,
      ∑' n : ℕ, restSeries d p (S.frob p) (singleDecomp d τ Q) σ k n = 0 := by
    intro p σ
    refine Finset.sum_eq_zero (fun k hk => ?_)
    have hk1 : k ≠ 1 := by
      simp at hk; omega
    have : ∀ n, restSeries d p (S.frob p) (singleDecomp d τ Q) σ k n = 0 := by
      intro n
      simp [restSeries, singleDecomp, hk1]
    simp [this]
  simp [h]

theorem card_lowerIdx_filter (d : IndexData) :
    (univ.filter (fun i : Fin d.N => i.val < d.j)).card = d.j := by
  have := d.j_lt_N
  rw [Fin.card_filter_val_lt]
  omega

theorem HeightLimitIdentity.proof (h83 : HeightTauIdentity.Statement) (hSh : ShFormula.Statement)
    (hTot : TotFormula.Statement) : HeightLimitIdentity.Statement := by
  intro d S hI hH B0 A0 b0 hA hb τ Q hQ hint
  set F := RestTerms.blockPowerSum d.f d.N 1 τ * Q with hF
  have hdec := singleDecomp_isHomDecomp d τ Q hQ
  have key := h83 d S hI B0 A0 b0 hA hb F (singleDecomp d τ Q) hdec
  rw [restTot_singleDecomp, hH τ Q hQ] at key
  have hsh : shSum d F = d.j := by
    unfold shSum
    rw [Finset.sum_eq_single τ]
    · rw [hSh d τ F _ hdec.1 hdec.2.1 hdec.2.2]
      have h1 : 1 ∈ Icc 1 d.N := by
        have := d.two_le_N
        simp; omega
      rw [Finset.sum_eq_single_of_mem 1 h1]
      · have hl : lowerPowerSum d (1 - 1) τ = (d.j : XPoly d) := by
          simp [lowerPowerSum, card_lowerIdx_filter]
        have hj : ((d.j : XPoly d)) * Q = d.j • Q := (nsmul_eq_mul _ _).symm
        simp only [singleDecomp, if_true, Nat.cast_one, one_mul, hl, hj, map_nsmul, hint]
        simp
      · intro k _ hk
        simp [singleDecomp, hk]
    · intro σ _ hσ
      rw [hSh d σ F _ hdec.1 hdec.2.1 hdec.2.2]
      refine Finset.sum_eq_zero (fun k _ => ?_)
      simp [singleDecomp, hσ]
    · simp
  have htot : totSum d F = d.N := by
    unfold totSum
    rw [Finset.sum_eq_single τ]
    · rw [hTot d τ F _ hdec.1 hdec.2.1 hdec.2.2]
      simp [singleDecomp, hint]
    · intro σ _ hσ
      rw [hTot d σ F _ hdec.1 hdec.2.1 hdec.2.2]
      simp [singleDecomp, hσ]
    · simp
  rw [hsh, htot] at key
  have hv := S.vol_pos
  rw [key]
  push_cast
  field_simp
  ring

end GroundTheory.Heights₂.Heights.TheoremB
