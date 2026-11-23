import Formalism.GaussJetBounds.OneLetterGaussJets.StatementG
import Formalism.GaussJetBounds.OneLetterGaussJets.StatementF
import Formalism.GaussJetBounds.OneLetterGaussJets.StatementA
import Formalism.GaussJetBounds.OneLetterGaussJets.OneLetterGaussProofs.CapLeOddShiftBound
import Formalism.GaussJetBounds.ThmAEntryFull

noncomputable section
open scoped BigOperators

namespace Formalism.DworkPowerSeriesWeights.OddLevelGainBounds

open Formalism.IncomingBounds

theorem gauss7_labels (l d : ℕ) [NeZero d] (hl : 2 ≤ l) (TT : Finset (ZMod d))
    (nu1 size : ZMod d → ℕ) :
    ∃ (lab : ∀ s, Fin (JnumOneLetter l d TT nu1 size s) → ZMod d × ℤ) (m : ℕ),
      (∀ s, Function.Injective (lab s)) ∧
      (∀ (s s0 : ZMod d) (j : ℤ), (∃ i, lab s i = (s0, j)) ↔
        (s0 ∈ TT ∧ Odd j ∧ s = s0 + (j : ZMod d) ∧ (0 < j → l ^ j.toNat ≤ nu1 s0) ∧
          (j < 0 → l ^ (-j).toNat ≤ Dl d TT nu1 size s))) ∧
      ∀ s i, (-(lab s i).2).toNat ≤ m := by
  classical
  have hex : ∀ s, ∃ f : Fin (JnumOneLetter l d TT nu1 size s) → ZMod d × ℤ, Function.Injective f ∧
      ∀ q : ZMod d × ℤ, (∃ i, f i = q) ↔ IsLabOneLetter l d TT nu1 size s q.1 q.2 := by
    intro s
    have hfin := letter_labels_finite l d hl TT nu1 size s
    have hcard : hfin.toFinset.card = JnumOneLetter l d TT nu1 size s :=
      (Set.ncard_eq_toFinset_card _ hfin).symm
    refine ⟨fun i => ((Finset.equivFinOfCardEq hcard).symm i).1, ?_, fun q => ⟨?_, fun hq => ?_⟩⟩
    · intro i i' h
      exact (Finset.equivFinOfCardEq hcard).symm.injective (Subtype.ext h)
    · rintro ⟨i, rfl⟩
      have h := ((Finset.equivFinOfCardEq hcard).symm i).2
      rw [Set.Finite.mem_toFinset] at h
      exact h
    · refine ⟨Finset.equivFinOfCardEq hcard ⟨q, ?_⟩, ?_⟩
      · rw [Set.Finite.mem_toFinset]
        exact hq
      · simp
  choose lab hinj hlab using hex
  refine ⟨lab, ∑ s, ∑ i, (-(lab s i).2).toNat, hinj, fun s s0 j => hlab s (s0, j), fun s i => ?_⟩
  calc (-(lab s i).2).toNat ≤ ∑ i, (-(lab s i).2).toNat :=
        Finset.single_le_sum (f := fun i => (-(lab s i).2).toNat) (fun _ _ => Nat.zero_le _)
          (Finset.mem_univ i)
    _ ≤ _ := Finset.single_le_sum (f := fun s => ∑ i, (-(lab s i).2).toNat)
          (fun _ _ => Nat.zero_le _) (Finset.mem_univ s)

theorem thmAGauss7_of (hA0 : ThmAGeneric7.{0}) : ThmAGauss7 := by
  intro l _ d N0 N1 _ hl3 hd hde hN0 K0 hK0 ζ hζ be hbe g hg0 hg U hU ε hε TT colN p hp hp1 I
    nu1 nu2 size hnu1 hnu2 hsize hJ n
  have hlp : l.Prime := Fact.out
  obtain ⟨K, instK, hult, hchar, φ, Y, hφ, hgauss, hgen⟩ :=
    residuallyGenericExists l (ZMod d × Fin N0 × Fin N0)
  have := hult
  have := hchar
  have hnl : ‖(l : K)‖ = ‖(l : ℂ_[l])‖ := by rw [← map_natCast φ, hφ]
  have hl1 : ‖(l : ℂ_[l])‖ < 1 := norm_l_lt_one l
  obtain ⟨lab, m, hinj, hlab, hm⟩ := gauss7_labels l d hlp.two_le TT nu1 size
  obtain ⟨hT1, hT2, hT3, hT4⟩ := admissibleTransfer ℂ_[l] K φ hφ l d N0 N1 K0 ζ be
  obtain ⟨hg0', hg'⟩ := hT3 g hg0 hg
  have hA := hA0 K l d N0 N1 hlp hl3 hd hde (hnl ▸ hl1) hN0 (K0.map φ) (hT1 hK0)
    (φ ζ) (hζ.map_of_injective φ.injective) _ (hT2 hbe) _ hg0' hg' _ (hT4 U hU) (φ ε)
    (by rcases hε with rfl | rfl <;> simp) TT colN p hp hp1 I Y hgen nu1 nu2 size hnu1 hnu2 hsize
    (JnumOneLetter l d TT nu1 size) lab hinj hlab hJ m hm
  rw [← frame_jet_evaluation ℂ_[l] K φ d N0 N1 g U ε be hg0 (asmS_cc_be hbe.2.2.1) colN p hp I
    (genFrame TT l m Y), hnl] at hA
  refine le_trans ?_ hA
  have hk : genFrame TT l m Y =
      fun y => Y y ^ (if y.1 ∈ TT ∧ y.2.1.val = 0 then l ^ m else 1) := by
    funext y
    unfold genFrame
    split_ifs <;> simp
  rw [hk]
  refine gauss_sum_powers ℂ_[l] K φ _ Y hgauss _ (fun y => ?_) _ n
  split_ifs
  · exact pow_ne_zero _ hlp.ne_zero
  · exact one_ne_zero

theorem thmAWeyl7_of (hG : ThmAGauss7) : ThmAWeyl7 := by
  intro l _ d N0 N1 _ hl hd hev hN0 K0 hK0 ζ hζ be hbe g hg0 hg U hU ε hε TT colN p hp hp1 I
    nu1 nu2 size h1 h2 h3 hJ c hc
  have hcpos : 0 < ‖c‖ := lt_of_lt_of_le (Real.rpow_pos_of_pos (norm_l_pos l) _) hc
  refine slope_bound_saturation ℂ_[l] d N0 colN p hp _
    (Submodule.smul_mem _ _ (coefficient_bound_membership ℂ_[l] d N0 N1 colN p hp I _)) fun n => ?_
  rw [MvPolynomial.coeff_smul, norm_smul, norm_inv, inv_mul_le_iff₀ hcpos, mul_one]
  exact (hG l d N0 N1 hl hd hev hN0 K0 hK0 ζ hζ be hbe g hg0 hg U hU ε hε TT colN p hp hp1 I
    nu1 nu2 size h1 h2 h3 hJ n).trans hc

theorem thmAEntry7_of (hW : ThmAWeyl7) : ThmAEntry7 := by
  intro l _ d N0 N1 _ hl hd hev hN0 K0 hK0 ζ hζ be hbe g hg0 hg U hU ε hε TT colN p hp hp1 I
    nu1 nu2 size hnu1 hnu2 hsize hJ δ hδ
  refine le_rpow_of_forall_norm l _ _ (norm_nonneg _) fun c hc => ?_
  have hmem := hW l d N0 N1 hl hd hev hN0 K0 hK0 ζ hζ be hbe g hg0 hg U hU ε hε TT colN p hp hp1 I
    nu1 nu2 size hnu1 hnu2 hsize hJ c hc
  have hcpos : 0 < ‖c‖ := lt_of_lt_of_le (Real.rpow_pos_of_pos (norm_l_pos l) _) hc
  have h1 := hδ _ hmem
  rw [map_smul, norm_smul, norm_inv] at h1
  rwa [inv_mul_le_iff₀ hcpos, mul_one] at h1

end Formalism.DworkPowerSeriesWeights.OddLevelGainBounds
