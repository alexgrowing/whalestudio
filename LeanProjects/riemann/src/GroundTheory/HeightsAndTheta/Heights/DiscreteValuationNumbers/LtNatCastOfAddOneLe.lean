import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.CutIdentityRightSideCongrOfSubMem
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

private theorem lt_natCast_of_add_one_le' {x : WithBot ℕ∞} {n : ℕ} (h : x + 1 ≤ (n : WithBot ℕ∞)) :
    x < (n : WithBot ℕ∞) := by
  induction x with
  | bot => exact WithBot.bot_lt_coe _
  | coe e =>
    have h' : e + 1 ≤ (n : ℕ∞) := by exact_mod_cast h
    have h'' : e < (n : ℕ∞) := (ENat.add_one_le_iff' (ENat.natCast_ne_top n)).mp h'
    exact_mod_cast h''

theorem TautologicalCase.proof (h3 : IntNumAddFirst.Statement.{u}) (h5 : MinimalPrimeMultiHomog.Statement.{u})
    (h6 : SupSpanMultiHomog.Statement.{u}) (h7 : SpecialQuotDim.Statement.{u})
    (h8 : SpecialIdealCorresp.Statement.{u}) (h9 : SpecialIdealMultiHomog.Statement.{u})
    (h10 : DimStrictDrop.Statement.{u}) : TautologicalCase.Statement.{u} := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ P d hP b f g hD cf cg hf hg hb L

  have hfin : ∀ x : MRing ι O, (Function.support (divCycle P x)).Finite := fun x =>
    (Ideal.finite_minimalPrimes_of_isNoetherianRing _ (P ⊔ Ideal.span {x})).subset fun W hW => by
      by_contra hmin
      exact hW (by unfold divCycle; rw [dif_neg]; exact fun h => hmin h.1)
  have hZfin : (Function.support (ratDiv P f g)).Finite :=
    ((hfin f).union (hfin g)).subset fun W hW => by
      by_contra h
      simp only [Set.mem_union, Function.mem_support, not_or, not_not] at h
      exact hW (by simp [ratDiv, h.1, h.2])
  have hPmh : IsMultiHomogIdeal P := hP.multiProj.multiHomog
  have : P.IsPrime := hP.multiProj.isPrime
  have hϖP : (C ϖ : MRing ι O) ∉ P := by
    intro h
    have h' : ϖ ∈ P.comap (C : O →+* MRing ι O) := h
    rw [hP.noTorsion, Ideal.mem_bot] at h'
    exact hϖ.ne_zero h'

  have hmh : ∀ (x : MRing ι O) (e : K → ℕ), IsMultiHomog x e → ∀ W, divCycle P x W ≠ 0 →
      IsMultiHomogIdeal W ∧ W.IsPrime ∧ P ≤ W := by
    intro x e he W hW
    unfold divCycle at hW
    split_ifs at hW with hW'
    · exact ⟨h5 O K ι _ W (h6 O K ι P x e hPmh he) hW'.1, hW'.1.1.1, le_sup_left.trans hW'.1.1.2⟩
    · exact absurd rfl hW

  have hadd : ∀ W, ratDiv P f g W ≠ 0 → vNum W (Matrix.vecCons b L) =
      vNum W (Matrix.vecCons (fun k => (cf k : ℤ)) L) - vNum W (Matrix.vecCons (fun k => (cg k : ℤ)) L) := by
    intro W hW
    have hϖW : (C ϖ : MRing ι O) ∈ W := hD.vertical W hW
    obtain ⟨hWm, hWp, hPW⟩ : IsMultiHomogIdeal W ∧ W.IsPrime ∧ P ≤ W := by
      by_cases hWf : divCycle P f W = 0
      · exact hmh g cg hg W fun hWg => hW (by simp [ratDiv, hWf, hWg])
      · exact hmh f cf hf W hWf
    have hdrop := h10 (MRing ι O) P W (lt_of_le_of_ne hPW fun e => hϖP (e ▸ hϖW))
    rw [hP.dim, show d + 1 + 1 + Fintype.card K = d + 2 + Fintype.card K by omega] at hdrop
    have hdim : ringKrullDim (MRing ι (IsLocalRing.ResidueField O) ⧸ specialIdeal W) <
        ((d + 2 + Fintype.card K : ℕ) : WithBot ℕ∞) := by
      rw [h7 O ϖ hϖ K ι W hϖW]
      exact lt_natCast_of_add_one_le' hdrop
    have key := h3 (IsLocalRing.ResidueField O) K ι d (specialIdeal W)
      (h8 O ϖ hϖ K ι P W hWp hϖW).1 (h9 O K ι W hWm) hdim b (fun k => (cg k : ℤ)) L
    rw [show b + (fun k => (cg k : ℤ)) = fun k => (cf k : ℤ) by rw [← hb]; funext k; simp] at key
    unfold vNum
    rw [key]; ring
  unfold cutIdentityLeftSide cutIdentityRightSide cycEval
  rw [← finsum_sub_distrib (hZfin.subset (Function.support_mul_subset_left _ _))
      (hZfin.subset (Function.support_mul_subset_left _ _)),
    ← finsum_sub_distrib ((hfin f).subset (Function.support_mul_subset_left _ _))
      ((hfin g).subset (Function.support_mul_subset_left _ _))]
  refine finsum_congr fun W => ?_
  rw [← mul_sub, ← sub_mul]
  change ratDiv P f g W * _ = ratDiv P f g W * _
  by_cases hW : ratDiv P f g W = 0
  · simp [hW]
  · beta_reduce
    rw [if_pos (hD.vertical W hW), hadd W hW]

end

end GroundTheory.Heights₂.Heights.NumbersDVR
