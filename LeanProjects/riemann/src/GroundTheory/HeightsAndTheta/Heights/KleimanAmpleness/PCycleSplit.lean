import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.StatementsCycleSplit
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.StatementsCycleSplitFilt
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.StatementsCycleSplitCurve
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.StatementsCycleSplitSmall
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial Filter

universe u w

section Lemmas

variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ} {x : Fin (N + 1) → Ω}

theorem interSum_one (pp : Ideal (Poly S N)) (L : SubSystem S x Ω) (c : ℕ) :
    interSum pp ![L] c = restrLen pp (L.twist (twistSys S x (c : ℤ))) -
      restrLen pp ((twistSys S x 0).twist (twistSys S x (c : ℤ))) := by
  have h0 : tensorSub ![L] ∅ = twistSys S x 0 := by simp [tensorSub]
  have h1 : tensorSub ![L] {0} = L := by
    simp [tensorSub, List.finRange_succ, twistSys_zero_twist]
  have huniv : (Finset.univ : Finset (Finset (Fin 1))) = {∅, {0}} := by decide
  rw [interSum, huniv, Finset.sum_pair (by decide), h0, h1]
  simp only [Finset.card_empty, Finset.card_singleton]
  norm_num
  ring

theorem restrLen_of_irrelevant (pp : Ideal (Poly S N)) (hX : ∀ i, (X i : Poly S N) ∈ pp)
    (F : SubSystem S x Ω) : restrLen pp F = 0 := by
  have hle : F.secs ≤ (F.twist (idealSys x pp)).secs := by
    intro y hy
    simp only [SubSystem.secs, Submodule.mem_iInf, Submodule.restrictScalars_mem] at hy ⊢
    intro I
    obtain ⟨i, hi⟩ := I.2.1
    have hxi : x i ≠ 0 := (mem_support x).mp (I.2.2 hi)
    have h1 : (1 : Ω) ∈ (idealSys x pp).sub I :=
      Submodule.subset_span ⟨X i, X i, 1, hX i, X_mem_monos hi, isHomogeneous_X S i,
        isHomogeneous_X S i, by rw [aeval_X, div_self hxi]⟩
    exact Submodule.subset_span ⟨1, h1, y, hy I, (one_smul Ω y).symm⟩
  have hs : Subsingleton (F.secs ⧸ ((F.twist (idealSys x pp)).secs).comap F.secs.subtype) := by
    rw [Submodule.Quotient.subsingleton_iff, eq_top_iff]
    intro y _
    exact hle y.2
  unfold restrLen
  rw [Module.length_eq_zero_iff.mpr hs]
  rfl

theorem ringKrullDim_quot_succ_le {G pp : Ideal (Poly S N)} [G.IsPrime] (hle : G ≤ pp) {f : Poly S N}
    (hfp : f ∈ pp) (hfG : f ∉ G) : ringKrullDim (Poly S N ⧸ pp) + 1 ≤ ringKrullDim (Poly S N ⧸ G) := by
  refine ringKrullDim_succ_le_of_surjective (Ideal.Quotient.factor hle)
    (Ideal.Quotient.factor_surjective hle) (r := Ideal.Quotient.mk _ f) ?_ ?_
  · apply mem_nonZeroDivisors_of_ne_zero
    rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]
  · rw [Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem]
    exact hfp

theorem withBot_le_one_of_le_two {a : WithBot ℕ∞} (h2 : a ≤ 2)
    (hne : a ≠ ((1 + 1 : ℕ) : WithBot ℕ∞)) : a ≤ 1 := by
  induction a using WithBot.recBotCoe with
  | bot => exact bot_le
  | coe a =>
    induction a using ENat.recTopCoe with
    | top => exact absurd h2 (by decide)
    | coe n =>
      have h2a : (n : ℕ∞) ≤ 2 := WithBot.coe_le_coe.mp h2
      have h2' : n ≤ 2 := by exact_mod_cast h2a
      have hne' : n ≠ 2 := fun h => hne (by rw [h]; rfl)
      have h1 : (n : ℕ∞) ≤ 1 := by exact_mod_cast (show n ≤ 1 by omega)
      exact WithBot.coe_le_coe.mpr h1

theorem withBot_not_succ_le {a b : WithBot ℕ∞} (ha : a = ((1 + 1 : ℕ) : WithBot ℕ∞)) (hab : a + 1 ≤ b)
    (hb : b ≤ 2) : False := by
  subst ha
  have := hab.trans hb
  exact absurd this (by decide)

end Lemmas

open Classical in

theorem CycleSplit.proof (hF : CycleSplit.Filt.Statement.{u, w}) (hCu : CycleSplit.Curve.Statement.{u, w})
    (hSm : CycleSplit.Small.Statement.{u, w}) : CycleSplit.Statement.{u, w} := by
  intro S _ _ Ω _ _ N x M 𝔪 h𝔪 J hJhom hJle hJm hdim
  obtain ⟨n, pp, d, hpp, hcount, hres⟩ := hF S Ω N x 𝔪 h𝔪 J hJhom hJle hJm

  let v : Ideal (Poly S N) → ℤ := fun G => if IsSubvar x G 1 then interNum G ![M.toSubSystem] else 0

  have hdimj : ∀ j, ringKrullDim (Poly S N ⧸ pp j) ≤ 2 := by
    intro j
    have := (hpp j).1
    obtain ⟨G, hG, hGle⟩ := Ideal.exists_minimalPrimes_le (hpp j).2.2
    exact (ringKrullDim_le_of_surjective (Ideal.Quotient.factor hGle)
      (Ideal.Quotient.factor_surjective hGle)).trans (hdim G hG)

  have hmin : ∀ j, IsSubvar x (pp j) 1 → pp j ∈ J.minimalPrimes := by
    intro j hsv
    have := (hpp j).1
    obtain ⟨G, hG, hGle⟩ := Ideal.exists_minimalPrimes_le (hpp j).2.2
    by_cases hGe : G = pp j
    · rw [← hGe]; exact hG
    · exfalso
      have : G.IsPrime := hG.1.1
      obtain ⟨f, hfp, hfG⟩ := SetLike.exists_of_lt (lt_of_le_of_ne hGle hGe)
      exact withBot_not_succ_le hsv.dim (ringKrullDim_quot_succ_le hGle hfp hfG) (hdim G hG)

  have hpiece : ∀ j, ∀ᶠ c : ℕ in atTop, interSum (pp j) ![M.toSubSystem] c = v (pp j) := by
    intro j
    obtain ⟨hjp, hjh, hJj⟩ := hpp j
    by_cases hsv : IsSubvar x (pp j) 1
    · simp only [v, if_pos hsv]
      exact hCu S Ω N x M 𝔪 h𝔪 (pp j) hsv (hJm.trans hJj)
    · simp only [v, if_neg hsv]
      by_cases hrel : ∃ i, (X i : Poly S N) ∉ pp j
      · refine hSm S Ω N x M 𝔪 h𝔪 (pp j) hjp hjh (hJle.trans hJj) (hJm.trans hJj) ?_
        exact withBot_le_one_of_le_two (hdimj j) fun h => hsv ⟨hjp, hjh, hJle.trans hJj, hrel, h⟩
      · push Not at hrel
        exact Eventually.of_forall fun c => by
          rw [interSum_one, restrLen_of_irrelevant _ hrel, restrLen_of_irrelevant _ hrel, sub_zero]

  have hshift : ∀ j, ∀ᶠ c : ℕ in atTop,
      0 ≤ (c : ℤ) + d j ∧ interSum (pp j) ![M.toSubSystem] ((c : ℤ) + d j).toNat = v (pp j) := by
    intro j
    have ht : Tendsto (fun c : ℕ => ((c : ℤ) + d j).toNat) atTop atTop := by
      refine tendsto_atTop_atTop.mpr fun b => ⟨b + (d j).natAbs, fun a ha => ?_⟩
      omega
    exact ((eventually_ge_atTop (d j).natAbs).and (ht.eventually (hpiece j))).mono
      fun c hc => ⟨by omega, hc.2⟩
  have hall := Filter.eventually_all.mpr hshift
  filter_upwards [hall, hres M, hres (twistBundle S x 0)] with c hc hM h0
  have h0' : restrLen J ((twistSys S x 0).twist (twistSys S x (c : ℤ))) =
      ∑ j, restrLen (pp j) ((twistSys S x 0).twist (twistSys S x ((c : ℤ) + d j))) := h0

  have hsum : interSum J ![M.toSubSystem] c = ∑ j, v (pp j) := by
    rw [interSum_one, hM, h0', ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← (hc j).2, interSum_one, Int.toNat_of_nonneg (hc j).1]
  rw [hsum, Finset.sum_comp (fun G => v G) pp]

  symm
  rw [finsum_eq_sum_of_support_subset _ (s := Finset.univ.image pp) ?_]
  · refine Finset.sum_congr rfl fun G hG => ?_
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hG
    by_cases hsv : IsSubvar x (pp j) 1
    · have hm := hmin j hsv
      have : (pp j).IsPrime := (hpp j).1
      rw [dif_pos ⟨hm, hsv⟩, nsmul_eq_mul]
      simp only [v, if_pos hsv]
      rw [← hcount (pp j) hm, ENat.toNat_natCast]
    · rw [dif_neg fun h => hsv h.2]
      simp only [v, if_neg hsv, smul_zero]
  · intro G hG
    rw [Function.mem_support] at hG
    split_ifs at hG with h
    · have : G.IsPrime := h.1.1.1
      have hc0 : (cutMult J G).toNat ≠ 0 := by
        intro h0; rw [h0] at hG; simp at hG
      rw [← hcount G h.1, ENat.toNat_natCast] at hc0
      obtain ⟨j, hj⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero hc0)
      rw [Finset.mem_filter] at hj
      rw [Finset.coe_image, Finset.coe_univ, Set.image_univ]
      exact ⟨j, hj.2⟩
    · exact absurd rfl hG

end GroundTheory.Heights₂.Heights.Kleiman
