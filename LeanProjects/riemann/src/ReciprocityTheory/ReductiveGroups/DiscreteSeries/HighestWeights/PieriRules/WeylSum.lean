import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.PieriRules.KTypeIntDomStatement
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.PieriRules.WeylPos
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.PieriRules.WeylRatio
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.PieriRules.BlockSum
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.PieriRules.WeylVanish

noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS.HW

open ReciprocityTheory.ChartRestriction.DS

theorem weylSum_inj {n : ℕ} {ε : Fin n → Bool} {Λ : Fin n → ℝ} (hΛ : KDom ε Λ) (β : Bool) :
    ∀ a b, ε a = β → ε b = β → (Λ + rhoC ε) a = (Λ + rhoC ε) b → a = b := by
  intro a b ha hb h
  have he : ε a = ε b := ha.trans hb.symm
  simp only [Pi.add_apply] at h
  rcases lt_trichotomy a b with hab | rfl | hab
  · have h1 := rhoC_sub_ge_one ε hab he
    have h2 := hΛ a b hab he
    linarith
  · rfl
  · have h1 := rhoC_sub_ge_one ε hab he.symm
    have h2 := hΛ b a hab he.symm
    linarith

theorem weylSum_split {n : ℕ} (ε : Fin n → Bool) (f : Fin n → ℝ) :
    ∑ s, f s = ∑ s ∈ univ.filter (fun s => ε s = true), f s +
      ∑ s ∈ univ.filter (fun s => ε s = false), f s := by
  rw [← Finset.sum_filter_add_sum_filter_not univ (fun s => ε s = true)]
  congr 1
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext s; simp

theorem weylSum_card_split {n : ℕ} (ε : Fin n → Bool) :
    ((univ.filter (fun s => ε s = true)).card : ℝ) + ((univ.filter (fun s => ε s = false)).card : ℝ) = n := by
  have h := weylSum_split ε (fun _ => (1 : ℝ))
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one, Finset.card_univ, Fintype.card_fin] at h
  linarith

theorem weylSum_pIdx {n : ℕ} (ε : Fin n → Bool) (β : Bool) (F G : Fin n → ℝ) :
    ∑ p : pIdx ε β, F p.1.1 * G p.1.2 =
      (∑ i ∈ univ.filter (fun i => ε i = β), F i) * ∑ j ∈ univ.filter (fun j => ε j = !β), G j := by
  rw [Finset.sum_mul_sum, ← Finset.sum_product', ← Finset.filter_product, Finset.univ_product_univ]
  exact (Finset.sum_subtype _ (by simp) (fun q : Fin n × Fin n => F q.1 * G q.2)).symm

theorem weylSum_card_pIdx {n : ℕ} (ε : Fin n → Bool) (β : Bool) :
    (Nat.card (pIdx ε β) : ℝ) = ((univ.filter (fun i => ε i = β)).card : ℝ) *
      ((univ.filter (fun j => ε j = !β)).card : ℝ) := by
  have h := weylSum_pIdx ε β (fun _ => (1 : ℝ)) (fun _ => (1 : ℝ))
  simp only [mul_one, Finset.sum_const, nsmul_eq_mul, Finset.card_univ] at h
  rw [Nat.card_eq_fintype_card, ← h]

theorem weylSum_shift {n : ℕ} (ε : Fin n → Bool) (Λ : Fin n → ℝ) (hΛ : KDom ε Λ) (c : ℝ)
    (hc : ∀ β : Bool, ∑ s ∈ univ.filter (fun s => ε s = β), ∏ b ∈ univ.filter (fun b => b ≠ s ∧ ε b = ε s),
      ((Λ + rhoC ε) s - (Λ + rhoC ε) b + c) / ((Λ + rhoC ε) s - (Λ + rhoC ε) b) =
        ((univ.filter (fun s => ε s = β)).card : ℝ)) :
    ∑ s, weylK ε (Λ + c • (Pi.single s (1 : ℝ) : Fin n → ℝ)) = (n : ℝ) * weylK ε Λ := by
  simp only [weylK_add_smul_single ε Λ hΛ]
  rw [← Finset.mul_sum, weylSum_split ε, hc true, hc false, weylSum_card_split]
  ring

theorem weylSumStd : WeylSumStdStatement := by
  intro n ε Λ hint hΛ
  refine ⟨?_, fun s hs => weylK_std_vanish ε Λ hint hΛ s hs⟩
  have h := weylSum_shift ε Λ hΛ 1 fun β => blockSum_plus ε β _ (weylSum_inj hΛ β)
  simpa only [one_smul, stdWt] using h

theorem weylSumDual : WeylSumDualStatement := by
  intro n ε Λ hint hΛ
  refine ⟨?_, fun s hs => weylK_dual_vanish ε Λ hint hΛ s hs⟩
  have h := weylSum_shift ε Λ hΛ (-1) fun β => by
    rw [← blockSum_minus ε β _ (weylSum_inj hΛ β)]
    refine Finset.sum_congr rfl fun s _ => Finset.prod_congr rfl fun b _ => by ring
  simpa only [neg_one_smul, dualWt] using h

theorem weylSumP : WeylSumPStatement := by
  intro n ε β Λ hint hΛ
  refine ⟨?_, fun p hp => weylK_p_vanish ε β Λ hint hΛ p hp⟩
  have hr : ∀ p : pIdx ε β, weylK ε (Λ + pWt ε β p) = weylK ε Λ *
      ((∏ b ∈ univ.filter (fun b => b ≠ p.1.1 ∧ ε b = ε p.1.1),
        ((Λ + rhoC ε) p.1.1 - (Λ + rhoC ε) b + 1) / ((Λ + rhoC ε) p.1.1 - (Λ + rhoC ε) b)) *
      (∏ b ∈ univ.filter (fun b => b ≠ p.1.2 ∧ ε b = ε p.1.2),
        ((Λ + rhoC ε) p.1.2 - (Λ + rhoC ε) b - 1) / ((Λ + rhoC ε) p.1.2 - (Λ + rhoC ε) b))) := by
    intro p
    have hij : ε p.1.1 ≠ ε p.1.2 := by rw [p.2.1, p.2.2]; cases β <;> decide
    rw [← mul_assoc]
    exact weylK_add_single_sub_single ε Λ hΛ p.1.1 p.1.2 hij
  rw [Finset.sum_congr rfl fun p _ => hr p, ← Finset.mul_sum, weylSum_pIdx ε β
    (fun i => ∏ b ∈ univ.filter (fun b => b ≠ i ∧ ε b = ε i),
      ((Λ + rhoC ε) i - (Λ + rhoC ε) b + 1) / ((Λ + rhoC ε) i - (Λ + rhoC ε) b))
    (fun j => ∏ b ∈ univ.filter (fun b => b ≠ j ∧ ε b = ε j),
      ((Λ + rhoC ε) j - (Λ + rhoC ε) b - 1) / ((Λ + rhoC ε) j - (Λ + rhoC ε) b)),
    blockSum_plus ε β _ (weylSum_inj hΛ β), blockSum_minus ε (!β) _ (weylSum_inj hΛ (!β)),
    weylSum_card_pIdx]
  ring

end ReciprocityTheory.ChartRestriction.DS.HW
