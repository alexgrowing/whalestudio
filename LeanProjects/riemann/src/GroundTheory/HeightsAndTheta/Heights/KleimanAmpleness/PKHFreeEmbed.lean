import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.KHFreeEmbedSt
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGenTwistGenerated
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry KHFree
open GroundTheory.Heights₂.Heights.HilbertSamuel.GenTwistGenerated (cellRes_mk cellMon_mono isMultiHomog_monomial)

noncomputable section

namespace KHFreeEmbed

set_option linter.unusedSectionVars false

variable {S : Type} [CommRing S] {K : Type} [Fintype K] [LinearOrder K] {ι : K → Type} [∀ k, Fintype (ι k)]
  [∀ k, LinearOrder (ι k)]

theorem cellRes_monoFrac {J I : ∀ k, Finset (ι k)} (hJI : ∀ k, J k ⊆ I k) (a : (Σ k, ι k) → ℤ)
    (hJ : ∀ k, negSet a k ⊆ J k) :
    KH.cellRes S (MRingOver S ι ⧸ (⊥ : Ideal (MRingOver S ι))) J I (monoFrac S J a) = monoFrac S I a := by
  have hI : ∀ k, negSet a k ⊆ I k := fun k => (hJ k).trans (hJI k)
  unfold monoFrac
  rw [dif_pos hJ, dif_pos hI, cellRes_mk (cellMon_mono hJI)]

theorem blockSum_add_negExp (a : (Σ k, ι k) → ℤ) (k : K) :
    blockSum a k + ((∑ i, negExp a ⟨k, i⟩ : ℕ) : ℤ) = ((∑ i, posExp a ⟨k, i⟩ : ℕ) : ℤ) := by
  unfold blockSum
  push_cast
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [negExp, posExp, Finsupp.coe_equivFunOnFinite_symm]
  omega

theorem isMultiHomog_posExp (a : (Σ k, ι k) → ℤ) :
    IsMultiHomog (monomial (posExp a) (1 : S) : MRingOver S ι) fun k => ∑ i, posExp a ⟨k, i⟩ :=
  isMultiHomog_monomial _ _ _ fun _ => rfl

theorem mk_posExp_mem (a : (Σ k, ι k) → ℤ) (e : K → ℤ) (he : ∀ k, e k = ((∑ i, posExp a ⟨k, i⟩ : ℕ) : ℤ)) :
    Ideal.Quotient.mk (⊥ : Ideal (MRingOver S ι)) (monomial (posExp a) 1) ∈
      KH.quotPart S (⊥ : Ideal (MRingOver S ι)) e := by
  unfold KH.quotPart
  refine Submodule.subset_span ⟨_, ⟨fun k => ?_, ?_⟩, rfl⟩
  · rw [he k]; exact Int.natCast_nonneg _
  · have : (fun k => (e k).toNat) = fun k => ∑ i, posExp a ⟨k, i⟩ := funext fun k => by rw [he k]; rfl
    rw [this]
    exact isMultiHomog_posExp a

theorem update_erase_subset (I : ∀ k, Finset (ι k)) (k : K) (i : ι k) (l : K) :
    Function.update I k ((I k).erase i) l ⊆ I l := by
  by_cases hl : l = k
  · subst hl; rw [Function.update_self]; exact Finset.erase_subset _ _
  · rw [Function.update_of_ne hl]

open Classical in

theorem embed_apply (a : (Σ k, ι k) → ℤ) (n : ℕ) (f : CombC S (negSet a) n) (I : KH.Cell K ι n) :
    embed S a n f I = if h : ∀ k, negSet a k ⊆ I.1 k then f ⟨I, h⟩ • monoFrac S I.1 a else 0 := by
  unfold embed
  rw [LinearMap.pi_apply]
  split_ifs <;> rfl

open Classical in

theorem cechD_apply (n : ℕ) (x : KH.CechC S ι (MRingOver S ι ⧸ (⊥ : Ideal (MRingOver S ι))) n)
    (I : KH.Cell K ι (n + 1)) :
    KH.cechD S ι (MRingOver S ι ⧸ (⊥ : Ideal (MRingOver S ι))) n x I = ∑ k, ∑ i ∈ I.1 k,
      if h : (∀ l, (Function.update I.1 k ((I.1 k).erase i) l).Nonempty) ∧
          ∑ l, ((Function.update I.1 k ((I.1 k).erase i) l).card - 1) = n then
        KH.faceSign I.1 k i • KH.cellRes S _ (Function.update I.1 k ((I.1 k).erase i)) I.1
          (x ⟨Function.update I.1 k ((I.1 k).erase i), h⟩)
      else 0 := by
  unfold KH.cechD
  rw [LinearMap.pi_apply, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs <;> rfl

open Classical in

theorem combD_apply (J : ∀ k, Finset (ι k)) (n : ℕ) (f : CombC S J n) (I : CombCell ι J (n + 1)) :
    combD S J n f I = ∑ k, ∑ i ∈ I.1.1 k,
      if h : ((∀ l, (Function.update I.1.1 k ((I.1.1 k).erase i) l).Nonempty) ∧
          ∑ l, ((Function.update I.1.1 k ((I.1.1 k).erase i) l).card - 1) = n) ∧
          ∀ l, J l ⊆ Function.update I.1.1 k ((I.1.1 k).erase i) l then
        KH.faceSign I.1.1 k i • f ⟨⟨Function.update I.1.1 k ((I.1.1 k).erase i), h.1⟩, h.2⟩
      else 0 := by
  unfold combD
  rw [LinearMap.pi_apply, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs <;> rfl

theorem embed_comm (a : (Σ k, ι k) → ℤ) (n : ℕ) (f : CombC S (negSet a) n) :
    KH.cechD S ι (MRingOver S ι ⧸ (⊥ : Ideal (MRingOver S ι))) n (embed S a n f) =
      embed S a (n + 1) (combD S (negSet a) n f) := by
  classical
  funext I
  rw [cechD_apply, embed_apply]
  by_cases hI : ∀ k, negSet a k ⊆ I.1 k
  · rw [dif_pos hI]
    erw [combD_apply]
    rw [Finset.sum_smul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.sum_smul]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases hc : (∀ l, (Function.update I.1 k ((I.1 k).erase i) l).Nonempty) ∧
        ∑ l, ((Function.update I.1 k ((I.1 k).erase i) l).card - 1) = n
    · rw [dif_pos hc]
      erw [embed_apply]
      by_cases hJ : ∀ l, negSet a l ⊆ Function.update I.1 k ((I.1 k).erase i) l
      · rw [dif_pos hJ, dif_pos ⟨hc, hJ⟩, LinearMap.map_smul_of_tower,
          cellRes_monoFrac (update_erase_subset I.1 k i) a hJ, smul_assoc]
      · rw [dif_neg hJ, dif_neg (fun h => hJ h.2), map_zero]
        simp
    · rw [dif_neg hc, dif_neg (fun h => hc h.1), zero_smul]
  · rw [dif_neg hI]
    refine Finset.sum_eq_zero fun k _ => Finset.sum_eq_zero fun i _ => ?_
    split_ifs with hc
    · erw [embed_apply]
      rw [dif_neg (fun hJ => hI fun l => (hJ l).trans (update_erase_subset I.1 k i l)), map_zero]
      simp
    · rfl

theorem embed_mem (a : (Σ k, ι k) → ℤ) (c d : K → ℤ) (h : blockSum a = c + d) (n : ℕ)
    (f : CombC S (negSet a) n) :
    embed S a n f ∈ KH.cechCc ι (fun c => KH.quotPart S (⊥ : Ideal (MRingOver S ι)) (c + d)) c n := by
  classical
  unfold KH.cechCc
  refine Submodule.mem_pi.mpr fun I _ => ?_
  erw [embed_apply]
  split_ifs with hI
  · refine Submodule.smul_mem _ _ ?_
    unfold monoFrac
    rw [dif_pos hI]
    refine Submodule.subset_span ⟨_, _, fun k => ∑ i, negExp a ⟨k, i⟩,
      isMultiHomog_monomial _ _ _ fun _ => rfl, ?_, rfl⟩
    refine mk_posExp_mem a _ fun k => ?_
    have hk := blockSum_add_negExp a k
    rw [h] at hk
    simp only [Pi.add_apply] at hk ⊢
    linarith
  · exact zero_mem _

theorem monoFrac_of_nonneg (a : (Σ k, ι k) → ℤ) (ha : ∀ p, 0 ≤ a p) :
    ∃ m ∈ KH.quotPart S (⊥ : Ideal (MRingOver S ι)) (blockSum a),
      ∀ I : ∀ k, Finset (ι k), monoFrac S I a = LocalizedModule.mk m 1 := by
  classical
  have hneg : ∀ k, negSet a k = ∅ := fun k =>
    Finset.filter_eq_empty_iff.mpr fun i _ => not_lt.mpr (ha _)
  have hnegExp : negExp a = 0 := by
    ext p
    simp only [negExp, Finsupp.coe_equivFunOnFinite_symm, Finsupp.coe_zero, Pi.zero_apply]
    have := ha p
    omega
  refine ⟨_, mk_posExp_mem a _ fun k => ?_, fun I => ?_⟩
  · have hk := blockSum_add_negExp a k
    rw [hnegExp] at hk
    simpa using hk
  · have hI : ∀ k, negSet a k ⊆ I k := fun k => by rw [hneg k]; exact Finset.empty_subset _
    unfold monoFrac
    rw [dif_pos hI]
    congr 1
    exact Subtype.ext (by simp [hnegExp])

theorem full : KHFreeEmbed.Statement := by
  intro S _ K _ _ ι _ _ a
  exact ⟨fun n f => embed_comm a n f, fun c d h n f => embed_mem a c d h n f, monoFrac_of_nonneg a⟩

end KHFreeEmbed

end

end GroundTheory.Heights₂.Heights.Kleiman
