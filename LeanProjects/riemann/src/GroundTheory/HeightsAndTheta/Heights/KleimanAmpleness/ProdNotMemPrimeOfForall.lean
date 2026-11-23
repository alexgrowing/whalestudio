import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsFurtherLast
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ExistsSumEqOneOfMulEqOne
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (chartRingOver)

noncomputable section

section Between

variable {S : Type} [CommRing S] {Ω : Type} [Field Ω] [Algebra S Ω]

theorem prod_notMem_prime_of_forall {K : Type} [Fintype K] {A : Subalgebra S Ω} {p : Ideal A} (hp : p.IsPrime)
    (f : K → Ω) (hf : ∀ k, f k ∈ A) (hnot : ∀ k, (⟨f k, hf k⟩ : A) ∉ p) :
    (⟨∏ k, f k, prod_mem fun k _ => hf k⟩ : A) ∉ p := by
  have := hp
  have h : (⟨∏ k, f k, prod_mem fun k _ => hf k⟩ : A) = ∏ k, (⟨f k, hf k⟩ : A) :=
    Subtype.ext (by simp)
  rw [h, Ideal.IsPrime.prod_mem_iff]
  rintro ⟨k, -, hk⟩
  exact hnot k hk

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}

theorem blockRing_between (y : (Σ k, ι k) → Ω) (k₀ : K) (j : ι k₀) (c : ∀ k, ι k) (hcj : c k₀ = j)
    (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) (w : ∀ k, ι k → Ω)
    (hw : ∀ k a b, y ⟨k, a⟩ * w k b ∈
      chartRingOver S (IndefiniteRowSideFullHecke.Kleiman2.oneBlock (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀)) (fun _ => j))
    (b : ∀ k, ι k) :
    chartRingOver S (IndefiniteRowSideFullHecke.Kleiman2.oneBlock (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀)) (fun _ => j) ≤ chartRingOver S y c ∧
      chartRingOver S y c ≤ powMulMem _ (∏ k, y ⟨k, c k⟩ * w k (b k)) (prod_mem fun k _ => hw k (c k) (b k)) := by
  subst hcj
  refine ⟨?_, ?_⟩
  · refine Algebra.adjoin_le ?_
    rintro _ ⟨⟨⟨⟩, i⟩, rfl⟩
    exact Algebra.subset_adjoin ⟨⟨k₀, i⟩, rfl⟩
  · refine Algebra.adjoin_le ?_
    rintro _ ⟨⟨k, a⟩, rfl⟩
    refine ⟨1, ?_⟩
    have hk := hc k
    have h : (∏ k', y ⟨k', c k'⟩ * w k' (b k')) ^ 1 * (y ⟨k, a⟩ / y ⟨k, c k⟩) =
        y ⟨k, a⟩ * w k (b k) * ∏ k' ∈ Finset.univ.erase k, y ⟨k', c k'⟩ * w k' (b k') := by
      rw [pow_one, ← Finset.mul_prod_erase _ _ (Finset.mem_univ k)]
      field_simp
    rw [h]
    exact Subalgebra.mul_mem _ (hw k a (b k)) (prod_mem fun k' _ => hw k' (c k') (b k'))

end Between

theorem ModelOfBlockGen.proof : ModelOfBlockGen.Statement := by
  intro S _ K _ _ ι _ Ω _ _ y k₀ hy hBG
  refine ⟨hy, ?_⟩
  show IndefiniteRowSideFullHecke.Kleiman2.modelPts S y = IndefiniteRowSideFullHecke.Kleiman2.modelPts S (IndefiniteRowSideFullHecke.Kleiman2.oneBlock (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀))
  ext z
  constructor
  · rintro ⟨c, hc, P, hP, rfl⟩
    choose w hw hsum using hBG (c k₀) (hc k₀)
    have hAc : ∀ k b, y ⟨k, c k⟩ * w k b ∈ chartRingOver S y c := fun k b =>
      (blockRing_between y k₀ (c k₀) c rfl hc w hw c).1 (hw k (c k) b)
    have hb : ∀ k, ∃ b, (⟨_, hAc k b⟩ : chartRingOver S y c) ∉ P := by
      intro k
      by_contra h
      push Not at h
      apply hP.ne_top
      rw [Ideal.eq_top_iff_one]
      have hk := hc k
      have h1 : (1 : chartRingOver S y c) = ∑ b, (⟨y ⟨k, b⟩ / y ⟨k, c k⟩,
          Algebra.subset_adjoin ⟨⟨k, b⟩, rfl⟩⟩ : chartRingOver S y c) * ⟨_, hAc k b⟩ := by
        apply Subtype.ext
        simp only [Subalgebra.coe_one, AddSubmonoidClass.coe_finsetSum, Subalgebra.coe_mul]
        rw [← hsum k]
        refine Finset.sum_congr rfl fun b _ => ?_
        field_simp
      rw [h1]
      exact Ideal.sum_mem _ fun b _ => P.mul_mem_left _ (h b)
    choose b hb using hb
    obtain ⟨hAB, hle⟩ := blockRing_between y k₀ (c k₀) c rfl hc w hw b
    have heP := prod_notMem_prime_of_forall hP (fun k => y ⟨k, c k⟩ * w k (b k)) (fun k => hAc k (b k)) hb
    have hP' : (P.comap (Subalgebra.inclusion hAB)).IsPrime := Ideal.comap_isPrime _ _
    exact ⟨fun _ => c k₀, fun _ => hc k₀, _, hP',
      locIn_eq_of_le_powMulMem hAB (prod_mem fun k _ => hw k (c k) (b k)) hle P hP heP⟩
  · rintro ⟨c₀, hc₀, p, hp, rfl⟩
    obtain ⟨j, rfl⟩ : ∃ j, c₀ = fun _ => j := ⟨c₀ (), funext fun _ => rfl⟩
    have hj : y ⟨k₀, j⟩ ≠ 0 := hc₀ ()
    choose w hw hsum using hBG j hj
    let A := chartRingOver S (IndefiniteRowSideFullHecke.Kleiman2.oneBlock (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀)) (fun _ => j)
    have hd : ∀ k, ∃ d, (⟨_, hw k d d⟩ : A) ∉ p := by
      intro k
      by_contra h
      push Not at h
      apply hp.ne_top
      rw [Ideal.eq_top_iff_one]
      have h1 : (1 : A) = ∑ b, (⟨_, hw k b b⟩ : A) := by
        apply Subtype.ext
        simp only [Subalgebra.coe_one, AddSubmonoidClass.coe_finsetSum]
        exact (hsum k).symm
      rw [h1]
      exact Ideal.sum_mem _ fun b _ => h b
    choose d hd using hd
    obtain ⟨b₀, hb₀⟩ : ∃ b, (⟨_, hw k₀ j b⟩ : A) ∉ p := by
      by_contra h
      push Not at h
      apply hp.ne_top
      rw [Ideal.eq_top_iff_one]
      have h1 : (1 : A) = ∑ b, (⟨y ⟨k₀, b⟩ / y ⟨k₀, j⟩, Algebra.subset_adjoin ⟨⟨(), b⟩, rfl⟩⟩ : A) *
          ⟨_, hw k₀ j b⟩ := by
        apply Subtype.ext
        simp only [Subalgebra.coe_one, AddSubmonoidClass.coe_finsetSum, Subalgebra.coe_mul]
        rw [← hsum k₀]
        refine Finset.sum_congr rfl fun b _ => ?_
        field_simp
      rw [h1]
      exact Ideal.sum_mem _ fun b _ => p.mul_mem_left _ (h b)
    let c : ∀ k, ι k := Function.update d k₀ j
    let b : ∀ k, ι k := Function.update d k₀ b₀
    have hcb : ∀ k, (⟨_, hw k (c k) (b k)⟩ : A) ∉ p := by
      intro k
      by_cases hk : k = k₀
      · subst k
        have h : (⟨_, hw k₀ (c k₀) (b k₀)⟩ : A) = ⟨_, hw k₀ j b₀⟩ := Subtype.ext (by simp [c, b])
        rw [h]
        exact hb₀
      · have h : (⟨_, hw k (c k) (b k)⟩ : A) = ⟨_, hw k (d k) (d k)⟩ :=
          Subtype.ext (by simp [c, b, Function.update_of_ne hk])
        rw [h]
        exact hd k
    have hc : ∀ k, y ⟨k, c k⟩ ≠ 0 := by
      intro k h0
      apply hcb k
      have h : (⟨_, hw k (c k) (b k)⟩ : A) = 0 := Subtype.ext (by simp [h0])
      rw [h]
      exact p.zero_mem
    obtain ⟨hAB, hle⟩ := blockRing_between y k₀ j c (by simp [c]) hc w hw b
    have hep := prod_notMem_prime_of_forall hp (fun k => y ⟨k, c k⟩ * w k (b k)) (fun k => hw k (c k) (b k)) hcb
    obtain ⟨P, hP, hPeq⟩ := exists_isPrime_locIn_eq hAB _ hle p hp hep
    exact ⟨c, hc, P, hP, hPeq.symm⟩

end

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
