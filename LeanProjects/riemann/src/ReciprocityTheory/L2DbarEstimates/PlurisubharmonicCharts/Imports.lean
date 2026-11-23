import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.BStep
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.SetLIntegralBiUnionLe

namespace ReciprocityTheory.L2DbarEstimates.Y

open MeasureTheory Filter Topology WeightedAtlas
open scoped ContDiff ENNReal Pointwise Matrix

noncomputable section

universe u

theorem b (n : ℕ) (Y : Type u) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι : Type*) (La : Type*) [AddCommGroup La] (hS : SAll.{u} n) (hE : EXTStatement n) (hN : EXTNullStatement n)
    (hLSE : LSEAll.{u} n) (hMVI : MVIntStatement n) : BStatement n Y ι La := by
  classical
  intro A L mu0 N w w0 s De σ T f hn hD hF hX hσ hpos hT hf hint hvan
  have h0 := A.start_int hMVI hn hD hf hT hint hvan
  have key : ∀ m, m ≤ T - n → ∃ hh : (Fin m → Fin n) → ι → Y → ℂ,
      (∀ q, A.IsSec (mu0 + (T - m) • L) (hh q) ∧
        ∫⁻ y, ENNReal.ofReal (A.nsq (mu0 + (T - m) • L) (hh q) y *
          A.sqn L s y ^ (-(((T - m : ℕ) : ℝ) - 1 / 2)) * A.sqn L w y ^ (-(1 / 2 : ℝ))) ∂A.mu
            < ⊤) ∧
      ∀ i y, y ∈ (A.chart i).source → f i y = ∑ q, (∏ j, s (q j) i y) * hh q i y := by
    intro m
    induction m with
    | zero =>
      intro _
      refine ⟨fun _ => f, fun q => ⟨by simpa using hf, by simpa using h0⟩, fun i y _ => ?_⟩
      simp
    | succ m ih =>
      intro hm
      obtain ⟨hh, hhP, hsum⟩ := ih (by omega)
      have hT' : n + 1 ≤ T - m := by omega
      choose H hH hHsum using fun q =>
        b_step A hS hE hN hLSE hn hD hF hX hσ hpos (T - m) hT' (hh q) (hhP q).1 (hhP q).2
      refine ⟨fun q' => H (Fin.tail q') (q' 0), fun q' => ?_, ?_⟩
      · have e1 : T - (m + 1) = T - m - 1 := by omega
        have e2 : (((T - m - 1 : ℕ) : ℝ) - 1 / 2) = ((T - m : ℕ) : ℝ) - 3 / 2 := by
          rw [Nat.cast_sub (show 1 ≤ T - m by omega)]
          push_cast
          ring
        obtain ⟨h1, h2⟩ := hH (Fin.tail q') (q' 0)
        rw [e1, e2]
        exact ⟨h1, h2⟩
      · intro i y hy
        rw [hsum i y hy, ← (Fin.consEquiv (fun _ => Fin n)).sum_comp, Fintype.sum_prod_type]
        simp only [Fin.consEquiv_apply, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ,
]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun q _ => ?_)
        rw [hHsum q i y hy, Finset.mul_sum]
        refine Finset.sum_congr rfl (fun k _ => ?_)
        have et : Fin.tail ((Fin.consEquiv fun _ => Fin n) (k, q)) = q :=
          Fin.tail_cons (α := fun _ => Fin n) k q
        rw [et]
        ring
  obtain ⟨hh, hhP, hsum⟩ := key (T - n) le_rfl
  have eT : T - (T - n) = n := by omega
  rw [eT] at hhP
  set cnt : (Fin (T - n) → Fin n) → Fin n → ℕ :=
    fun q k => (Finset.univ.filter (fun j => q j = k)).card with hcnt
  refine ⟨fun α i y => ∑ q ∈ Finset.univ.filter (fun q => cnt q = α), hh q i y,
    fun α _ => ⟨?_, ?_⟩, ?_⟩
  · exact A.isSec_sum _ (fun q _ => (hhP q).1)
  · exact A.sum_int _ hh (fun q _ => (hhP q).1) (fun y => A.sqn L w y ^ (-(n : ℝ)))
      ((A.continuous_sqn hD.sec_w).measurable.pow_const _)
      (fun y => Real.rpow_nonneg (A.sqn_nonneg _ _ y) _)
      (fun q _ => A.end_int (by omega) hD (hhP q).2)
  · intro i y hy
    rw [hsum i y hy]
    have hmaps : ∀ q ∈ (Finset.univ : Finset (Fin (T - n) → Fin n)),
        cnt q ∈ Finset.Nat.antidiagonalTuple n (T - n) := by
      intro q _
      rw [Finset.Nat.mem_antidiagonalTuple]
      simp only [cnt]
      rw [← Finset.card_eq_sum_card_fiberwise (fun j _ => Finset.mem_univ (q j))]
      simp
    rw [← Finset.sum_fiberwise_of_maps_to hmaps]
    refine Finset.sum_congr rfl (fun α _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun q hq => ?_)
    have hq' : cnt q = α := (Finset.mem_filter.1 hq).2
    congr 1
    rw [← hq', ← Finset.prod_fiberwise Finset.univ q (fun j => s (q j) i y)]
    refine Finset.prod_congr rfl (fun k _ => ?_)
    rw [Finset.prod_congr rfl (fun j hj => by rw [(Finset.mem_filter.1 hj).2]), Finset.prod_const]

end

end ReciprocityTheory.L2DbarEstimates.Y
