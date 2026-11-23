import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsLiftSpread
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PLiftSpreadRead
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PChartDenominator
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

namespace LiftSpread

theorem exists_common {α : Type} [Fintype α] (Q : α → ℕ → Prop) (hQ : ∀ a n k, Q a n → Q a (k * n))
    (h : ∀ a, ∃ n, 1 ≤ n ∧ Q a n) : ∃ n, 1 ≤ n ∧ ∀ a, Q a n := by
  classical
  choose N hN1 hN using h
  refine ⟨∏ a, N a, Nat.one_le_iff_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr fun a _ => by
    have := hN1 a; omega), fun a => ?_⟩
  obtain ⟨m, hm⟩ := Finset.dvd_prod_of_mem N (Finset.mem_univ a)
  rw [hm, mul_comm]
  exact hQ a _ m (hN a)

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

omit [∀ k, Fintype (ι k)] in

theorem prod_zpow_nsmul (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (t : ℕ) (a : K → ℤ) :
    ∏ k, y ⟨k, c k⟩ ^ (-(t • a) k) = ∏ _l : Fin t, ∏ k, y ⟨k, c k⟩ ^ (-a k) := by
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← Finset.prod_pow]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [← zpow_natCast, ← zpow_mul]
  congr 1
  simp only [Pi.smul_apply, nsmul_eq_mul]
  ring

theorem prod_mem_chartLat (y : (Σ k, ι k) → Ω) {σ : Type} (t : ℕ) (a : K → ℤ) (x : σ → Ω)
    (hx : ∀ j, x j ∈ chartLat y a 1) (f : Fin t → σ) : ∏ l, x (f l) ∈ chartLat y (t • a) 1 := by
  intro c hc
  have hW : ∀ j, x j * ∏ k, y ⟨k, c k⟩ ^ (-a k) ∈ chartRingZ y c := fun j => by
    have h := hx j c hc
    simpa only [Nat.cast_one, one_mul] using h
  simp only [Nat.cast_one, one_mul]
  rw [prod_zpow_nsmul, ← Finset.prod_mul_distrib]
  exact Subalgebra.prod_mem _ fun l _ => hW (f l)

end LiftSpread

theorem LiftSpread.proof : LiftSpread.Statement := by
  intro K _ _ ι _ _ Ω _ _ y D N _ hA
  classical
  obtain ⟨q, hq, hgen, -⟩ := hA
  obtain ⟨σ, _, s, hs, hrel⟩ := GenRead.exists_sections_of_generatedV y hgen

  obtain ⟨M, hM1, hM⟩ := LiftSpread.exists_common (fun j n => (n : Ω) * s j ∈ chartLat y (q • N) 1)
    (fun j n k h => by
      have e : ((k * n : ℕ) : Ω) * s j = k • ((n : Ω) * s j) := by
        rw [nsmul_eq_mul]; push_cast; ring
      rw [e]
      exact AddSubgroup.nsmul_mem _ h k)
    (fun j => ChartDenominator.proof K ι Ω y (q • N) 1 (s j) (hs j))

  have hrel' : ∀ c : ∀ k, ι k, ∃ v : σ → Ω, (∀ k, y ⟨k, c k⟩ ≠ 0) → (∀ j, v j ∈ chartRingQ y c) ∧
      ∑ j, v j * (s j * ∏ k, y ⟨k, c k⟩ ^ (-(q • N) k)) = 1 := fun c => by
    by_cases hc : ∀ k, y ⟨k, c k⟩ ≠ 0
    · obtain ⟨v, hv⟩ := hrel c hc
      exact ⟨v, fun _ => hv⟩
    · exact ⟨0, fun h => absurd h hc⟩
  choose v hv using hrel'
  obtain ⟨Δ, hΔ1, hΔ⟩ := LiftSpread.exists_common (α := (∀ k, ι k) × σ)
    (fun p n => (∀ k, y ⟨k, p.1 k⟩ ≠ 0) → (n : Ω) * v p.1 p.2 ∈ chartRingZ y p.1)
    (fun p n k h hc => by
      rw [Nat.cast_mul, mul_assoc]
      exact mul_mem (natCast_mem _ k) (h hc))
    (fun p => by
      by_cases hc : ∀ k, y ⟨k, p.1 k⟩ ≠ 0
      · obtain ⟨n, hn, h⟩ := exists_nat_mul_mem_adjoin_int _ ((hv p.1 hc).1 p.2)
        exact ⟨n, hn, fun _ => h⟩
      · exact ⟨1, le_rfl, fun h => absurd h hc⟩)
  refine ⟨q, Δ * M, 0, hq, Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega)), fun t _ => ?_⟩

  let e := Fintype.equivFin (Fin t → σ)
  refine ⟨Fintype.card (Fin t → σ), fun i => ∏ l, (M : Ω) * s (e.symm i l), fun i => ?_, fun c hc => ?_⟩
  · rw [mul_smul]
    exact LiftSpread.prod_mem_chartLat y t (q • N) _ hM (e.symm i)
  · refine ⟨t, fun i => ∏ l, (Δ : Ω) * v c (e.symm i l), fun i => ?_, ?_⟩
    · exact Subalgebra.prod_mem _ fun l _ => hΔ (c, e.symm i l) hc
    · set w := ∏ k, y ⟨k, c k⟩ ^ (-(q • N) k) with hw
      have hbase : ∑ j, (Δ : Ω) * v c j * ((M : Ω) * s j * w) = ((Δ * M : ℕ) : Ω) := by
        have h1 := (hv c hc).2
        calc ∑ j, (Δ : Ω) * v c j * ((M : Ω) * s j * w) = (Δ : Ω) * M * ∑ j, v c j * (s j * w) := by
              rw [Finset.mul_sum]
              exact Finset.sum_congr rfl fun j _ => by ring
          _ = ((Δ * M : ℕ) : Ω) := by rw [h1]; push_cast; ring
      rw [e.symm.sum_comp (fun f : Fin t → σ =>
        (∏ l, (Δ : Ω) * v c (f l)) * ((∏ l, (M : Ω) * s (f l)) *
          ∏ k, y ⟨k, c k⟩ ^ (-((t * q) • N) k)))]
      calc ∑ f : Fin t → σ, (∏ l, (Δ : Ω) * v c (f l)) * ((∏ l, (M : Ω) * s (f l)) *
            ∏ k, y ⟨k, c k⟩ ^ (-((t * q) • N) k))
          = ∑ f : Fin t → σ, ∏ l, ((Δ : Ω) * v c (f l) * ((M : Ω) * s (f l) * w)) := by
            refine Finset.sum_congr rfl fun f _ => ?_
            rw [mul_smul, LiftSpread.prod_zpow_nsmul, ← hw, ← Finset.prod_mul_distrib,
              ← Finset.prod_mul_distrib]
        _ = (∑ j, (Δ : Ω) * v c j * ((M : Ω) * s j * w)) ^ t := by
            rw [Finset.sum_pow', Fintype.piFinset_univ]
        _ = ((Δ * M : ℕ) : Ω) ^ t := by rw [hbase]

end GroundTheory.Heights₂.Heights.HilbertSamuel
