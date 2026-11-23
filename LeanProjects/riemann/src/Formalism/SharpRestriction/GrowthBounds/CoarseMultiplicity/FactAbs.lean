import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.BFDefs
import Formalism.SharpRestriction.GrowthBounds.RootWeights.PadicGeMulNat

noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees Formalism.MainNotions.G.GLWeightTheory

theorem fact_abs {D : Formalism.BasicNotions.D7} (h52 : Formalism.MainNotions.CovariantDegrees.FactorialUnitDecomposition D) {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) (σ : Type)
    [Fintype σ] [DecidableEq σ] (odd : σ → Prop) [DecidablePred odd] (t ρ L : σ → ℕ)
    (hodd : ∀ v, odd v → L v = p ^ (t v + 1) ∧ ρ v < L v) (hend : ∀ v, ¬ odd v → L v = 1 ∧ ρ v = 0) (c : ℕ) :
    ∃ (T : Finset (σ →₀ ℕ)) (q : (σ →₀ ℕ) → ℚ),
      (∀ ν ∈ T, (ν.sum fun _ n => n) ≤ 4 * c ∧ (∀ v ∈ ν.support, odd v) ∧ PadicGe p (q ν) 0) ∧
      ∀ μ : σ →₀ ℕ, ∃ h : ℚ, PadicGe p h c ∧
        (∏ v, ((ρ v + L v * μ v).factorial : ℚ)) *
            (∑ ν ∈ T, q ν * ((ν.prod fun k i => (μ k).choose i : ℕ) : ℚ)) =
          (∏ v, ((ρ v).factorial : ℚ) * ((μ v).factorial : ℚ) * ((L v).factorial : ℚ) ^ (μ v)) * (1 + h) := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨h1, h2⟩ := h52 p hp h5
  set t' : σ → ℕ := fun v => if odd v then t v else 0 with ht'
  set ρ' : σ → ℕ := fun v => if odd v then ρ v else 0 with hρ'
  have hlt : ∀ k, ρ' k < p ^ (t' k + 1) := by
    intro k
    by_cases hk : odd k
    · simp only [hρ', ht', if_pos hk]
      rw [← (hodd k hk).1]; exact (hodd k hk).2
    · simp only [hρ', ht', if_neg hk]
      exact pow_pos hp.pos _
  obtain ⟨hunit, -, hop⟩ := h2 σ t' ρ' hlt
  obtain ⟨T, q, hT, hq⟩ := hop true c
  let E : (σ → ℕ) → (σ →₀ ℕ) := fun j => Finsupp.equivFunOnFinite.symm j
  have hE : Function.Injective E := Finsupp.equivFunOnFinite.symm.injective
  have hEa : ∀ j v, E j v = j v := fun j v => rfl
  refine ⟨(T.filter fun j => ∀ v, ¬ odd v → j v = 0).image E, fun ν => q ν, ?_, ?_⟩
  · intro ν hν
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hν
    obtain ⟨hjT, hj0⟩ := Finset.mem_filter.1 hj
    refine ⟨?_, ?_, ?_⟩
    · rw [Finsupp.sum_fintype _ _ (fun _ => rfl)]
      exact (hT j hjT).1
    · intro v hv
      by_contra hno
      exact (Finsupp.mem_support_iff.1 hv) (hj0 v hno)
    · exact (hT j hjT).2
  · intro μ
    set e' : σ → ℕ := fun v => if odd v then μ v else 0 with he'
    set U : ℚ := ∏ k, cUnit (p ^ (t' k + 1)) (e' k) * dUnit (p ^ (t' k + 1)) (e' k) (ρ' k) with hU
    set A : ℚ := ∏ k, (((ρ' k + p ^ (t' k + 1) * e' k).factorial : ℕ) : ℚ) with hA
    set B : ℚ := ∏ k, ((ρ' k).factorial : ℚ) * ((e' k).factorial : ℚ) * ((p ^ (t' k + 1)).factorial : ℚ) ^ (e' k) with hB
    set g : ℚ := ∑ j ∈ T, q j * ∏ k, ((e' k).choose (j k) : ℚ) with hg
    have hU0 : U ≠ 0 := (hunit e').1
    have hUv : padicValRat p U = 0 := (hunit e').2
    have hAB : A = B * U := by
      rw [hA, hB, hU, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun k _ => ?_
      rw [h1 (t' k) (ρ' k) (e' k) (hlt k)]
      ring
    have hB0 : B ≠ 0 := by
      rw [hB]
      refine Finset.prod_ne_zero_iff.2 fun k _ => ?_
      have a1 : ((ρ' k).factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
      have a2 : ((e' k).factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
      have a3 : ((p ^ (t' k + 1)).factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
      exact mul_ne_zero (mul_ne_zero a1 a2) (pow_ne_zero _ a3)
    have hq' : PadicGe p (U⁻¹ - g) c := by
      have := hq e'
      simp only [if_true] at this
      have e : A / B = U := by rw [hAB]; field_simp
      rw [← hA, ← hB, e] at this
      exact this
    have hgs : (∑ ν ∈ (T.filter fun j => ∀ v, ¬ odd v → j v = 0).image E,
        q ν * ((ν.prod fun k i => (μ k).choose i : ℕ) : ℚ)) = g := by
      rw [Finset.sum_image fun a _ b _ h => hE h, hg, Finset.sum_filter]
      refine Finset.sum_congr rfl fun j _ => ?_
      by_cases hj : ∀ v, ¬ odd v → j v = 0
      · rw [if_pos hj, Finsupp.prod_fintype _ _ (fun _ => Nat.choose_zero_right _)]
        push_cast
        congr 1
        refine Finset.prod_congr rfl fun k _ => ?_
        by_cases hk : odd k
        · simp only [he', if_pos hk, hEa]
        · simp only [he', if_neg hk, hEa, hj k hk, Nat.choose_zero_right]
      · rw [if_neg hj]
        push_neg at hj
        obtain ⟨v, hv, hjv⟩ := hj
        have : (∏ k, ((e' k).choose (j k) : ℚ)) = 0 := by
          refine Finset.prod_eq_zero (Finset.mem_univ v) ?_
          simp only [he', if_neg hv]
          rw [Nat.choose_eq_zero_of_lt (Nat.pos_of_ne_zero hjv)]
          simp
        rw [this, mul_zero]
    refine ⟨(-U) * (U⁻¹ - g), ?_, ?_⟩
    · have hU' : PadicGe p (-U) 0 := padicGe_neg (Or.inr (by rw [hUv]; simp))
      have := padicGe_mul hU' hq'
      simpa using this
    · rw [hgs]
      set M : ℚ := ∏ v, (if odd v then (1 : ℚ) else ((μ v).factorial : ℚ)) with hM
      have l1 : (∏ v, ((ρ v + L v * μ v).factorial : ℚ)) = A * M := by
        rw [hA, hM, ← Finset.prod_mul_distrib]
        refine Finset.prod_congr rfl fun v _ => ?_
        by_cases hv : odd v
        · simp only [hρ', ht', he', if_pos hv, (hodd v hv).1, mul_one]
        · simp only [hρ', ht', he', if_neg hv, (hend v hv).1, (hend v hv).2]
          simp
      have l2 : (∏ v, ((ρ v).factorial : ℚ) * ((μ v).factorial : ℚ) * ((L v).factorial : ℚ) ^ (μ v)) = B * M := by
        rw [hB, hM, ← Finset.prod_mul_distrib]
        refine Finset.prod_congr rfl fun v _ => ?_
        by_cases hv : odd v
        · simp only [hρ', ht', he', if_pos hv, (hodd v hv).1, mul_one]
        · simp only [hρ', ht', he', if_neg hv, (hend v hv).1, (hend v hv).2]
          simp
      rw [l1, l2, hAB]
      field_simp
      ring

end Formalism.MainNotions.ColumnSystems.Pf
