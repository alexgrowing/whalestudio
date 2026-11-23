import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.OddThetaFunctionExistenceUniqueness
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DifferentiableSqTh
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EvenThetaEqProdSigmaStarSquareQuotientStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EvenThetaTwoTorsionBasicPropertiesStatement
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators

noncomputable section

namespace GlobalTheory.EvenTheta.Fibres

def trFac (Λ : AddSubgroup ℂ) (z ω : ℂ) : ℂ :=
  Complex.exp (-(Real.pi : ℂ) * z * (starRingEnd ℂ) ω / (area Λ : ℂ) -
    (Real.pi : ℂ) * ω * (starRingEnd ℂ) ω / (2 * (area Λ : ℂ)))

variable {Λ : AddSubgroup ℂ}

theorem thetaTranslationOperator_apply (ω : ℂ) (G : ℂ → ℂ) (z : ℂ) : U1 Λ ω G z = G (z + ω) * trFac Λ z ω := rfl

theorem trFac_mul {β : ℂ} {n : ℕ} (hb : β * starRingEnd ℂ β = (n : ℂ)) (z ω : ℂ) :
    trFac Λ (β * z) (β * ω) = trFac Λ z ω ^ n := by
  simp only [trFac]
  rw [← Complex.exp_nat_mul, ← hb, map_mul]
  congr 1
  ring

theorem trFac_add_sub (v z ω : ℂ) :
    trFac Λ (v + z) ω * trFac Λ (z - v) ω = trFac Λ z ω ^ 2 := by
  simp only [trFac]
  rw [← Complex.exp_nat_mul, ← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem sg_sq (h : IsLat Λ) {ω : ℂ} (hω : ω ∈ Λ) (z : ℂ) :
    sgStar Λ (z + ω) ^ 2 * trFac Λ z ω ^ 2 = sgStar Λ z ^ 2 := by
  rw [← mul_pow, ← thetaTranslationOperator_apply, h.sg_law hω]
  split_ifs <;> ring

theorem sqTh_law (h : IsLat Λ) {ω : ℂ} (hω : ω ∈ Λ) (v z : ℂ) :
    sqTh Λ v (z + ω) * trFac Λ z ω ^ 2 = sqTh Λ v z := by
  have h1 := h.sg_law hω (v + z)
  have h2 := h.sg_law hω (z - v)
  rw [thetaTranslationOperator_apply] at h1 h2
  have e1 : sgStar Λ (v - (z + ω)) = -sgStar Λ (z - v + ω) := by
    rw [← h.sg_neg]; congr 1; ring
  have e2 : sgStar Λ (v - z) = -sgStar Λ (z - v) := by
    rw [← h.sg_neg]; congr 1; ring
  have e3 : sgStar Λ (v + z + ω) * sgStar Λ (z - v + ω) * trFac Λ z ω ^ 2 =
      sgStar Λ (v + z) * sgStar Λ (z - v) := by
    rw [← trFac_add_sub v, mul_mul_mul_comm, h1, h2]
    split_ifs <;> ring
  simp only [sqTh]
  rw [e1, e2, ← add_assoc]
  linear_combination (-1 / sgStar Λ v ^ 2) * e3

theorem law_of_fac (h : IsLat Λ) {F : ℂ → ℂ} {k : ℕ} {ω : ℂ} (hω : ω ∈ Λ) (z : ℂ)
    (hF : F (z + ω) * trFac Λ z ω ^ (2 * k) = F z) :
    F (z + ω) * sgStar Λ z ^ (2 * k) = F z * sgStar Λ (z + ω) ^ (2 * k) := by
  rw [← hF, pow_mul (sgStar Λ z), ← sg_sq h hω z]
  ring

theorem isogeny_fibres : ∀ Λ : AddSubgroup ℂ, IsLat Λ → ∀ (β t₀ : ℂ) (k : ℕ), (∀ ω ∈ Λ, β * ω ∈ Λ) → β + starRingEnd ℂ β = 1 → β * starRingEnd ℂ β = ((2 * k : ℕ) : ℂ) → 2 * t₀ ∈ Λ → β * t₀ ∉ Λ → (1 - β) * t₀ ∉ Λ → ∃ (Q : Fin k → ℂ) (Q' : Fin (2 * k) → ℂ), (∀ i, Q i ∉ Λ ∧ InRationalLattice Λ (Q i)) ∧ (∀ j, Q' j ∉ Λ ∧ InRationalLattice Λ (Q' j)) ∧ (∀ z, GL3Theta.th0 Λ t₀ (β * z) = ∏ i, sqTh Λ (Q i) z) ∧ (∀ z, sqTh Λ (β * t₀) (β * z) = ∏ j, sqTh Λ (Q' j) z) ∧ (∀ i j, wpF Λ (Q i) ≠ wpF Λ (Q' j)) ∧ (∃ j, wpF Λ (Q' j) = wpF Λ t₀) ∧ (∃ j, wpF Λ (Q' j) = wpF Λ (β * t₀)) ∧ wpF Λ t₀ ≠ wpF Λ (β * t₀) := by
  intro Λ h β t₀ k hβ htr hN h2 h1 h1'
  have hβ' : ∀ ω ∈ Λ, (1 - β) * ω ∈ Λ := fun ω hω => by
    rw [sub_mul, one_mul]; exact Λ.sub_mem hω (hβ ω hω)
  have hN' : β * (1 - β) = 2 * (k : ℂ) := by
    rw [← htr, add_sub_cancel_left, hN]; push_cast; ring
  have ht₀ : t₀ ∉ Λ := fun hh => h1 (hβ _ hh)
  have hk : 0 < k := by
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · exfalso
      simp only [Nat.cast_zero, mul_zero, mul_eq_zero] at hN'
      rcases hN' with h0 | h0
      · exact h1 (by rw [h0, zero_mul]; exact Λ.zero_mem)
      · exact h1' (by rw [h0, zero_mul]; exact Λ.zero_mem)
    · exact hk
  have hnat : ∀ (n : ℕ) (x : ℂ), x ∈ Λ → (n : ℂ) * x ∈ Λ := fun n x hx => by
    rw [← nsmul_eq_mul]; exact Λ.nsmul_mem hx n
  have h2t₁ : 2 * (β * t₀) ∈ Λ := by
    convert hβ _ h2 using 1; ring
  have hplus : t₀ + β * t₀ ∉ Λ := fun hh => h1' (by
    convert Λ.sub_mem hh h2t₁ using 1; ring)
  have hminus : t₀ - β * t₀ ∉ Λ := fun hh => h1' (by
    convert hh using 1; ring)
  have hla : ∀ x : ℂ, 2 * (β * x) ∈ Λ → InRationalLattice Λ x := fun x hx =>
    ⟨4 * k, by omega, by
      convert hβ' _ hx using 1
      push_cast
      linear_combination (-2 * x) * hN'⟩
  obtain ⟨hd, h0, hev, -, hz, hU⟩ := GlobalTheory.T.th0_zero_even_sq_zeros_and_periodicity Λ h t₀ ht₀ h2
  obtain ⟨Q, hQ, hQe⟩ := GlobalTheory.T.evenTheta_eq_prod_sigmaStarSquareQuotient Λ h k (fun z => GL3Theta.th0 Λ t₀ (β * z))
    (hd.comp (by fun_prop)) (fun z => by rw [mul_neg, hev]) (by rw [mul_zero, h0])
    (fun ω hω z => law_of_fac h (F := fun z => GL3Theta.th0 Λ t₀ (β * z)) hω z (by
      have hn : β * ω / 2 + t₀ ∉ Λ := fun hh => h1' (by
        convert Λ.sub_mem (hβ' _ hh) (hnat k ω hω) using 1
        linear_combination (-ω / 2) * hN')
      have := hU _ (hβ ω hω) hn (β * z)
      rw [thetaTranslationOperator_apply, trFac_mul hN] at this
      simpa only [mul_add] using this))
  obtain ⟨Q', hQ', hQe'⟩ := GlobalTheory.T.evenTheta_eq_prod_sigmaStarSquareQuotient Λ h (2 * k) (fun z => sqTh Λ (β * t₀) (β * z))
    ((h.differentiable_sqTh _).comp (by fun_prop)) (fun z => by rw [mul_neg, sqTh_neg])
    (by rw [mul_zero, h.sqTh_zero h1])
    (fun ω hω z => law_of_fac h (F := fun z => sqTh Λ (β * t₀) (β * z)) hω z (by
      have := sqTh_law h (hβ ω hω) (β * t₀) (β * z)
      rw [trFac_mul hN, ← pow_mul, mul_comm (2 * k) 2] at this
      simpa only [mul_add] using this))
  have hA : ∀ i, β * Q i + t₀ ∈ Λ := fun i => by
    rw [← hz, hQe]
    exact Finset.prod_eq_zero (Finset.mem_univ i)
      ((h.sqTh_eq_zero (hQ i) _).2 (Or.inr (by rw [sub_self]; exact Λ.zero_mem)))
  have hB : ∀ j, β * t₀ + β * Q' j ∈ Λ ∨ β * t₀ - β * Q' j ∈ Λ := fun j => by
    rw [← h.sqTh_eq_zero h1, hQe']
    exact Finset.prod_eq_zero (Finset.mem_univ j)
      ((h.sqTh_eq_zero (hQ' j) _).2 (Or.inr (by rw [sub_self]; exact Λ.zero_mem)))
  have hC : ∀ x : ℂ, x ∉ Λ → β * t₀ - β * x ∈ Λ → ∃ j, wpF Λ (Q' j) = wpF Λ x := fun x hx hx' => by
    have h3 := (h.sqTh_eq_zero h1 (β * x)).2 (Or.inr hx')
    rw [hQe', Finset.prod_eq_zero_iff] at h3
    obtain ⟨j, -, hj⟩ := h3
    exact ⟨j, ((h.wp_eq_iff (hQ' j) hx).2 ((h.sqTh_eq_zero (hQ' j) x).1 hj)).symm⟩
  refine ⟨Q, Q', fun i => ⟨hQ i, hla _ ?_⟩, fun j => ⟨hQ' j, hla _ ?_⟩, hQe, hQe', ?_,
    hC _ ht₀ (by rw [sub_self]; exact Λ.zero_mem), hC _ h1 ?_, ?_⟩
  · convert Λ.sub_mem (hnat 2 _ (hA i)) h2 using 1
    push_cast; ring
  · rcases hB j with hj | hj
    · convert Λ.sub_mem (hnat 2 _ hj) h2t₁ using 1
      push_cast; ring
    · convert Λ.sub_mem h2t₁ (hnat 2 _ hj) using 1
      push_cast; ring
  · intro i j hij
    have ha := hA i
    rcases (h.wp_eq_iff (hQ i) (hQ' j)).1 hij.symm with hc | hc <;> rcases hB j with hj | hj
    · exact hplus (by convert Λ.sub_mem (Λ.add_mem ha hj) (hβ _ hc) using 1; ring)
    · exact hminus (by convert Λ.sub_mem (Λ.sub_mem ha hj) (hβ _ hc) using 1; ring)
    · exact hminus (by convert Λ.sub_mem (Λ.sub_mem ha hj) (hβ _ hc) using 1; ring)
    · exact hplus (by convert Λ.sub_mem (Λ.add_mem ha hj) (hβ _ hc) using 1; ring)
  · convert hnat k _ h2 using 1
    linear_combination t₀ * hN'
  · intro he
    rcases (h.wp_eq_iff ht₀ h1).1 he.symm with hc | hc
    · exact hplus hc
    · exact hminus hc

end GlobalTheory.EvenTheta.Fibres
