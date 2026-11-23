import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatFrame

open MvPowerSeries ReciprocityTheory.PGsh GlobalTheory.FGDepth

namespace GlobalTheory.FGDepth

theorem exists_lipschitz_eval {C : Type} [Field C] (v : AddValuation C (WithTop ℝ)) {ι : Type}
    (Q : MvPolynomial ι C) :
    ∃ K : ℝ, (∀ a : ι → C, (∀ i, IsIntV v (a i)) →
        ((-K : ℝ) : WithTop ℝ) ≤ v (MvPolynomial.eval a Q)) ∧
      ∀ (M : ℝ) (a a' : ι → C), (∀ i, IsIntV v (a i)) → (∀ i, IsIntV v (a' i)) →
        (∀ i, ((M : ℝ) : WithTop ℝ) ≤ v (a i - a' i)) →
        ((M - K : ℝ) : WithTop ℝ) ≤ v (MvPolynomial.eval a Q - MvPolynomial.eval a' Q) := by
  induction Q using MvPolynomial.induction_on with
  | C c =>
    by_cases hc : v c = ⊤
    · exact ⟨0, fun a _ => by simp [hc], fun M a a' _ _ _ => by simp⟩
    · obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.mp hc
      exact ⟨-r, fun a _ => by simp [hr], fun M a a' _ _ _ => by simp⟩
  | add p q hp hq =>
    obtain ⟨K₁, h₁, h₁'⟩ := hp
    obtain ⟨K₂, h₂, h₂'⟩ := hq
    refine ⟨max K₁ K₂, fun a ha => ?_, fun M a a' ha ha' hM => ?_⟩
    · rw [map_add]
      refine v.map_le_add (le_trans ?_ (h₁ a ha)) (le_trans ?_ (h₂ a ha))
      · exact WithTop.coe_le_coe.mpr (neg_le_neg (le_max_left _ _))
      · exact WithTop.coe_le_coe.mpr (neg_le_neg (le_max_right _ _))
    · rw [map_add, map_add, add_sub_add_comm]
      refine v.map_le_add (le_trans ?_ (h₁' M a a' ha ha' hM))
        (le_trans ?_ (h₂' M a a' ha ha' hM))
      · exact WithTop.coe_le_coe.mpr (sub_le_sub_left (le_max_left _ _) _)
      · exact WithTop.coe_le_coe.mpr (sub_le_sub_left (le_max_right _ _) _)
  | mul_X p i hp =>
    obtain ⟨K, h, h'⟩ := hp
    refine ⟨K, fun a ha => ?_, fun M a a' ha ha' hM => ?_⟩
    · rw [map_mul, MvPolynomial.eval_X, v.map_mul]
      exact le_add_of_le_of_nonneg (h a ha) (ha i)
    · rw [map_mul, map_mul, MvPolynomial.eval_X, MvPolynomial.eval_X]
      have e : MvPolynomial.eval a p * a i - MvPolynomial.eval a' p * a' i =
          (MvPolynomial.eval a p - MvPolynomial.eval a' p) * a i +
            MvPolynomial.eval a' p * (a i - a' i) := by ring
      rw [e]
      refine v.map_le_add ?_ ?_
      · rw [v.map_mul]
        exact le_add_of_le_of_nonneg (h' M a a' ha ha' hM) (ha i)
      · rw [v.map_mul]
        have e2 : ((M - K : ℝ) : WithTop ℝ) = ((-K : ℝ) : WithTop ℝ) + ((M : ℝ) : WithTop ℝ) := by
          rw [← WithTop.coe_add]; congr 1; ring
        rw [e2]
        exact add_le_add (h a' ha') (hM i)

theorem exists_poly_derivAt0_subst {C : Type} [Field C] {σ Λ : Type} [Fintype σ] [Fintype Λ]
    (P : MvPolynomial Λ C) (Z : MvPowerSeries σ C) :
    ∃ Q : MvPolynomial (σ × Λ) C, ∀ a : σ → Λ → C,
      derivAt0 P (MvPowerSeries.subst
        (fun s => ∑ l, a s l • (MvPowerSeries.X l : MvPowerSeries Λ C)) Z) =
      MvPolynomial.eval (fun x : σ × Λ => a x.1 x.2) Q := by
  let u : σ → MvPowerSeries Λ (MvPolynomial (σ × Λ) C) :=
    fun s => ∑ l, (MvPolynomial.X (s, l) : MvPolynomial (σ × Λ) C) • MvPowerSeries.X l
  have hu : HasSubst u := hasSubst_of_constantCoeff_zero fun s => by simp [u]
  let Zu : MvPowerSeries Λ (MvPolynomial (σ × Λ) C) :=
    subst u (MvPowerSeries.map (MvPolynomial.C : C →+* MvPolynomial (σ × Λ) C) Z)
  refine ⟨∑ α ∈ P.support, MvPolynomial.C (P.coeff α * mfact α) * coeff α Zu, fun a => ?_⟩
  have key : MvPowerSeries.map (MvPolynomial.eval (fun x : σ × Λ => a x.1 x.2)) Zu =
      MvPowerSeries.subst (fun s => ∑ l, a s l • (MvPowerSeries.X l : MvPowerSeries Λ C)) Z := by
    rw [MvPowerSeries.map_subst hu]
    congr 1
    · funext s
      simp [u, MvPowerSeries.smul_eq_C_mul]
    · ext d
      simp
  rw [← key, derivAt0, map_sum]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [map_mul, MvPolynomial.eval_C, coeff_map]

theorem derivAt0_subst_linear_lipschitz :
    ∀ (C : Type) [Field C] (v : AddValuation C (WithTop ℝ)) (σ Λ : Type) [Fintype σ] [Fintype Λ] (P : MvPolynomial Λ C) (Z : MvPowerSeries σ C), ∃ K : ℝ, ∀ (M : ℝ) (a a' : σ → Λ → C), (∀ s l, IsIntV v (a s l)) → (∀ s l, IsIntV v (a' s l)) → (∀ s l, ((M : ℝ) : WithTop ℝ) ≤ v (a s l - a' s l)) → ((M - K : ℝ) : WithTop ℝ) ≤ v (derivAt0 P (MvPowerSeries.subst (fun s => ∑ l, a s l • (MvPowerSeries.X l : MvPowerSeries Λ C)) Z) - derivAt0 P (MvPowerSeries.subst (fun s => ∑ l, a' s l • (MvPowerSeries.X l : MvPowerSeries Λ C)) Z)) := by
  intro C _ v σ Λ _ _ P Z
  obtain ⟨Q, hQ⟩ := exists_poly_derivAt0_subst P Z
  obtain ⟨K, -, hK⟩ := exists_lipschitz_eval v Q
  refine ⟨K, fun M a a' ha ha' hM => ?_⟩
  rw [hQ, hQ]
  exact hK M _ _ (fun x => ha x.1 x.2) (fun x => ha' x.1 x.2) (fun x => hM x.1 x.2)

end GlobalTheory.FGDepth
