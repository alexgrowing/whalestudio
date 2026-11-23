import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HasseOrderBound.Development

noncomputable section

open Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions NumberField IsDedekindDomain Module Formalism.MainNotions.Gaps.EtaleWeightGaps

namespace PI.HasseOrdBdW

section

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} (X : PJ D B P j)

def Rep (u : WeightFamilies.Wt D j) (F : X.Forms) : Prop := ∃ g : B.Cusp j u, X.inc u g = F

variable {X}

theorem rep_mul {wL u : WeightFamilies.Wt D j} (x : B.Cusp j wL) {F : X.Forms} (hF : Rep X u F) :
    Rep X (wadd wL u) (X.inc wL x * F) := by
  obtain ⟨g, rfl⟩ := hF
  obtain ⟨H, hH⟩ := X.inc_mul wL u x g
  exact ⟨H, hH.symm⟩

theorem rep_pow (la : HeightOneSpectrum (𝓞 B.KO)) (y : X.Pt la) {wL wF : WeightFamilies.Wt D j} (x : B.Cusp j wL) (d : ℝ)
    (hd : (d : EReal) ≤ X.vAt la y (X.inc wL x)) :
    ∀ (a m : ℕ) (F : X.Forms), Rep X (addL wF wL m) F →
      Rep X (addL wF wL (m + a)) (X.inc wL x ^ a * F) ∧
      X.vAt la y F + (((a : ℝ) * d : ℝ) : EReal) ≤ X.vAt la y (X.inc wL x ^ a * F) := by
  intro a
  induction a with
  | zero =>
    intro m F hF
    simp only [pow_zero, one_mul, Nat.cast_zero, zero_mul, EReal.coe_zero, add_zero]
    exact ⟨hF, le_rfl⟩
  | succ a ih =>
    intro m F hF
    obtain ⟨hR, hv⟩ := ih m F hF
    have hR' := rep_mul x hR
    rw [wadd_addL] at hR'
    refine ⟨by rw [pow_succ', mul_assoc]; exact hR', ?_⟩
    obtain ⟨g, hg⟩ := hR
    rw [pow_succ', mul_assoc, ← hg, X.vAt_mul]
    rw [← hg] at hv
    have e1 : ((((a + 1 : ℕ) : ℝ) * d : ℝ)) = (a : ℝ) * d + d := by push_cast; ring
    rw [e1, EReal.coe_add]
    calc X.vAt la y F + ((((a : ℝ) * d : ℝ) : EReal) + (d : EReal))
        = (d : EReal) + (X.vAt la y F + (((a : ℝ) * d : ℝ) : EReal)) := by ac_rfl
      _ ≤ _ := add_le_add hd hv

theorem rep_prod (la : HeightOneSpectrum (𝓞 B.KO)) (y : X.Pt la) {N : ℕ} {wL wF : WeightFamilies.Wt D j}
    (w : Fin N → B.Cusp j wL) (d : ℝ) (hd : ∀ k, (d : EReal) ≤ X.vAt la y (X.inc wL (w k))) (e : Fin N → ℕ) :
    ∀ (s : Finset (Fin N)) (m : ℕ) (F : X.Forms), Rep X (addL wF wL m) F →
      Rep X (addL wF wL (m + ∑ k ∈ s, e k)) ((∏ k ∈ s, X.inc wL (w k) ^ e k) * F) ∧
      X.vAt la y F + ((((∑ k ∈ s, e k : ℕ) : ℝ) * d : ℝ) : EReal) ≤
        X.vAt la y ((∏ k ∈ s, X.inc wL (w k) ^ e k) * F) := by
  classical
  intro s
  induction s using Finset.induction_on with
  | empty =>
    intro m F hF
    simp only [Finset.prod_empty, Finset.sum_empty, one_mul, add_zero, Nat.cast_zero, zero_mul, EReal.coe_zero]
    exact ⟨hF, le_rfl⟩
  | @insert a s ha ih =>
    intro m F hF
    obtain ⟨hR, hv⟩ := ih m F hF
    obtain ⟨hR2, hv2⟩ := rep_pow la y (w a) d (hd a) (e a) _ _ hR
    rw [Finset.prod_insert ha, Finset.sum_insert ha, mul_assoc]
    refine ⟨?_, ?_⟩
    · have h3 : m + (e a + ∑ k ∈ s, e k) = m + ∑ k ∈ s, e k + e a := by ring
      rw [h3]
      exact hR2
    · calc _ = X.vAt la y F + ((((∑ k ∈ s, e k : ℕ) : ℝ) * d : ℝ) : EReal) + (((e a : ℝ) * d : ℝ) : EReal) := by
            rw [add_assoc, ← EReal.coe_add]
            congr 2
            push_cast
            ring
        _ ≤ _ := le_trans (add_le_add hv le_rfl) hv2

end

theorem orthogonalSplitPolarizationVanishes : S2 := by
  intro D B P j X la y N wL wF w d hd m g e n hn
  subst hn
  obtain ⟨⟨g', hg'⟩, hv⟩ := rep_prod la y w d hd e Finset.univ m (X.inc _ g) ⟨g, rfl⟩
  refine ⟨g', by rw [mul_comm, hg'], ?_⟩
  rw [hg']
  exact hv

end PI.HasseOrdBdW
