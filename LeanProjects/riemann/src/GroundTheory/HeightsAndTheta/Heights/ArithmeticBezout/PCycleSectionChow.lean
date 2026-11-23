import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsMahler
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

theorem isChowFormCycle_zero_one {F : Type*} [Field F] {n k : ℕ} :
    IsChowFormCycle (0 : ProjCycle F n) k 1 :=
  ⟨1, one_ne_zero, fun _ => 1, by simp, by simp⟩

theorem IsChowFormCycle.C_mul {F : Type*} [Field F] {n k : ℕ} {Z : ProjCycle F n}
    {f : MvPolynomial (Fin k × Fin n) F} (hf : IsChowFormCycle Z k f) {c : F} (hc : c ≠ 0) :
    IsChowFormCycle Z k (C c * f) := by
  obtain ⟨c', hc', g, hg, rfl⟩ := hf
  exact ⟨c * c', mul_ne_zero hc hc', g, hg, by rw [MvPolynomial.C_mul, mul_assoc]⟩

theorem CycleSectionChow.proof (h1 : ChowFormSection.Statement) (h2 : ChowFormCycleAdd.Statement)
    (h3 : ChowFormCycleSmul.Statement) : CycleSectionChow.Statement := by
  intro n e Z f u hprime hf hadm
  obtain ⟨c, hc, g, hg, rfl⟩ := hf
  have hW : ∀ W ∈ Z.support, IsChowFormCycle (divCycle W u) e (specFirst (g W) u) :=
    fun W hW' => h1 ℂ n e W (g W) u (hprime W hW') (hg W hW') (hadm W hW')
  have key : ∀ s ⊆ Z.support, IsChowFormCycle (∑ W ∈ s, Z W • divCycle W u) e
      (∏ W ∈ s, specFirst (g W) u ^ Z W) := by
    intro s
    induction s using Finset.induction_on with
    | empty => intro _; simpa using (isChowFormCycle_zero_one : IsChowFormCycle (0 : ProjCycle ℂ n) e 1)
    | insert a s ha ih =>
      intro hs
      rw [Finset.sum_insert ha, Finset.prod_insert ha]
      exact h2 ℂ n e _ _ _ _ (h3 ℂ n e (Z a) _ _ (hW a (hs (Finset.mem_insert_self a s))))
        (ih (fun x hx => hs (Finset.mem_insert_of_mem hx)))
  have hspec : specFirst (C c * ∏ W ∈ Z.support, g W ^ Z W) u =
      C c * ∏ W ∈ Z.support, specFirst (g W) u ^ Z W := by
    simp only [specFirst, map_mul, map_prod, map_pow, bind₁_C_right]
  rw [hspec]
  exact (key Z.support subset_rfl).C_mul hc

end

end GroundTheory.Heights₂.Heights
