import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TprodMemDegLE
open scoped TensorProduct

noncomputable section

open Formalism.BasicNotions.TH GlobalTheory.RealLift MvPolynomial

namespace GlobalTheory.KFixIrr.DegSucc

variable {ι : Type} [Fintype ι] [DecidableEq ι] {P Q R S : ℕ}

theorem atPlace_tprod_update {V : Type} [AddCommGroup V] [Module ℂ V] (w : ι) (L : Module.End ℂ V) (f : ι → V) :
    atPl (V := fun _ : ι => V) w L (PiTensorProduct.tprod ℂ f) = PiTensorProduct.tprod ℂ (Function.update f w (L (f w))) := by
  rw [atPl, PiTensorProduct.map_tprod]
  congr 1
  funext i
  by_cases h : i = w
  · subst h; simp
  · simp [Function.update_of_ne h]

theorem dg_add {σ : Type} (s t : σ →₀ ℕ) :
    ((s + t).sum fun _ e => e) = (s.sum fun _ e => e) + (t.sum fun _ e => e) :=
  Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl)

theorem monomial_mem (k : ℕ) (g : ι → (Ln P Q R S →₀ ℕ)) (a : ι → ℂ)
    (h : ∑ w, ((g w).sum fun _ e => e) ≤ k + 1) :
    PiTensorProduct.tprod ℂ (fun w => (monomial (g w) (a w) : Formalism.BasicNotions.TH.Pol P Q R S)) ∈
      GlobalTheory.KFixIrr.degLE ι P Q R S k ⊔ Submodule.span ℂ
      {T' | ∃ (w : ι) (l : Formalism.BasicNotions.TH.Ln P Q R S), ∃ T ∈ GlobalTheory.KFixIrr.degLE ι P Q R S k,
        T' = GlobalTheory.RealLift.atPl (V := fun _ : ι => Formalism.BasicNotions.TH.Pol P Q R S) w
          (LinearMap.mulLeft ℂ (MvPolynomial.X l : Formalism.BasicNotions.TH.Pol P Q R S)) T} := by
  have hdeg : ∀ (G : ι → (Ln P Q R S →₀ ℕ)) (b : ι → ℂ), ∑ w, ((G w).sum fun _ e => e) ≤ k →
      PiTensorProduct.tprod ℂ (fun w => (monomial (G w) (b w) : Formalism.BasicNotions.TH.Pol P Q R S)) ∈
        GlobalTheory.KFixIrr.degLE ι P Q R S k := by
    intro G b hG
    apply GlobalTheory.KFixIrr.tprod_mem_degLE
    refine le_trans (Finset.sum_le_sum fun w _ => ?_) hG
    exact totalDegree_monomial_le _ _
  by_cases hk : ∑ w, ((g w).sum fun _ e => e) ≤ k
  · exact Submodule.mem_sup_left (hdeg g a hk)
  obtain ⟨w, hw⟩ : ∃ w, g w ≠ 0 := by
    by_contra hc
    push_neg at hc
    apply hk
    simp [hc]
  obtain ⟨l, hl⟩ : ∃ l, g w l ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hw (Finsupp.ext hc)
  set s' := g w - Finsupp.single l 1 with hs'
  have hle : Finsupp.single l 1 ≤ g w := by
    rw [Finsupp.single_le_iff]; omega
  have hs : g w = s' + Finsupp.single l 1 := (tsub_add_cancel_of_le hle).symm
  set G := Function.update g w s' with hG
  have hsum : ∑ w', ((G w').sum fun _ e => e) + 1 = ∑ w', ((g w').sum fun _ e => e) := by
    rw [← Finset.add_sum_erase Finset.univ (fun w' => ((G w').sum fun _ e => e)) (Finset.mem_univ w),
      ← Finset.add_sum_erase Finset.univ (fun w' => ((g w').sum fun _ e => e)) (Finset.mem_univ w)]
    have hrest : ∑ x ∈ Finset.univ.erase w, ((G x).sum fun _ e => e) = ∑ x ∈ Finset.univ.erase w, ((g x).sum fun _ e => e) := by
      apply Finset.sum_congr rfl
      intro x hx
      have : x ≠ w := Finset.ne_of_mem_erase hx
      rw [hG, Function.update_of_ne this]
    rw [hrest, hG, Function.update_self, hs, dg_add]
    simp [Finsupp.sum_single_index]
    ring
  have hGk : ∑ w', ((G w').sum fun _ e => e) ≤ k := by omega
  refine Submodule.mem_sup_right (Submodule.subset_span ⟨w, l, _, hdeg G a hGk, ?_⟩)
  rw [atPlace_tprod_update]
  congr 1
  funext i
  by_cases hi : i = w
  · subst hi
    rw [Function.update_self, LinearMap.mulLeft_apply, hG, Function.update_self, hs, monomial_add_single, pow_one,
      mul_comm]
  · rw [Function.update_of_ne hi, hG, Function.update_of_ne hi]

theorem degLE_succ_le : ∀ {ι : Type} [Fintype ι] [DecidableEq ι] {P Q R S : ℕ} (k : ℕ),
    GlobalTheory.KFixIrr.degLE ι P Q R S (k + 1) ≤ GlobalTheory.KFixIrr.degLE ι P Q R S k ⊔ Submodule.span ℂ
      {T' | ∃ (w : ι) (l : Formalism.BasicNotions.TH.Ln P Q R S), ∃ T ∈ GlobalTheory.KFixIrr.degLE ι P Q R S k,
        T' = GlobalTheory.RealLift.atPl (V := fun _ : ι => Formalism.BasicNotions.TH.Pol P Q R S) w
          (LinearMap.mulLeft ℂ (MvPolynomial.X l : Formalism.BasicNotions.TH.Pol P Q R S)) T} := by
  intro ι _ _ P Q R S k
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨f, hf, rfl⟩
  have hf' : PiTensorProduct.tprod ℂ f = PiTensorProduct.tprod ℂ
      (fun w => ∑ s ∈ (f w).support, (monomial s (coeff s (f w)) : Formalism.BasicNotions.TH.Pol P Q R S)) := by
    congr 1; funext w; exact (f w).as_sum
  rw [SetLike.mem_coe, hf', MultilinearMap.map_sum_finset]
  refine Submodule.sum_mem _ fun r hr => ?_
  rw [Fintype.mem_piFinset] at hr
  apply monomial_mem k r (fun w => coeff (r w) (f w))
  exact le_trans (Finset.sum_le_sum fun w _ => le_totalDegree (hr w)) hf

end GlobalTheory.KFixIrr.DegSucc

end
