import Development.AutomorphicArithmetic.DivisorFrames.MemAdjoinGelfandSupOfCommuteGlGenerators
import Development.AutomorphicArithmetic.DivisorFrames.GelfandElementMemAdjoinCapelliCoeffs
import Formalism.RealPlaceAnalysis.ThirdArithmeticHolds

open Formalism.REAL
open scoped TensorProduct

namespace UpperTheory.V.Fb

variable {A ι : Type} [Ring A] [Algebra ℂ A] {n : ℕ}

private theorem qdet_mem (S : Subalgebra ℂ A) (X : Fin n → Fin n → A) (h : ∀ a b, X a b ∈ S) (u : ℂ) :
    qdet X u ∈ S := by
  refine S.sum_mem fun σ _ => S.mul_mem (intCast_mem S _) (S.list_prod_mem fun x hx => ?_)
  obtain ⟨k, rfl⟩ := List.mem_ofFn.1 hx
  refine S.add_mem ?_ (h _ _)
  split_ifs
  · exact S.algebraMap_mem _
  · exact S.zero_mem

theorem multiCentre [Fintype ι] (X : ι → Fin n → Fin n → A) (hX : ∀ i, GlRel (X i))
    (hc : ∀ i j, i ≠ j → ∀ a b c d, Commute (X i a b) (X j c d)) {z : A}
    (hz : z ∈ Algebra.adjoin ℂ {x | ∃ i a b, x = X i a b}) (hzc : ∀ i a b, X i a b * z = z * X i a b) :
    z ∈ Algebra.adjoin ℂ {x | ∃ i u, x = qdet (X i) u} := by
  classical
  have key : ∀ s : Finset ι,
      z ∈ Algebra.adjoin ℂ ({x | ∃ i ∈ s, ∃ u, x = qdet (X i) u} ∪ {x | ∃ i ∉ s, ∃ a b, x = X i a b}) := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact Algebra.adjoin_mono (by rintro _ ⟨i, a, b, rfl⟩; exact Or.inr ⟨i, by simp, a, b, rfl⟩) hz
    | insert i s hi ih =>
      set B := Algebra.adjoin ℂ
        ({x | ∃ j ∈ s, ∃ u, x = qdet (X j) u} ∪ {x | ∃ j ∉ insert i s, ∃ a b, x = X j a b}) with hB
      have h1 : ∀ b ∈ B, ∀ c d, X i c d * b = b * X i c d := fun b hb c d => by
        have : B ≤ Subalgebra.centralizer ℂ {X i c d} := by
          refine Algebra.adjoin_le ?_
          rintro _ (⟨j, hj, u, rfl⟩ | ⟨j, hj, a, b, rfl⟩)
          · refine qdet_mem _ _ (fun a b => ?_) u
            rintro _ rfl
            exact hc i j (fun e => hi (e ▸ hj)) c d a b
          · rintro _ rfl
            exact hc i j (fun e => hj (e ▸ Finset.mem_insert_self i s)) c d a b
        exact this hb _ rfl
      have h2 := UpperTheory.mem_adjoin_gelfand_sup_of_commute_glGenerators A n (X i) (hX i) B h1 z (Algebra.adjoin_le (by
        rintro _ (⟨j, hj, u, rfl⟩ | ⟨j, hj, a, b, rfl⟩)
        · exact Algebra.mem_sup_right (Algebra.subset_adjoin (Or.inl ⟨j, hj, u, rfl⟩))
        · by_cases e : j = i
          · subst e
            exact Algebra.mem_sup_left (Algebra.subset_adjoin ⟨(a, b), rfl⟩)
          · exact Algebra.mem_sup_right (Algebra.subset_adjoin (Or.inr ⟨j, by simp [e, hj], a, b, rfl⟩))) ih) (hzc i)
      refine (sup_le (Algebra.adjoin_le ?_) (Algebra.adjoin_mono ?_) : _ ≤ _) h2
      · rintro _ ⟨k, rfl⟩
        refine Algebra.adjoin_mono ?_ (UpperTheory.gelfandElement_mem_adjoin_capelliCoeffs A n (X i) (hX i) k)
        rintro _ ⟨u, rfl⟩
        exact Or.inl ⟨i, Finset.mem_insert_self i s, u, rfl⟩
      · rintro _ (⟨j, hj, u, rfl⟩ | h)
        · exact Or.inl ⟨j, Finset.mem_insert_of_mem hj, u, rfl⟩
        · exact Or.inr h
  refine Algebra.adjoin_mono ?_ (key Finset.univ)
  rintro _ (⟨j, -, u, rfl⟩ | ⟨j, hj, -⟩)
  · exact ⟨j, u, rfl⟩
  · exact absurd (Finset.mem_univ j) hj

theorem map_qdet {B : Type} [Ring B] [Algebra ℂ B] (f : A →ₐ[ℂ] B) (X : Fin n → Fin n → A) (u : ℂ) :
    f (qdet X u) = qdet (fun a b => f (X a b)) u := by
  have hT : ∀ v a b, f (Tm X v a b) = Tm (fun a b => f (X a b)) v a b := fun v a b => by
    unfold Tm
    split_ifs <;> simp
  simp only [qdet, qminor, map_sum, map_mul, map_intCast, map_list_prod, List.map_ofFn, Function.comp_def, hT]

theorem glRel_map {R S F : Type} [Ring R] [Ring S] [FunLike F R S] [RingHomClass F R S] (f : F) {X : Fin n → Fin n → R}
    (h : GlRel X) : GlRel fun a b => f (X a b) := fun a b c d => by
  have := congrArg f (h a b c d)
  simpa only [map_sub, map_mul, apply_ite f, map_zero] using this

theorem exists_re_im {B : Type} [Ring B] [Algebra ℝ B] (w : ℂ ⊗[ℝ] B) (hw : ∀ x : B, (1 ⊗ₜ x) * w = w * (1 ⊗ₜ x)) :
    ∃ p ∈ Subalgebra.center ℝ B, ∃ q ∈ Subalgebra.center ℝ B, w = (1 : ℂ) ⊗ₜ p + Complex.I ⊗ₜ q := by
  let P : (ℂ →ₗ[ℝ] ℝ) → ℂ ⊗[ℝ] B →ₗ[ℝ] B := fun f => (TensorProduct.lid ℝ B).toLinearMap ∘ₗ f.rTensor B
  have hP : ∀ f c x, P f (c ⊗ₜ x) = f c • x := fun f c x => by simp [P]
  have hl : ∀ f (x : B) (w : ℂ ⊗[ℝ] B), P f ((1 ⊗ₜ x) * w) = x * P f w := fun f x w => by
    induction w with
    | zero => simp
    | tmul c y => rw [Algebra.TensorProduct.tmul_mul_tmul, hP, hP, one_mul, mul_smul_comm]
    | add a b ha hb => rw [mul_add, map_add, map_add, ha, hb, mul_add]
  have hr : ∀ f (x : B) (w : ℂ ⊗[ℝ] B), P f (w * (1 ⊗ₜ x)) = P f w * x := fun f x w => by
    induction w with
    | zero => simp
    | tmul c y => rw [Algebra.TensorProduct.tmul_mul_tmul, hP, hP, mul_one, smul_mul_assoc]
    | add a b ha hb => rw [add_mul, map_add, map_add, ha, hb, add_mul]
  have hc : ∀ f, P f w ∈ Subalgebra.center ℝ B := fun f =>
    Subalgebra.mem_center_iff.2 fun x => by rw [← hl, hw, hr]
  refine ⟨_, hc Complex.reLm, _, hc Complex.imLm, ?_⟩
  clear hc hw
  induction w with
  | zero => simp
  | tmul c y =>
    rw [hP, hP, ← TensorProduct.smul_tmul, ← TensorProduct.smul_tmul, ← TensorProduct.add_tmul]
    congr 1
    simp
  | add a b ha hb =>
    rw [map_add, map_add, TensorProduct.tmul_add, TensorProduct.tmul_add, add_add_add_comm, ← ha, ← hb]

theorem qdet_mem_span_center [Algebra ℝ A] [IsScalarTower ℝ ℂ A] {B : Type} [Ring B] [Algebra ℝ B]
    (X : ι → Fin n → Fin n → B) (hX : ∀ i, GlRel (X i))
    (hc : ∀ i j, i ≠ j → ∀ a b c d, Commute (X i a b) (X j c d))
    (htop : Algebra.adjoin ℝ {x | ∃ i a b, x = X i a b} = ⊤) (ρ : B →ₐ[ℝ] A) (i : ι) (u : ℂ) :
    qdet (fun a b => ρ (X i a b)) u ∈ Submodule.span ℂ (ρ '' (Subalgebra.center ℝ B : Set B)) := by
  let j : B →ₐ[ℝ] ℂ ⊗[ℝ] B := Algebra.TensorProduct.includeRight
  let ψ : ℂ ⊗[ℝ] B →ₐ[ℂ] A := Algebra.TensorProduct.lift (Algebra.ofId ℂ A) ρ fun c x => Algebra.commutes c (ρ x)
  have hψ : ∀ c x, ψ (c ⊗ₜ x) = c • ρ x := fun c x =>
    (Algebra.TensorProduct.lift_tmul _ _ _ c x).trans (Algebra.smul_def c (ρ x)).symm
  set w := qdet (fun a b => j (X i a b)) u with hw
  have h1 : ∀ x : B, j x * w = w * j x := fun x => by
    have : Algebra.adjoin ℝ {x | ∃ i a b, x = X i a b} ≤ (Subalgebra.centralizer ℝ {w}).comap j := by
      refine Algebra.adjoin_le ?_
      rintro _ ⟨k, a, b, rfl⟩ _ rfl
      by_cases e : k = i
      · subst e
        exact qDetCentral _ n _ (glRel_map j (hX k)) u a b
      · refine (qdet_mem (Subalgebra.centralizer ℂ {j (X k a b)}) _ (fun c d => ?_) u _ rfl).symm
        rintro _ rfl
        exact (hc k i e a b c d).map j
    exact (this (htop ▸ Algebra.mem_top) w rfl).symm
  obtain ⟨p, hp, q, hq, e⟩ := exists_re_im w h1
  have h2 : ψ w = qdet (fun a b => ρ (X i a b)) u := by
    rw [hw, map_qdet]
    congr 1
    funext a b
    exact (hψ 1 _).trans (one_smul _ _)
  rw [← h2, e, map_add, hψ, hψ]
  exact add_mem (Submodule.smul_mem _ _ (Submodule.subset_span ⟨p, hp, rfl⟩))
    (Submodule.smul_mem _ _ (Submodule.subset_span ⟨q, hq, rfl⟩))

end UpperTheory.V.Fb
