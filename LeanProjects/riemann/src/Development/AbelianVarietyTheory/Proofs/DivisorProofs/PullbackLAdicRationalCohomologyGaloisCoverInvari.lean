import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.E5
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTraceFiniteEtaleGaloisCoverLadicStatement
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace GlobalTheory

theorem pullHQ_galoisCover_inv : ∀ (l : ℕ) [Fact l.Prime] {Y X : Scheme.{0}} (f : Y ⟶ X) [IsFinite f] [Etale f] [Surjective f] (G : Type) [Fintype G]
  (a : G → (Y ⟶ Y)) (ha : ∀ g, a g ≫ f = f),
  IsIso (Sigma.desc (fun g => pullback.lift (a g) (𝟙 Y) (by rw [ha g, Category.id_comp])) : ∐ (fun _ : G => Y) ⟶ pullback f f) → ∀ n i : ℤ, Function.Injective (pullHQ l (sch.map f) n i) ∧
  LinearMap.range (pullHQ l (sch.map f) n i) = ⨅ g, LinearMap.ker (pullHQ l (sch.map (a g)) n i - LinearMap.id) := by
  intro l _ Y X f _ _ _ G _ a ha hiso n i
  obtain ⟨tr, h1, h2⟩ := GlobalTheory.T.exists_trace_finiteEtaleGaloisCover_ladic l f G a ha hiso n i
  set F := pullHQ l (sch.map f) n i with hF
  set T := tr.baseChange ℚ_[l] with hT
  have pqc : ∀ {A B C : Scheme.{0}} (u : A ⟶ B) (v : B ⟶ C),
      pullHQ l (sch.map (u ≫ v)) n i = (pullHQ l (sch.map u) n i).comp (pullHQ l (sch.map v) n i) := by
    intro A B C u v
    rw [pullHQ, pullHQ, pullHQ, ← LinearMap.baseChange_comp, ← pullHl_comp, ← Functor.map_comp]
  have pqi : ∀ A : Scheme.{0}, pullHQ l (sch.map (𝟙 A)) n i = LinearMap.id := by
    intro A
    rw [pullHQ, CategoryTheory.Functor.map_id, pullHl_id, LinearMap.baseChange_id]
  have key1 : ∀ x, T (F x) = (Fintype.card G : ℚ_[l]) • x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul r m =>
      rw [hF, pullHQ, hT, LinearMap.baseChange_tmul, LinearMap.baseChange_tmul, h1, Nat.cast_smul_eq_nsmul]
      exact TensorProduct.tmul_smul _ _ _
    | add x y hx hy => rw [map_add, map_add, hx, hy, smul_add]
  have key2 : ∀ y, F (T y) = ∑ g, pullHQ l (sch.map (a g)) n i y := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul r m =>
      rw [hF, pullHQ, hT, LinearMap.baseChange_tmul, LinearMap.baseChange_tmul, h2, TensorProduct.tmul_sum]
      simp only [pullHQ, LinearMap.baseChange_tmul]
    | add x y hx hy => rw [map_add, map_add, hx, hy, ← Finset.sum_add_distrib]; simp only [map_add]
  have comp : ∀ g, (pullHQ l (sch.map (a g)) n i).comp F = F := by
    intro g
    rw [hF, ← pqc, ha g]
  by_cases hG : Fintype.card G = 0
  ·
    haveI : IsEmpty G := Fintype.card_eq_zero_iff.mp hG
    have hS : IsEmpty ↥(∐ (fun _ : G => Y)) := by
      constructor
      intro p
      obtain ⟨j, _⟩ := (sigmaOpenCover (fun _ : G => Y)).exists_eq p
      exact isEmptyElim (show G from j)
    haveI hYe : IsEmpty Y :=
      ⟨fun y => hS.false ((pullback.lift (𝟙 Y) (𝟙 Y) rfl ≫ inv (Sigma.desc (fun g =>
        pullback.lift (a g) (𝟙 Y) (by rw [ha g, Category.id_comp])) : ∐ (fun _ : G => Y) ⟶ pullback f f)).base y)⟩
    haveI : IsEmpty X := ⟨fun x => by
      obtain ⟨y, _⟩ := (inferInstance : Surjective f).surj x
      exact hYe.false y⟩
    haveI : IsIso f := isIso_of_isEmpty f
    have e1 : (pullHQ l (sch.map (inv f)) n i).comp F = LinearMap.id := by
      rw [hF, ← pqc, IsIso.inv_hom_id, pqi]
    have e2 : F.comp (pullHQ l (sch.map (inv f)) n i) = LinearMap.id := by
      rw [hF, ← pqc, IsIso.hom_inv_id, pqi]
    refine ⟨fun x y hxy => ?_, ?_⟩
    · have := congrArg (pullHQ l (sch.map (inv f)) n i) hxy
      rwa [← LinearMap.comp_apply, e1, ← LinearMap.comp_apply, e1] at this
    · rw [iInf_of_empty, LinearMap.range_eq_top]
      intro y
      exact ⟨pullHQ l (sch.map (inv f)) n i y, by rw [← LinearMap.comp_apply, e2, LinearMap.id_apply]⟩
  have hc : (Fintype.card G : ℚ_[l]) ≠ 0 := Nat.cast_ne_zero.mpr hG
  refine ⟨fun x y hxy => ?_, ?_⟩
  · have := congrArg T hxy
    rw [key1, key1] at this
    exact smul_right_injective _ hc this
  · apply le_antisymm
    · rintro _ ⟨x, rfl⟩
      simp only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply]
      intro g
      rw [← LinearMap.comp_apply, comp g, sub_self]
    · intro y hy
      simp only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero] at hy
      refine ⟨(Fintype.card G : ℚ_[l])⁻¹ • T y, ?_⟩
      rw [map_smul, key2]
      simp only [hy, Finset.sum_const, Finset.card_univ]
      rw [← Nat.cast_smul_eq_nsmul ℚ_[l], smul_smul, inv_mul_cancel₀ hc, one_smul]

end GlobalTheory
