import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
import Development.AbelianVarietyTheory.Definitions.Divisors.InfUniv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GroupObjectLiftDividedPowers
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorModOfTmul
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham
open scoped TensorProduct
open IsLocalRing
universe u

namespace GlobalTheory

theorem eqLift_tensorModOf : ∀ {C : Type} [CommRing C] (I : Ideal C) {A : Type} [CommRing A] {H : Type u} [AddCommGroup H] [Module C H]
  (σ : A →+* Module.End C H), (letI := GlobalTheory.HTSummand.tensorModOf σ; Module.Projective (C ⊗[ℤ] A) H) →
  ∀ (χ : A →+* C) (l₀ : H →ₗ[C] C ⧸ I), (∀ a x, l₀ (σ a x) = Ideal.Quotient.mk I (χ a) * l₀ x) →
  ∃ l : H →ₗ[C] C, (∀ a x, l (σ a x) = χ a * l x) ∧ ∀ x, Ideal.Quotient.mk I (l x) = l₀ x := by
  intro C _ I A _ H _ _ σ hproj χ l₀ hl₀
  letI mH : Module (C ⊗[ℤ] A) H := GlobalTheory.HTSummand.tensorModOf σ
  let χt : C ⊗[ℤ] A →ₐ[ℤ] C := Algebra.TensorProduct.productMap (AlgHom.id ℤ C) χ.toIntAlgHom
  have hχt : ∀ (r : C) (a : A), χt (r ⊗ₜ[ℤ] a) = r * χ a := fun r a => by
    simp [χt, Algebra.TensorProduct.productMap_apply_tmul]
  obtain ⟨s, hs⟩ := Module.projective_def'.mp hproj
  have hsx : ∀ x, (s x).sum (fun y c => c • y) = x := by
    intro x
    have := LinearMap.congr_fun hs x
    simpa [Finsupp.linearCombination_apply] using this
  let g : H → C := fun y => Function.surjInv Ideal.Quotient.mk_surjective (l₀ y)
  have hg : ∀ y, Ideal.Quotient.mk I (g y) = l₀ y := fun y =>
    Function.surjInv_eq Ideal.Quotient.mk_surjective (l₀ y)
  let F : H → C := fun x => (s x).sum (fun y c => χt c * g y)
  have hadd : ∀ x x', F (x + x') = F x + F x' := by
    intro x x'
    simp only [F, map_add]
    exact Finsupp.sum_add_index' (by simp) (by intros; simp [add_mul])
  have hS : ∀ (t : C ⊗[ℤ] A) x, F (t • x) = χt t * F x := by
    intro t x
    simp only [F, map_smul]
    rw [Finsupp.sum_smul_index (by simp), Finsupp.mul_sum]
    simp [_root_.mul_assoc]
  have hr : ∀ (r : C) (x : H), r • x = ((r ⊗ₜ[ℤ] (1 : A) : C ⊗[ℤ] A) • x) := by
    intro r x
    rw [GlobalTheory.HTSummand.tensorModOf_tmul, map_one]
    rfl
  have ha : ∀ (a : A) (x : H), σ a x = ((1 ⊗ₜ[ℤ] a : C ⊗[ℤ] A) • x) := by
    intro a x
    rw [GlobalTheory.HTSummand.tensorModOf_tmul, one_smul]
  let l : H →ₗ[C] C :=
    { toFun := F
      map_add' := hadd
      map_smul' := by
        intro r x
        show F (r • x) = r * F x
        rw [hr, hS, hχt, map_one, _root_.mul_one] }
  have hl₀t : ∀ (t : C ⊗[ℤ] A) y, l₀ (t • y) = Ideal.Quotient.mk I (χt t) * l₀ y := by
    intro t y
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul r a =>
      rw [GlobalTheory.HTSummand.tensorModOf_tmul, l₀.map_smul, hl₀, hχt, map_mul, Algebra.smul_def,
        Ideal.Quotient.algebraMap_eq, _root_.mul_assoc]
    | add t t' h h' => rw [add_smul, map_add, h, h', map_add, map_add, add_mul]
  refine ⟨l, ?_, ?_⟩
  · intro a x
    show F (σ a x) = χ a * F x
    rw [ha, hS, hχt, _root_.one_mul]
  · intro x
    show Ideal.Quotient.mk I (F x) = l₀ x
    conv_rhs => rw [← hsx x]
    simp only [F, map_finsuppSum, map_mul, hg, hl₀t]

end GlobalTheory
