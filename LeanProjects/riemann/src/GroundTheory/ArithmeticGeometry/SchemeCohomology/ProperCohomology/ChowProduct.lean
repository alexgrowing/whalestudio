import Mathlib
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProjectiveCohomology.TwistingSheaf
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProjectiveCohomology.TwistingSheafCore
set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.SchemeCoh

open AlgebraicGeometry CategoryTheory Limits MvPolynomial

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable section

namespace ProjSpace

variable (A : Type u) [CommRing A]

lemma bijective_algebraMap_gradeZero (n : ℕ) :
    Function.Bijective (algebraMap A (grading A n 0)) := by
  refine ⟨fun a b h => ?_, ?_⟩
  · have h' := congrArg Subtype.val h
    rw [SetLike.GradeZero.coe_algebraMap, SetLike.GradeZero.coe_algebraMap,
      MvPolynomial.algebraMap_eq] at h'
    exact MvPolynomial.C_injective _ _ h'
  · rintro ⟨p, hp⟩
    refine ⟨coeff 0 p, Subtype.ext ?_⟩
    rw [SetLike.GradeZero.coe_algebraMap, MvPolynomial.algebraMap_eq]
    by_cases h0 : p = 0
    · subst h0
      simp
    · exact (totalDegree_eq_zero_iff_eq_C.1
        (((mem_homogeneousSubmodule _ _).1 hp).totalDegree h0)).symm

instance isIso_SpecMap_gradeZero (n : ℕ) :
    IsIso (Spec.map (CommRingCat.ofHom (algebraMap A (grading A n 0)))) := by
  have : IsIso (CommRingCat.ofHom (algebraMap A (grading A n 0))) :=
    (ConcreteCategory.isIso_iff_bijective _).2 (bijective_algebraMap_gradeZero A n)
  infer_instance

instance isProper_toSpecBase (n : ℕ) : IsProper (toSpecBase A n) := by
  dsimp only [toSpecBase]
  infer_instance

def multiProj : (k : ℕ) → (Fin (k + 1) → ℕ) → Σ P : Scheme.{u}, P ⟶ Spec (.of A)
  | 0, n => ⟨projectiveSpace A (n 0), toSpecBase A (n 0)⟩
  | k + 1, n => ⟨pullback (toSpecBase A (n 0)) (multiProj k (Fin.tail n)).2,
      pullback.fst _ _ ≫ toSpecBase A (n 0)⟩

abbrev MP (k : ℕ) (n : Fin (k + 1) → ℕ) : Scheme.{u} := (multiProj A k n).1

abbrev mpStr (k : ℕ) (n : Fin (k + 1) → ℕ) : MP A k n ⟶ Spec (.of A) := (multiProj A k n).2

instance isProper_mpStr : (k : ℕ) → (n : Fin (k + 1) → ℕ) → IsProper (mpStr A k n)
  | 0, n => isProper_toSpecBase A (n 0)
  | k + 1, n => by
    have := isProper_mpStr k (Fin.tail n)
    change IsProper (pullback.fst (toSpecBase A (n 0)) (mpStr A k (Fin.tail n)) ≫ _)
    infer_instance

def pr : (k : ℕ) → (n : Fin (k + 1) → ℕ) → (i : Fin (k + 1)) →
    MP A k n ⟶ projectiveSpace A (n i)
  | 0, n, i => Fin.cases (motive := fun i => MP A 0 n ⟶ projectiveSpace A (n i)) (𝟙 _)
      (fun j => j.elim0) i
  | k + 1, n, i => Fin.cases (motive := fun i => MP A (k + 1) n ⟶ projectiveSpace A (n i))
      (pullback.fst (toSpecBase A (n 0)) (mpStr A k (Fin.tail n)))
      (fun j => pullback.snd (toSpecBase A (n 0)) (mpStr A k (Fin.tail n)) ≫ pr k (Fin.tail n) j) i

@[reassoc]
lemma pr_toSpecBase : (k : ℕ) → (n : Fin (k + 1) → ℕ) → (i : Fin (k + 1)) →
    pr A k n i ≫ toSpecBase A (n i) = mpStr A k n
  | 0, n, i => by
    induction i using Fin.cases with
    | zero => exact Category.id_comp _
    | succ j => exact j.elim0
  | k + 1, n, i => by
    induction i using Fin.cases with
    | zero => rfl
    | succ j =>
      change (pullback.snd _ _ ≫ pr A k (Fin.tail n) j) ≫ toSpecBase A (Fin.tail n j) = _
      rw [Category.assoc, pr_toSpecBase k (Fin.tail n) j, ← pullback.condition]
      rfl

variable {A}

@[simp] lemma pr_zero_zero (n : Fin 1 → ℕ) : pr A 0 n 0 = 𝟙 _ := rfl

@[simp] lemma pr_succ_zero (k : ℕ) (n : Fin (k + 2) → ℕ) :
    pr A (k + 1) n 0 = pullback.fst (toSpecBase A (n 0)) (mpStr A k (Fin.tail n)) := rfl

@[simp] lemma pr_succ_succ (k : ℕ) (n : Fin (k + 2) → ℕ) (j : Fin (k + 1)) :
    pr A (k + 1) n j.succ =
      pullback.snd (toSpecBase A (n 0)) (mpStr A k (Fin.tail n)) ≫ pr A k (Fin.tail n) j := rfl

def liftAux : (k : ℕ) → (n : Fin (k + 1) → ℕ) → {T : Scheme.{u}} → (t : T ⟶ Spec (.of A)) →
    (a : ∀ i, T ⟶ projectiveSpace A (n i)) → (∀ i, a i ≫ toSpecBase A (n i) = t) →
    {f : T ⟶ MP A k n // f ≫ mpStr A k n = t}
  | 0, _, _, _, a, ha => ⟨a 0, ha 0⟩
  | k + 1, n, _, t, a, ha =>
    ⟨pullback.lift (a 0) (liftAux k (Fin.tail n) t (fun j => a j.succ) (fun j => ha j.succ)).1
      (by rw [ha 0]; exact (liftAux k (Fin.tail n) t _ _).2.symm), by
      change pullback.lift _ _ _ ≫ pullback.fst _ _ ≫ _ = _
      rw [pullback.lift_fst_assoc, ha 0]⟩

def lift (k : ℕ) (n : Fin (k + 1) → ℕ) {T : Scheme.{u}} (t : T ⟶ Spec (.of A))
    (a : ∀ i, T ⟶ projectiveSpace A (n i)) (ha : ∀ i, a i ≫ toSpecBase A (n i) = t) :
    T ⟶ MP A k n :=
  (liftAux k n t a ha).1

@[reassoc (attr := simp)]
lemma lift_mpStr (k : ℕ) (n : Fin (k + 1) → ℕ) {T : Scheme.{u}} (t : T ⟶ Spec (.of A))
    (a : ∀ i, T ⟶ projectiveSpace A (n i)) (ha : ∀ i, a i ≫ toSpecBase A (n i) = t) :
    lift k n t a ha ≫ mpStr A k n = t :=
  (liftAux k n t a ha).2

@[reassoc (attr := simp)]
lemma lift_pr : (k : ℕ) → (n : Fin (k + 1) → ℕ) → {T : Scheme.{u}} → (t : T ⟶ Spec (.of A)) →
    (a : ∀ i, T ⟶ projectiveSpace A (n i)) → (ha : ∀ i, a i ≫ toSpecBase A (n i) = t) →
    (i : Fin (k + 1)) → lift k n t a ha ≫ pr A k n i = a i
  | 0, n, _, t, a, ha, i => by
    induction i using Fin.cases with
    | zero => exact Category.comp_id _
    | succ j => exact j.elim0
  | k + 1, n, _, t, a, ha, i => by
    induction i using Fin.cases with
    | zero => exact pullback.lift_fst _ _ _
    | succ j =>
      rw [pr_succ_succ]
      change pullback.lift _ _ _ ≫ pullback.snd _ _ ≫ pr A k (Fin.tail n) j = _
      rw [pullback.lift_snd_assoc]
      exact lift_pr k (Fin.tail n) t _ _ j

lemma hom_ext : (k : ℕ) → (n : Fin (k + 1) → ℕ) → {T : Scheme.{u}} → (f g : T ⟶ MP A k n) →
    (∀ i, f ≫ pr A k n i = g ≫ pr A k n i) → f = g
  | 0, n, _, f, g, h => by
    have := h 0
    rw [pr_zero_zero] at this
    exact (Category.comp_id f).symm.trans (this.trans (Category.comp_id g))
  | k + 1, n, _, f, g, h => by
    apply pullback.hom_ext
    · exact h 0
    · refine hom_ext k (Fin.tail n) _ _ fun j => ?_
      have := h j.succ
      rw [pr_succ_succ] at this
      exact (Category.assoc _ _ _).trans (this.trans (Category.assoc _ _ _).symm)

end ProjSpace

end

end GroundTheory.Arith.SchemeCoh
