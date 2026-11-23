import Mathlib
import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.SlopeTestRemainingChoices
import Development.EtaleCohomology.KummerTheory.InjSlice
import Development.AbelianVarietyTheory.Definitions.Divisors.E5
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Et

theorem UpperTheory.cohomology_representatives :
    SlopeTestRemainingChoices → ∀ (R : Type) [CommRing R] (I : Cx R) (U : Scheme.{0}) (m n k : ℤ), m + 1 = n → n + 1 = k →
      (∀ z : Sec (I.X n) U, Sec.map (I.d n k) z = 0 → ∃ c, Rep z c) ∧ (∀ c, ∃ z : Sec (I.X n) U, Rep z c) ∧
      (∀ (z : Sec (I.X n) U) c, Rep z c → Sec.map (I.d n k) z = 0 ∧ (c = 0 ↔ ∃ y : Sec (I.X m) U, Sec.map (I.d m n) y = z)) ∧
      (∀ (z z' : Sec (I.X n) U) c c', Rep z c → Rep z' c' → Rep (z + z') (c + c') ∧ Rep (z - z') (c - c') ∧ (c = c' ↔ ∃ y : Sec (I.X m) U, z = z' + Sec.map (I.d m n) y)) ∧
      Rep (0 : Sec (I.X n) U) 0 ∧ ∀ (a : ℕ) (z : Sec (I.X n) U) c, Rep z c → Rep (a • z) (a • c) := by
  intro A R _ I U m n k hmn hnk
  have hrep := A.rep R U I m n k hmn hnk
  have hev := (A.evs R (E := sch.obj U) (I := I) (n := n)).1
  have hvan : ∀ (z : Sec (I.X n) U) c, Rep z c →
      Sec.map (I.d n k) z = 0 ∧ (c = 0 ↔ ∃ y : Sec (I.X m) U, Sec.map (I.d m n) y = z) := by
    rintro z c ⟨α, rfl, rfl⟩
    exact hrep.2 α
  have hadd : ∀ (z z' : Sec (I.X n) U) c c', Rep z c → Rep z' c' → Rep (z + z') (c + c') := by
    rintro z z' c c' ⟨α, rfl, rfl⟩ ⟨β, rfl, rfl⟩
    exact ⟨α + β, CohomologyClass.mk_add α β, (hev α.1 β.1 0 n (by simp) U (𝟙 U)).1⟩
  have hsub : ∀ (z z' : Sec (I.X n) U) c c', Rep z c → Rep z' c' → Rep (z - z') (c - c') := by
    rintro z z' c c' ⟨α, rfl, rfl⟩ ⟨β, rfl, rfl⟩
    exact ⟨α - β, CohomologyClass.mk_sub α β, (hev α.1 β.1 0 n (by simp) U (𝟙 U)).2.1⟩
  have hzero : Rep (0 : Sec (I.X n) U) 0 :=
    ⟨0, CohomologyClass.mk_zero _ _ _, (hev 0 0 0 n (by simp) U (𝟙 U)).2.2.1⟩
  refine ⟨?_, ?_, hvan, ?_, hzero, ?_⟩
  · intro z hz
    obtain ⟨α, h0, -⟩ := hrep.1 z hz
    refine ⟨CohomologyClass.mk α, α, rfl, ?_⟩
    rw [h0]
    change ((I.X n).obj.map (𝟙 (op U))).hom z = z
    rw [CategoryTheory.Functor.map_id]
    rfl
  · intro c
    obtain ⟨α, rfl⟩ := c.mk_surjective
    exact ⟨_, α, rfl, rfl⟩
  · intro z z' c c' h h'
    refine ⟨hadd _ _ _ _ h h', hsub _ _ _ _ h h', ?_⟩
    rw [← sub_eq_zero, (hvan _ _ (hsub _ _ _ _ h h')).2]
    constructor
    · rintro ⟨y, hy⟩
      exact ⟨y, by rw [hy]; abel⟩
    · rintro ⟨y, hy⟩
      exact ⟨y, by rw [hy]; abel⟩
  · intro a z c h
    induction a with
    | zero => simpa using hzero
    | succ a ih => simpa [succ_nsmul] using hadd _ _ _ _ ih h

end
