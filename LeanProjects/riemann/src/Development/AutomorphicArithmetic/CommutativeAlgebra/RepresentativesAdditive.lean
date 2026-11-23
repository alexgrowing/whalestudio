import Mathlib
import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.SlopeTestRemainingChoices
import Development.EtaleCohomology.KummerTheory.InjSlice
import Development.AbelianVarietyTheory.Definitions.Divisors.E5
import Development.AutomorphicArithmetic.CommutativeAlgebra.CohomologyRepresentatives
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Et

theorem UpperTheory.representatives_additive :
    SlopeTestRemainingChoices → (∀ (R : Type) [CommRing R] (F : Shv R) {V U : Scheme.{0}} (g : V ⟶ U) (n : ℤ) (z : Sec ((res R F).X n) U) (c : H R (sch.obj U) F n), Rep z c → Rep (Sec.res g z) (pull R (sch.map g) F n c)) ∧
      (∀ (R : Type) [CommRing R] (I : Cx R) (U : Scheme.{0}) (n : ℤ) {ι : Type} (t : Finset ι) (z : ι → Sec (I.X n) U) (c : ι → _), (∀ b, Rep (z b) (c b)) → Rep (∑ b ∈ t, z b) (∑ b ∈ t, c b)) ∧
      ∀ (q : ℕ) [NeZero q] (U : Scheme.{0}) (i : ℤ) (ζ : Prim q Γ(U, ⊤)), Rep (resGen i ζ) (rootClass i ζ) := by
  intro A
  refine ⟨?_, ?_, ?_⟩
  · rintro R _ F V U g n z c ⟨α, rfl, rfl⟩
    refine ⟨zcomp (Cocycle.ofHom ((chains R).map (sch.map g))) α (zero_add n), rfl, ?_⟩
    have h4 := (A.evs R).2.2.2.1 (sch.map g) α.1 0 n (by simp) V (𝟙 V : V ⟶ V)
    have h2 := (A.evs R).2.1 α.1 0 n (by simp) V U g (𝟙 U : U ⟶ U)
    have e1 : Sx.map (sch.map g) (p := 0) (𝟙 V : V ⟶ V) = g := Category.id_comp g
    have e2 : Sx.res g (E := sch.obj U) (p := 0) (𝟙 U : U ⟶ U) = Sx.map (sch.map g) (p := 0) (𝟙 V : V ⟶ V) := e1.symm ▸ Category.comp_id g
    exact (h4.trans (congrArg (ev α.1 0 n (by simp) V) e2.symm)).trans h2.symm
  · intro R _ I U n ι t z c h
    classical
    have hr := UpperTheory.cohomology_representatives A R I U (n - 1) n (n + 1) (by omega) rfl
    induction t using Finset.induction_on with
    | empty => simpa using hr.2.2.2.2.1
    | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      exact (hr.2.2.2.1 _ _ _ _ (h a) ih).1
  · intro q _ U i ζ
    obtain ⟨α, hα⟩ := (rootClass i ζ).mk_surjective
    refine ⟨α, hα, ?_⟩
    rw [(A.unit q).2.2.2 i U ζ] at hα
    exact ((A.sec _ (tw q i) U).1 (twGen i ζ) α).2 hα

end
