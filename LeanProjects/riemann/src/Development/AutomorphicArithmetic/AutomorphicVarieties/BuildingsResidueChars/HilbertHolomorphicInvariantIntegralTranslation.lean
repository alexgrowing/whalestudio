import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.WeightChange
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.GlobFixed
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.Sd
open scoped Matrix

private theorem map_aff' {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (x : R) :
    Matrix.GeneralLinearGroup.map f (aff 1 x) = aff 1 (f x) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [aff]

private theorem aff_add' {R : Type} [CommRing R] (x y : R) : aff 1 x * aff 1 y = aff 1 (x + y) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [aff, Matrix.mul_apply, Fin.sum_univ_succ, add_comm]

private theorem aff_zero' {R : Type} [CommRing R] : aff (1 : Rˣ) (0 : R) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [aff]

private theorem aff_mirab' {R : Type} [CommRing R] (x : R) : aff (1 : Rˣ) x ∈ mirab R := by
  change _ = _
  simp [funext_iff, Fin.forall_fin_two, Matrix.vecMul, dotProduct, aff]

open UpperTheory.V.Af.GlobalFixedVectors in
theorem UpperTheory.hilbertHolomorphic_invariant_integralTranslation :
    ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (k : ℕ) (c : Pl F → ℕ) (ω : HChar F) (φ : TR.Sm F 2), IsHol k c ω φ → ∀ o : Af F, (∀ v : Pl F, Valued.v (pLoc F v o) ≤ 1) → TR.finRep F 2 (aff 1 o) φ = φ := by
  classical
  intro F _ _ _ k c ω φ hφ o ho
  have key : ∀ S : Finset (Pl F),
      (∀ x ∈ Ohat F, (∀ w ∈ S, pLoc F w x = 0) → TR.finRep F 2 (aff 1 x) φ = φ) →
      ∀ x ∈ Ohat F, TR.finRep F 2 (aff 1 x) φ = φ := by
    intro S
    induction S using Finset.induction_on with
    | empty => exact fun h x hx => h x hx (by simp)
    | insert w S hw ih =>
      intro h
      refine ih fun x hx hS => ?_
      have e : aff 1 x = aff 1 (x - sLoc F w (pLoc F w x)) * locGL F 2 w (aff 1 (pLoc F w x)) := gl_ext fun u => by
        rw [map_mul, map_aff', map_aff', map_sub]
        by_cases hu : u = w
        · subst hu
          rw [pLoc_locGL, pLoc_sLoc, sub_self, aff_zero', one_mul]
        · rw [pLoc_locGL_of_ne hu, pLoc_sLoc_of_ne hu, sub_zero, mul_one]
      have hK : aff 1 (pLoc F w x) ∈ K1 w (c w) := by
        refine ⟨aff 1 ⟨pLoc F w x, mem_Ohat.1 hx w⟩, ?_, map_aff' _ _⟩
        change Matrix.GeneralLinearGroup.map _ _ ∈ mirab _
        rw [map_aff']
        exact aff_mirab' _
      have h1 : TR.finRep F 2 (locGL F 2 w (aff 1 (pLoc F w x))) φ = φ := hφ.level w _ hK
      rw [e, map_mul, Module.End.mul_apply, h1]
      refine h _ (sub_mem hx (sLoc_mem w hx)) fun u hu => ?_
      rw [map_sub]
      by_cases huw : u = w
      · subst huw
        rw [pLoc_sLoc, sub_self]
      · rw [pLoc_sLoc_of_ne huw, sub_zero]
        exact hS u ((Finset.mem_insert.1 hu).resolve_left huw)
  obtain ⟨S, hS⟩ := exists_KAway_subset (M := 1) (hφ.aut.level.mem_nhds (show (1 : GL (Fin 2) (Af F)) ∈ _ by simp))
  refine key S (fun x hx h0 => hS (mem_KAway.2 ⟨⟨aff 1 ⟨x, hx⟩, ?_, map_aff' _ _⟩, fun w hw => ?_⟩)) o (mem_Ohat.2 ho)
  · haveI : Subsingleton (Ohat F ⧸ Ideal.span {((1 : ℕ) : ↥(Ohat F))}) :=
      Ideal.Quotient.subsingleton_iff.2 (by simp)
    ext i j
    exact Subsingleton.elim _ _
  · rw [map_aff', h0 w hw, aff_zero']
