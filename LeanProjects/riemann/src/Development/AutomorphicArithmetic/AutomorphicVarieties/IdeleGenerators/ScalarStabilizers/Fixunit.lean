import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.WeightChange
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.GlobFixed
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.Sd

private theorem map_aff {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (y : Rˣ) :
    Matrix.GeneralLinearGroup.map f (aff y 0) = aff (Units.map (f : R →* S) y) 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [aff]

private theorem aff_mem {R : Type} [CommRing R] (y : Rˣ) : aff y 0 ∈ mirab R := by
  change Matrix.vecMul _ _ = _
  ext i
  fin_cases i <;> simp [aff, Matrix.vecMul, dotProduct, Fin.sum_univ_succ]

open UpperTheory.V.Af.GlobalFixedVectors Matrix in
theorem UpperTheory.V.Sd.Hm.fixunit :
    ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (φ : TR.Sm F 2), IsOpen {k | TR.finRep F 2 k φ = φ} →
        ∀ c : Pl F → ℕ, (∀ w, φ ∈ Hi.fixd (locSm F w) (K1 w (c w))) → ∀ u : (Af F)ˣ, (∀ w, Valued.v (pLoc F w (u : Af F)) = 1) →
        ∀ g, φ.1 (g * finGL F 2 (aff u 0)) = φ.1 g := by
  classical
  intro F _ _ _ φ hop c hc u hu g
  have key : ∀ S : Finset (Pl F),
      (∀ k ∈ KAway 2 1 S, (∀ w, GeneralLinearGroup.map (pLoc F w) k ∈ K1 w (c w)) → TR.finRep F 2 k φ = φ) →
      (∀ k ∈ KAway 2 1 ∅, (∀ w, GeneralLinearGroup.map (pLoc F w) k ∈ K1 w (c w)) → TR.finRep F 2 k φ = φ) := by
    intro S
    induction S using Finset.induction_on with
    | empty => exact id
    | insert w S hw ih =>
      intro h
      refine ih fun k hk hl => ?_
      have h1 := loc_mem w (mem_KAway.1 hk).1
      have h2 : k * (locGL F 2 w (GeneralLinearGroup.map (pLoc F w) k))⁻¹ ∈ KAway 2 1 (insert w S) := by
        refine mem_KAway.2 ⟨mul_mem (mem_KAway.1 hk).1 (inv_mem h1), fun u hu => ?_⟩
        by_cases huw : u = w
        · subst huw; simp [pLoc_locGL]
        · simp [pLoc_locGL_of_ne huw, (mem_KAway.1 hk).2 u ((Finset.mem_insert.1 hu).resolve_left huw)]
      have h3 : TR.finRep F 2 (locGL F 2 w (GeneralLinearGroup.map (pLoc F w) k)) φ = φ := hc w _ (hl w)
      have h4 := h _ h2 fun v => by
        by_cases hv : v = w
        · subst hv; simp [pLoc_locGL]
        · simpa [pLoc_locGL_of_ne hv] using hl v
      rwa [← h3, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel_right, h3] at h4
  obtain ⟨S, hS⟩ := exists_KAway_subset (M := 1) (hop.mem_nhds (by simp))
  have hi : ∀ w, Valued.v (pLoc F w ((u⁻¹ : (Af F)ˣ) : Af F)) = 1 := fun w => by
    have : Valued.v (pLoc F w ((u⁻¹ : (Af F)ˣ) : Af F)) * Valued.v (pLoc F w (u : Af F)) = 1 := by
      rw [← map_mul, ← map_mul, Units.inv_mul, map_one, map_one]
    rwa [hu, mul_one] at this
  have m1 : ∀ w, pLoc F w (u : Af F) ∈ w.adicCompletionIntegers F := fun w => (hu w).le
  have m2 : ∀ w, pLoc F w ((u⁻¹ : (Af F)ˣ) : Af F) ∈ w.adicCompletionIntegers F := fun w => (hi w).le
  let u0 : (Ohat F)ˣ := ⟨⟨u, mem_Ohat.2 m1⟩, ⟨((u⁻¹ : (Af F)ˣ) : Af F), mem_Ohat.2 m2⟩, Subtype.ext u.mul_inv, Subtype.ext u.inv_mul⟩
  have e := key S (fun k hk _ => hS hk) (aff u 0) (mem_KAway.2 ⟨⟨aff u0 0, ?_, ?_⟩, by simp⟩) fun w => ?_
  · exact congrFun (congrArg Subtype.val e) g
  · haveI : Subsingleton (Ohat F ⧸ Ideal.span {((1 : ℕ) : ↥(Ohat F))}) :=
      Ideal.Quotient.subsingleton_iff.2 (by simp)
    ext i j
    exact Subsingleton.elim _ _
  · rw [map_aff]; rfl
  · let u1 : (w.adicCompletionIntegers F)ˣ := ⟨⟨_, m1 w⟩, ⟨_, m2 w⟩,
      Subtype.ext (by change pLoc F w _ * pLoc F w _ = 1; rw [← map_mul, Units.mul_inv, map_one]),
      Subtype.ext (by change pLoc F w _ * pLoc F w _ = 1; rw [← map_mul, Units.inv_mul, map_one])⟩
    refine ⟨aff u1 0, ?_, ?_⟩
    · change GeneralLinearGroup.map _ (aff u1 0) ∈ mirab _
      rw [map_aff]
      exact aff_mem _
    · rw [map_aff, map_aff]
      congr 1
