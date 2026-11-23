import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.CycRepApply
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.ConjEq

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Stick UpperTheory.V.FW
open scoped nonZeroDivisors

private theorem embT_mul (M : ℕ) [NeZero M] (L : Type) [Field L] [NumberField L] [IsCyclotomicExtension {M} ℚ L]
    (φ : L →+* ℂ) (g x : (ZMod M)ˣ) (a : L) : embT M L φ (g * x) a = embT M L φ x (sg M L g a) := by
  rw [mul_comm g x]
  simp [embT, map_mul, AlgEquiv.mul_apply]

theorem UpperTheory.V.FW.sgnStab :
    ∀ (M : ℕ) [NeZero M] (L : Type) [Field L] [NumberField L] [IsCyclotomicExtension {M} ℚ L] [IsCMField L] (φ : L →+* ℂ), Function.Surjective (embT M L φ) ∧ (∀ a : L, cE L a = a → sgn (embT M L φ) a ∈ evenF (-1 : (ZMod M)ˣ)) ∧ (∀ f ∈ sgnE (embT M L φ), ∀ g, (fun x => f (g * x)) ∈ sgnE (embT M L φ)) ∧ (fun _ => (1 : ZMod 2)) ∈ sgnE (embT M L φ) := by
  intro M _ L _ _ _ _ φ
  have : IsGalois ℚ L := IsCyclotomicExtension.isGalois {M} ℚ L
  have hc : ∀ a : L, sg M L (-1) a = cE L a := fun a => by
    have h := congrArg (fun e : L ≃+* L => e a) (conjEq M L).1
    simpa using h
  have hcomm : ∀ (g : (ZMod M)ˣ) (a : L), cE L (sg M L g a) = sg M L g (cE L a) := by
    intro g a
    rw [← hc, ← hc, ← AlgEquiv.mul_apply, ← AlgEquiv.mul_apply, ← map_mul, ← map_mul, mul_comm]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro ψ
    obtain ⟨σ, hσ⟩ := NumberField.ComplexEmbedding.exists_comp_symm_eq_of_comp_eq (k := ℚ) φ ψ
      (Subsingleton.elim _ _)
    refine ⟨(sg M L).symm σ.symm, ?_⟩
    rw [← hσ]
    ext x
    simp [embT]
  · intro a ha g
    simp only [sgn]
    rw [embT_mul, hc, ha]
  · intro f hf g
    induction hf using AddSubgroup.closure_induction with
    | mem f hf =>
      obtain ⟨u, hu, rfl⟩ := hf
      apply AddSubgroup.subset_closure
      have hv : ((Units.map (sgO M L g).toMonoidHom u : 𝓞 L) : L) = sg M L g ((u : 𝓞 L) : L) := by
        simp [sgO, RingOfIntegers.mapRingEquiv_apply]
      refine ⟨Units.map (sgO M L g).toMonoidHom u, ?_, ?_⟩
      · rw [hv, hcomm, hu]
      · funext x
        simp only [sgn, hv, embT_mul]
    | zero => exact zero_mem _
    | add f h _ _ hf hh => exact add_mem hf hh
    | neg f _ hf => exact neg_mem hf
  · apply AddSubgroup.subset_closure
    refine ⟨-1, ?_, ?_⟩
    · simp
    · funext x
      simp [sgn]
