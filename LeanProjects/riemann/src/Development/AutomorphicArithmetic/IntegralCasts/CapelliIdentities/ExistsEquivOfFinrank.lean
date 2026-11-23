import Mathlib

open NumberField in
private theorem ext_hom {F : Type} [Field F] [NumberField F] {A : Type} [Ring A] [Algebra ℚ A]
    (φ : RingOfIntegers F →+* A) :
    ∃ ψ : F →+* A, ∀ c : RingOfIntegers F, ψ (algebraMap _ F c) = φ c := by
  haveI : Algebra.IsPushout ℤ (RingOfIntegers F) ℚ F :=
    Algebra.isPushout_of_isLocalization (nonZeroDivisors ℤ) ℚ (RingOfIntegers F) F
  refine ⟨(Algebra.pushoutDesc F φ.toIntAlgHom (algebraMap ℚ A).toIntAlgHom
    (fun x y => (Algebra.commutes y (φ x)).symm)).toRingHom, fun c => ?_⟩
  exact Algebra.pushoutDesc_left F _ _ _ c

private theorem tower {F : Type} [Field F] [NumberField F] {V : Type} [AddCommGroup V]
    [Module ℚ V] (ψ : F →+* Module.End ℚ V) :
    letI : Module F V := Module.compHom V ψ
    IsScalarTower ℚ F V := by
  letI : Module F V := Module.compHom V ψ
  refine ⟨fun q a v => ?_⟩
  change ψ (q • a) v = q • ψ a v
  rw [map_rat_smul ψ q a]
  rfl

theorem UpperTheory.Reformulated.B.ExistsEquivOfFinrank.exists_equiv_of_finrank :
    ∀ {F : Type} [inst : Field F] [NumberField F]
    {V V' : Type} [inst_2 : AddCommGroup V] [inst_3 : _root_.Module ℚ V] [FiniteDimensional ℚ V]
    [inst_5 : AddCommGroup V'] [inst_6 : _root_.Module ℚ V'] [FiniteDimensional ℚ V']
    (φ : NumberField.RingOfIntegers F →+* Module.End ℚ V) (φ' : NumberField.RingOfIntegers F →+* Module.End ℚ V'),
    Module.finrank ℚ V = Module.finrank ℚ V' →
      ∃ (e : V ≃ₗ[ℚ] V'),
        ∀ (c : NumberField.RingOfIntegers F) (v : V),
          (e : V → V') (((φ : NumberField.RingOfIntegers F → Module.End ℚ V) c : V → V) v) =
            ((φ' : NumberField.RingOfIntegers F → Module.End ℚ V') c : V' → V') ((e : V → V') v) := by
  intro F _ _ V V' _ _ _ _ _ _ φ φ' h
  obtain ⟨ψ, hψ⟩ := ext_hom φ
  obtain ⟨ψ', hψ'⟩ := ext_hom φ'
  letI : Module F V := Module.compHom V ψ
  letI : Module F V' := Module.compHom V' ψ'
  haveI := tower ψ
  haveI := tower ψ'
  haveI : Module.Finite F V := Module.Finite.of_restrictScalars_finite ℚ F V
  haveI : Module.Finite F V' := Module.Finite.of_restrictScalars_finite ℚ F V'
  have h2 : Module.finrank F V = Module.finrank F V' := by
    rw [← Module.finrank_mul_finrank ℚ F V, ← Module.finrank_mul_finrank ℚ F V'] at h
    exact Nat.eq_of_mul_eq_mul_left Module.finrank_pos h
  let e : V ≃ₗ[F] V' := LinearEquiv.ofFinrankEq V V' h2
  refine ⟨e.restrictScalars ℚ, fun c v => ?_⟩
  rw [← hψ, ← hψ']
  exact e.map_smul (algebraMap _ F c) v
