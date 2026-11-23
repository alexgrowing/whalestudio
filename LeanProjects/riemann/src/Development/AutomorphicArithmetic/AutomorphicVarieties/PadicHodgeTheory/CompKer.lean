import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.IsFirstOrderDeformationOfRZero
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoQuot

open Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.HV UpperTheory.V.Base IsLocalRing

theorem UpperTheory.V.Loc.compKer :
    ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] [IsAdicComplete (maximalIdeal O) O] (E : Type) [Field E] [Algebra ℚ_[l] E] [Module.Finite ℚ_[l] E] [Algebra O E] [Algebra ℤ_[l] E] [IsScalarTower ℤ_[l] O E] [IsScalarTower ℤ_[l] ℚ_[l] E] [IsFractionRing O E] {Γ ι : Type} [Group Γ] [TopologicalSpace Γ] [Fintype ι] [DecidableEq ι] (rbar : Γ →* Matrix ι ι (ResidueField O)) (Pc : Cond O rbar) (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (ρ : Lift O rbar R), Represents Pc ρ → ∀ (x : R →ₐ[O] O) (P : Ideal R) {n : ℕ} (φ : R →ₐ[O] MvPowerSeries (Fin n) E), UpperTheory.V.Loc.IsCompl P x φ → (∃ y, x y ≠ 0 ∧ ∀ a ∈ P, y * a = 0) → ∀ (C : Type) [CommRing C] [Algebra O C] [IsCO O C] (f : R →ₐ[O] C), OnComp Pc (ρ.map x).hom (ρ.map f) ↔ P ≤ RingHom.ker f := by
  intro l _ O _ _ _ _ _ _ _ E _ _ _ _ _ _ _ _ Γ ι _ _ _ _ rbar Pc R _ _ _ ρ hR x P n φ hc hy0 C _ _ _ f
  have hcomp : ∀ {A B D : Type} [CommRing A] [Algebra O A] [IsCO O A] [CommRing B] [Algebra O B] [IsCO O B]
      [CommRing D] [Algebra O D] [IsCO O D] (u : A →ₐ[O] B) (v : B →ₐ[O] D) (r : Lift O rbar A),
      Lift.map v (Lift.map u r) = Lift.map (v.comp u) r := by
    intro A B D _ _ _ _ _ _ _ _ _ u v r
    apply Lift.ext
    ext γ a b
    rfl
  constructor
  · rintro ⟨B, _, _, _, _, ρB, hPB, ⟨x4, hx4⟩, y, hy⟩
    obtain ⟨g, hg, -⟩ := (hR B).2 ρB hPB
    subst hg
    have hf : y.comp g = f := by
      obtain ⟨h, -, huniq⟩ := (hR C).2 (Lift.map f ρ) ((hR C).1 f)
      rw [huniq (y.comp g) (by show Lift.map (y.comp g) ρ = _; rw [← hcomp]; exact hy), huniq f rfl]
    have hx : x4.comp g = x := by
      obtain ⟨h, -, huniq⟩ := (hR O).2 (Lift.map x ρ) ((hR O).1 x)
      refine (huniq (x4.comp g) ?_).trans (huniq x rfl).symm
      show Lift.map (x4.comp g) ρ = _
      rw [← hcomp]
      apply Lift.ext
      ext γ a b
      exact hx4 γ a b
    obtain ⟨y0, hy0ne, hann⟩ := hy0
    intro a ha
    rw [RingHom.mem_ker, ← hf]
    have hprod : g y0 * g a = 0 := by rw [← map_mul, hann a ha, map_zero]
    rcases mul_eq_zero.1 hprod with h0 | h0
    · exfalso
      apply hy0ne
      rw [← hx]
      simp [h0]
    · simp [h0]
  · intro hPf
    haveI : IsDomain (MvPowerSeries (Fin n) E) := NoZeroDivisors.to_isDomain _
    have hker : RingHom.ker φ = P := hc.ker
    haveI hprime : P.IsPrime := hker ▸ RingHom.ker_isPrime φ
    have hxP : ∀ a ∈ P, x a = 0 := by
      intro a ha
      have h1 := hc.const a
      rw [← hker, RingHom.mem_ker] at ha
      rw [ha, map_zero] at h1
      exact (IsFractionRing.injective O E) (by rw [← h1, map_zero])
    have hfP : ∀ a ∈ P, f a = 0 := fun a ha => (RingHom.mem_ker).1 (hPf ha)
    letI hco : IsCO O (R ⧸ P) :=
      co_quot O R (R ⧸ P) (Ideal.Quotient.mkₐ O P) (Ideal.Quotient.mkₐ_surjective O P)
    refine ⟨R ⧸ P, inferInstance, inferInstance, hco, inferInstance,
      Lift.map (Ideal.Quotient.mkₐ O P) ρ, (hR _).1 _, ⟨Ideal.Quotient.liftₐ P x hxP, ?_⟩,
      ⟨Ideal.Quotient.liftₐ P f hfP, ?_⟩⟩
    · intro γ a b
      rfl
    · rw [hcomp]
      apply Lift.ext
      ext γ a b
      rfl
