import Development.AutomorphicArithmetic.AutomorphicVarieties.OddResidueBounds.ZeroMemUnrHom
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.LenComp

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Bern UpperTheory.V.B4 UpperTheory.V.B5 UpperTheory.V.Odd

private theorem length_ker_pow_le (R X : Type) [CommRing R] [AddCommGroup X] [Module R X]
    (f : Module.End R X) (r : ℕ) :
    Module.length R (LinearMap.ker (f ^ r)) ≤ r * Module.length R (LinearMap.ker f) := by
  induction r with
  | zero =>
    simp only [Nat.cast_zero, zero_mul, nonpos_iff_eq_zero]
    rw [Module.length_eq_zero_iff]
    refine ⟨fun x y => Subtype.ext ?_⟩
    have hx := LinearMap.mem_ker.mp x.2
    have hy := LinearMap.mem_ker.mp y.2
    simp only [pow_zero, Module.End.one_apply] at hx hy
    rw [hx, hy]
  | succ n ih =>
    rw [pow_succ]
    refine ((UpperTheory.V.Base.lenComp R X (f ^ n) f).1).trans ?_
    calc Module.length R (LinearMap.ker (f ^ n)) + Module.length R (LinearMap.ker f)
        ≤ n * Module.length R (LinearMap.ker f) + Module.length R (LinearMap.ker f) := by
          gcongr
      _ = ((n + 1 : ℕ) : ℕ∞) * Module.length R (LinearMap.ker f) := by
          push_cast; rw [add_mul, one_mul]

theorem UpperTheory.V.Odd.lenPow :
    ∀ (R X : Type) [CommRing R] [AddCommGroup X] [Module R X] (P : Submodule R X) (a : R) (r : ℕ), (∀ x ∈ P, a ^ r • x = 0) → Module.length R P ≤ r * Module.length R (Submodule.torsionBy R X a) := by
  intro R X _ _ _ P a r hP
  let f : Module.End R X := a • (1 : Module.End R X)
  have hker : LinearMap.ker f = Submodule.torsionBy R X a := by
    ext x
    simp [f, Submodule.mem_torsionBy_iff]
  have hpow : ∀ x : X, (f ^ r) x = a ^ r • x := by
    intro x
    simp [f, smul_pow]
  have hle : P ≤ LinearMap.ker (f ^ r) := by
    intro x hx
    rw [LinearMap.mem_ker, hpow]
    exact hP x hx
  calc Module.length R P ≤ Module.length R (LinearMap.ker (f ^ r)) :=
        Module.length_le_of_injective (Submodule.inclusion hle) (Submodule.inclusion_injective hle)
    _ ≤ r * Module.length R (LinearMap.ker f) := length_ker_pow_le R X f r
    _ = r * Module.length R (Submodule.torsionBy R X a) := by rw [hker]
