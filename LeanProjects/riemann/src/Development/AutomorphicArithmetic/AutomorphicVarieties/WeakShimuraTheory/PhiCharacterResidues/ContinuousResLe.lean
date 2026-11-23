import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.IsAlgClosureField
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.Inertia

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement
open GlobalTheory.CuspRep GlobalTheory.GalOfCusp

namespace UpperTheory.V.Ws

variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} {D : Raw Ω c}

theorem continuous_resLe {F L : IntermediateField ℚ Ω} (h : F ≤ L) : Continuous (resLe h) := by
  letI : Algebra F L := (IntermediateField.inclusion h).toRingHom.toAlgebra
  haveI : IsScalarTower F L Ω := IsScalarTower.of_algebraMap_eq fun _ => rfl
  exact Af.continuous_restrictScalarsHom F L Ω

namespace Link

variable {T : Tower D} {c' : Coef l} {h : c.O ≤ c'.O} (K : Link T c' h) (X : Space (T.fr ∅) (inc h)) (n : ℕ)

def sc (g : G T.L Ω) : c'.O := K.κ g * K.β g ^ n

theorem sc_one : K.sc n 1 = 1 := by simp [sc]

theorem sc_mul (g g' : G T.L Ω) : K.sc n (g * g') = K.sc n g * K.sc n g' := by
  simp only [sc, map_mul, Units.val_mul, mul_pow]; ring

def rho : G T.L Ω →* M4 X.A where
  toFun g := algebraMap c'.O X.A (K.sc n g) • X.P.r (resLe T.F_le g)
  map_one' := by simp [sc_one]
  map_mul' g g' := by
    simp only [sc_mul, map_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    rw [mul_comm]

theorem rho_apply (g : G T.L Ω) : K.rho X n g = algebraMap c'.O X.A (K.sc n g) • X.P.r (resLe T.F_le g) := rfl

def cpT (g : G T.L Ω) : X.B[X] := (X.cp (resLe T.F_le g)).scaleRoots (algebraMap c'.O X.B (K.sc n g))

def IsPsiT (ψ : ∀ v : W.Vl l T.L, Fin 4 → Dec (F := T.L) (K.s.A v) →* X.Bˣ) : Prop :=
  ∀ v i g, (ψ v i g : X.B) = algebraMap c'.O X.B (K.sc n g) * X.ψ (K.e v) i (resLe T.F_le g)

end Link

end UpperTheory.V.Ws

end
