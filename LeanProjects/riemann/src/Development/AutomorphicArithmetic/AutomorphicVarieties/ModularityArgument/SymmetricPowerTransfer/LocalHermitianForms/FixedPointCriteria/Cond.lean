import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.FixedPointCriteria.IntDown
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.IrreducibleParity.NotEvenIrr

noncomputable section

namespace UpperTheory.V.Z.Sym.Loc.PK

open QuadraticAlgebra UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc

variable {O K : Type} [CommRing O] [Field K] [Algebra O K] {τ : K}

variable (O τ) in

def Gu : Subgroup (Etau K τ)ˣ where
  carrier := {u | IsIntegral O (u : Etau K τ) ∧ IsIntegral O ((u⁻¹ : (Etau K τ)ˣ) : Etau K τ)}
  one_mem' := by simp [isIntegral_one]
  mul_mem' {a b} ha hb := ⟨by simpa using ha.1.mul hb.1, by
    rw [_root_.mul_inv_rev, Units.val_mul]; exact hb.2.mul ha.2⟩
  inv_mem' {a} ha := ⟨ha.2, by simpa using ha.1⟩

variable (O) in

def Ord (y : Etau K τ) : Set (Etau K τ) := (Submodule.span O {1, y} : Submodule O (Etau K τ))

variable (O) in

def Hu (y : Etau K τ) : Subgroup (Etau K τ)ˣ where
  carrier := {u | PS.ml u (Ord O y) = Ord O y}
  one_mem' := PS.ml_one _
  mul_mem' {a b} ha hb := by
    change PS.ml (a * b) _ = _
    rw [PS.ml_mul, show PS.ml b (Ord O y) = Ord O y from hb, show PS.ml a (Ord O y) = Ord O y from ha]
  inv_mem' {a} ha := by
    change PS.ml a⁻¹ _ = _
    conv_lhs => rw [← show PS.ml a (Ord O y) = Ord O y from ha]
    rw [← PS.ml_mul, inv_mul_cancel, PS.ml_one]

def yy (π : O) (m : ℕ) (x : Etau K τ) : Etau K τ := algebraMap O K (π ^ m) • x

structure Cond (π : O) (n : ℕ) (e : Oˣ) (h : O) (x : Etau K τ) : Prop where
  irr : Irreducible π
  gen : Gen1 O x
  tr : QuadraticAlgebra.trace x = 0
  sq : x * x = algebraMap O (Etau K τ) (e : O)
  om : (ω : Etau K τ) = algebraMap O (Etau K τ) h + yy π n x

end UpperTheory.V.Z.Sym.Loc.PK
