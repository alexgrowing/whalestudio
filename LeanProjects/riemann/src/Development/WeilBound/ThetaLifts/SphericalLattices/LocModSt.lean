import Development.AutomorphicSpectrum.Proofs.MembershipProofs.BigCellLocal
import Development.AbelianVarietyTheory.Definitions.Divisors.LineOppositeParabolicUnitaryLeviSectionEq
import Formalism.SatakeDualWeyl.StatementF
import Development.WeilBound.ThetaLifts.SphericalLattices.FunDefs

noncomputable section

namespace PositivityTheory.Sph.M2

open Matrix Formalism.UG GlobalTheory.CompanionTheory.VacLoc.BigCellLocal

section Loc

variable (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (c : L →+* L) (m : ℕ)

def GW : Subgroup (GL (Fin m ⊕ Fin m) L) where
  carrier := {g | Iso c (Wm L (Fin m)) (Wm L (Fin m)) (g : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) L)}
  one_mem' := by
    show Iso c _ _ ((1 : GL (Fin m ⊕ Fin m) L) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) L)
    simp [Iso, Matrix.map_one _ (map_zero c) (map_one c)]
  mul_mem' := fun {a b} ha hb => by
    show Iso c _ _ ((a * b : GL (Fin m ⊕ Fin m) L) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) L)
    rw [Units.val_mul]; exact Iso.mul ha hb
  inv_mem' := fun {a} ha => by
    show Iso c _ _ ((a⁻¹ : GL (Fin m ⊕ Fin m) L) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) L)
    exact Iso.inv ha (by rw [← Units.val_mul, mul_inv_cancel, Units.val_one])

def IntGL : Subgroup (GL (Fin m ⊕ Fin m) L) := (Matrix.GeneralLinearGroup.map (intL L).subtype).range

def KW : Subgroup (GL (Fin m ⊕ Fin m) L) := GW L c m ⊓ IntGL L m

def PW : Subgroup (GL (Fin m ⊕ Fin m) L) :=
  GW L c m ⊓ GlobalTheory.LGrp.blockQ L (GlobalTheory.LGrp.twoBlocks (Fin m) (Fin m))

abbrev KPW : Subgroup (GL (Fin m ⊕ Fin m) L) := PW L c m ⊓ KW L c m

def levM (t : GL (Fin m) L) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) L :=
  fromBlocks (t : Matrix (Fin m) (Fin m) L) 0 0 (((t⁻¹ : GL (Fin m) L) : Matrix (Fin m) (Fin m) L)ᵀ.map c)

def lev : GL (Fin m) L →* GL (Fin m ⊕ Fin m) L where
  toFun t := ⟨levM L c m t, levM L c m t⁻¹,
    by
      have h1 : (t : Matrix (Fin m) (Fin m) L) * ((t⁻¹ : GL (Fin m) L) : Matrix (Fin m) (Fin m) L) = 1 := Units.mul_inv t
      simp only [levM, fromBlocks_multiply, inv_inv, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]
      rw [h1, ← Matrix.map_mul, ← Matrix.transpose_mul, h1, Matrix.transpose_one,
        Matrix.map_one _ (map_zero c) (map_one c), fromBlocks_one],
    by
      have h2 : ((t⁻¹ : GL (Fin m) L) : Matrix (Fin m) (Fin m) L) * (t : Matrix (Fin m) (Fin m) L) = 1 := Units.inv_mul t
      simp only [levM, fromBlocks_multiply, inv_inv, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]
      rw [h2, ← Matrix.map_mul, ← Matrix.transpose_mul, h2, Matrix.transpose_one,
        Matrix.map_one _ (map_zero c) (map_one c), fromBlocks_one]⟩
  map_one' := by
    ext1
    simp [levM, Matrix.map_one _ (map_zero c) (map_one c), fromBlocks_one]
  map_mul' s t := by
    ext1
    simp only [Units.val_mul, levM, fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]
    rw [_root_.mul_inv_rev, Units.val_mul, Matrix.transpose_mul, Matrix.map_mul]

def zW (x : Lˣ) : GL (Fin m ⊕ Fin m) L :=
  ⟨fromBlocks ((x : L) • 1) 0 0 (((x⁻¹ : Lˣ) : L) • 1), fromBlocks (((x⁻¹ : Lˣ) : L) • 1) 0 0 ((x : L) • 1),
    by simp [fromBlocks_multiply, smul_smul, fromBlocks_one],
    by simp [fromBlocks_multiply, smul_smul, fromBlocks_one]⟩

def LocModSt : Prop :=
  ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (c : L →+* L) (q : ℕ), IsUnramInv ϖ c q →
    ∀ (m : ℕ), ∀ p ∈ PW L c m,
      ((((KPW L c m).map (MulAut.conj p⁻¹).toMonoidHom).relIndex (KPW L c m) : ℕ) : ℝ) =
        (q : ℝ) ^ (-(2 * (m : ℤ) * ordL (p : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) L).toBlocks₁₁.det)) *
        ((((KPW L c m).map (MulAut.conj p).toMonoidHom).relIndex (KPW L c m) : ℕ) : ℝ)

end Loc

end PositivityTheory.Sph.M2

end
