import Mathlib
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.CountSt

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts

open DirichletCharacter

private theorem cast_prim {a b : ℕ} (h : a = b) (χ : DirichletCharacter ℂ a) :
    (cast (congrArg (DirichletCharacter ℂ) h) χ).IsPrimitive ↔ χ.IsPrimitive := by
  subst h; rfl

private theorem cast_L {a b : ℕ} [NeZero a] [NeZero b] (h : a = b) (χ : DirichletCharacter ℂ a) (s : ℂ) :
    DirichletCharacter.LFunction (cast (congrArg (DirichletCharacter ℂ) h) χ) s = DirichletCharacter.LFunction χ s := by
  subst h; rfl

def toSig {n : ℕ} [NeZero n] (χ : DirichletCharacter ℂ n) : Σ N : ℕ, DirichletCharacter ℂ (N + 1) :=
  ⟨n - 1, cast (congrArg (DirichletCharacter ℂ) (Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2 (NeZero.ne n))).symm) χ⟩

theorem toSig_fst {n : ℕ} [NeZero n] (χ : DirichletCharacter ℂ n) : (toSig χ).1 + 1 = n := by
  exact Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2 (NeZero.ne n))

theorem toSig_isPrimitive {n : ℕ} [NeZero n] (χ : DirichletCharacter ℂ n) :
    (toSig χ).2.IsPrimitive ↔ χ.IsPrimitive := by
  exact cast_prim (Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2 (NeZero.ne n))).symm χ

theorem toSig_LFunction {n : ℕ} [NeZero n] (χ : DirichletCharacter ℂ n) (s : ℂ) :
    DirichletCharacter.LFunction (toSig χ).2 s = DirichletCharacter.LFunction χ s := by
  exact cast_L (Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2 (NeZero.ne n))).symm χ s

theorem toSig_level_eq {n m : ℕ} [NeZero n] [NeZero m] (χ : DirichletCharacter ℂ n) (ψ : DirichletCharacter ℂ m)
    (h : toSig χ = toSig ψ) : n = m := by
  have h1 := congrArg Sigma.fst h
  have hn := toSig_fst χ
  have hm := toSig_fst ψ
  omega

end Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts
