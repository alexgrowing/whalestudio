import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.HostFacts
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.PrimePairSizeCondition
import Development.AutomorphicArithmetic.PrimeDiscriminants.ExistsPrimitiveRootTorsionOrder
import Development.AutomorphicArithmetic.WeightCongruences.ProdNegOneZpow

open NumberField

noncomputable section

namespace UpperTheory.HF.Formalism.HC.HostRaw

open UpperTheory.HF _root_.Formalism _root_.Formalism.HC _root_.Formalism.HC.HostRaw

variable {φ : Frame} (H : HostRaw φ)

def muO (l : ℕ) : ℕ := Module.finrank H.E (CyclotomicField l H.E)

instance muW_neZero : NeZero H.w := ⟨H.w_pos.ne'⟩

def muGen : H.E := H.exists_primitiveRoot_w.choose

theorem muGen_prim : IsPrimitiveRoot H.muGen H.w := H.exists_primitiveRoot_w.choose_spec

theorem dvd_w_iff {m : ℕ} (hm : 0 < m) : m ∣ H.w ↔ ∃ ζ : H.E, IsPrimitiveRoot ζ m := by
  constructor
  · rintro ⟨k, hk⟩
    exact ⟨_, H.muGen_prim.pow H.w_pos (hk.trans (mul_comm _ _))⟩
  · rintro ⟨ζ, hζ⟩
    have : NeZero m := ⟨hm.ne'⟩
    exact NumberField.Units.dvd_torsionOrder_of_isPrimitiveRoot hζ

theorem isMu_iff_pow (x : H.E) : H.IsMu x ↔ ∃ k : ℕ, x = H.muGen ^ k := by
  rw [isMu_iff]
  constructor
  · intro h
    obtain ⟨k, -, hk⟩ := H.muGen_prim.eq_pow_of_pow_eq_one h
    exact ⟨k, hk.symm⟩
  · rintro ⟨k, rfl⟩
    rw [← pow_mul, mul_comm, pow_mul, H.muGen_prim.pow_eq_one, one_pow]

def muExp : φ.GG →* (ZMod H.w)ˣ := (H.muGen_prim.autToPow ℚ).comp H.gal.symm.toMonoidHom

def psiAut (τ : φ.Psi) : H.E →+* H.E := (H.gal.symm (τ : φ.GG) : H.E →+* H.E)

def CondMU [Fintype φ.Psi] (a : φ.Psi → ℤ) : Prop := UpperTheory.MU H.psiAut a

abbrev IsRt (x : H.E) : Prop := H.IsMu x

abbrev muW : ℕ := H.w

theorem dvd_muW_iff {m : ℕ} (hm : 0 < m) : m ∣ H.muW ↔ ∃ ζ : H.E, IsPrimitiveRoot ζ m := H.dvd_w_iff hm

theorem isRt_iff (x : H.E) : H.IsRt x ↔ x ^ H.muW = 1 := H.isMu_iff x

theorem isRt_iff_pow (x : H.E) : H.IsRt x ↔ ∃ k : ℕ, x = H.muGen ^ k := H.isMu_iff_pow x

end UpperTheory.HF.Formalism.HC.HostRaw

end
