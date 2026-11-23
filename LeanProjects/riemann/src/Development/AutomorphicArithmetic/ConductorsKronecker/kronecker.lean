import Development.AutomorphicArithmetic.PrimitiveCosets.RecH
import Development.AutomorphicArithmetic.PrimitiveCosets.ToEBij

open UpperTheory.Comparison₂ Formalism Formalism.HC Formalism.D5 Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.LHost NumberField Ideal

private theorem UpperTheory.GL.kron_sgn (s : ℤˣ) :
    (Multiplicative.toAdd (Formalism.LFunctionChainParameters.LHost.sgn2 s) = 0 ↔ s = 1) ∧ (Multiplicative.toAdd (Formalism.LFunctionChainParameters.LHost.sgn2 s) = 1 ↔ s = -1) := by
  revert s
  decide

private theorem UpperTheory.GL.kron_int (s : ℤˣ) (J : ℤ) (h : (s : ℤ) = J) :
    (Multiplicative.toAdd (Formalism.LFunctionChainParameters.LHost.sgn2 s) = 0 ↔ J = 1) ∧ (Multiplicative.toAdd (Formalism.LFunctionChainParameters.LHost.sgn2 s) = 1 ↔ J = -1) := by
  subst h
  rw [(UpperTheory.GL.kron_sgn s).1, (UpperTheory.GL.kron_sgn s).2, Units.ext_iff, Units.ext_iff]
  simp

theorem UpperTheory.GL.kronecker :
    ∀ {φ : Frame} (H : HostAx φ) (m : ℕ) (hm : m.Coprime H.condN),
      ((recH H.toHostRaw (ZMod.unitOfCoprime m hm)).toAdd.1.1 = 0 ↔ jacobiSym (-(H.d : ℤ)) m = 1) ∧
      ((recH H.toHostRaw (ZMod.unitOfCoprime m hm)).toAdd.1.1 = 1 ↔ jacobiSym (-(H.d : ℤ)) m = -1) ∧
      ((recH H.toHostRaw (ZMod.unitOfCoprime m hm)).toAdd.1.2 = 0 ↔ (H.art (ZMod.unitOfCoprime m hm)).1.1 = 1) ∧
      ((recH H.toHostRaw (ZMod.unitOfCoprime m hm)).toAdd.1.2 = 1 ↔ (H.art (ZMod.unitOfCoprime m hm)).1.1 = -1) ∧
      (H.PsQ → ((recH H.toHostRaw (ZMod.unitOfCoprime m hm)).toAdd.1.2 = 0 ↔ jacobiSym (-(H.q : ℤ)) m = 1) ∧
        ((recH H.toHostRaw (ZMod.unitOfCoprime m hm)).toAdd.1.2 = 1 ↔ jacobiSym (-(H.q : ℤ)) m = -1)) ∧
      (recH H.toHostRaw (ZMod.unitOfCoprime m hm)).toAdd.2 = φ.iotaInv (H.art (ZMod.unitOfCoprime m hm)).2 := by
  intro φ H m hm
  have hd : (((H.art (ZMod.unitOfCoprime m hm)).1.2 : ℤˣ) : ℤ) = jacobiSym (-(H.d : ℤ)) m := by
    rw [H.der.art_ch, jacobi_neg_recip H.d_mod_four (H.odd_of_coprime hm)]
    exact jacobi_congr ((H.val_unitOfCoprime hm).of_dvd H.d_dvd_condN)
  refine ⟨(UpperTheory.GL.kron_int _ _ hd).1, (UpperTheory.GL.kron_int _ _ hd).2, (UpperTheory.GL.kron_sgn _).1, (UpperTheory.GL.kron_sgn _).2,
    fun hP => UpperTheory.GL.kron_int _ _ ?_, rfl⟩
  rw [← H.psAt_of_coprime hm, hP.psAt_eq hm]
