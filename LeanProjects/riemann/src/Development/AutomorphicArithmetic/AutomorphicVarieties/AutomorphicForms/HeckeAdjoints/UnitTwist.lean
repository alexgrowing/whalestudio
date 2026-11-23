import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.HeckeAdjoints.HasPairingOfHerm
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.HeckeAdjoints.OneScalar
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.HeckeAdjoints.ExpoChar
open NumberField IsDedekindDomain Matrix Formalism.L2.Host UpperTheory.V UpperTheory.V.TR UpperTheory.V.Af.Gk

theorem UpperTheory.V.Af.Gk.unitTwist :
    UpperTheory.V.Af.Gk.UnitTwist := by
  intro F _ _ _ a ha π
  obtain ⟨s, hs⟩ := UpperTheory.V.Af.Gk.oneScalar F a π
  obtain ⟨χ, hχ⟩ := UpperTheory.V.Af.Gk.expoChar F (-s / ((Fintype.card (InfinitePlace F) : ℂ) * a))
  refine ⟨χ, ?_⟩
  rintro _ ⟨φ, hφ, rfl⟩
  have ht : (Matrix.of (oneL F a)).trace = (a : TR.Rinf F) := by
    change (1 : Matrix (Fin a) (Fin a) (TR.Rinf F)).trace = _
    simp
  have h1 : (Fintype.card (InfinitePlace F) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  have h2 : (a : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hd : TR.dchi χ (Matrix.of (oneL F a)).trace = -s := by
    rw [ht, TR.dchi_eq_sum]
    simp only [hχ, Pi.natCast_apply, Complex.ofReal_natCast, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    field_simp
  change TR.lie F a (oneL F a) (TR.mulChi a χ φ) = 0
  rw [TR.lie_mulChi, hs φ hφ, hd, ← add_smul, add_neg_cancel, zero_smul, map_zero]
