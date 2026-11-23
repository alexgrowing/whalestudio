import Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.ModulusAdjoinISqrtNegPrimes
import Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.KerTwo
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.ShaLenEq
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.LenLeAdd
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.ContTw
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.GaloisCohomologyLength.ShaLenEqShaInv

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Two
open scoped Pointwise

theorem UpperTheory.V.Two.shaTwo :
    ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (E E' : Type) [Field E] [NumberField E] [Algebra E Ω] [Field E'] [NumberField E'] [Algebra E' Ω] (e : ℤ), galOf ℚ E' Ω ≤ galOf ℚ E Ω → (galOf ℚ E' Ω).relIndex (galOf ℚ E Ω) ∣ 2 → shaInv E 2 e ≤ 1 + shaInv E' 2 e := by
  intro Ω _ _ _ E E' _ _ _ _ _ _ e hle hidx
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : IsAlgClosure E Ω := ⟨inferInstance, Algebra.IsAlgebraic.tower_top (K := ℚ) E⟩
  haveI : IsAlgClosure E' Ω := ⟨inferInstance, Algebra.IsAlgebraic.tower_top (K := ℚ) E'⟩
  obtain ⟨D⟩ := ldata_nonempty (F := E) (Ω := Ω) 2
  obtain ⟨D'⟩ := ldata_nonempty (F := E') (Ω := Ω) 2
  have h1 := (shaLenEq ℚ E Ω 2 D e).1
  have h2 := (shaLenEq ℚ E' Ω 2 D' e).1
  rw [shaLen_eq_shaInv] at h1 h2
  have hsel := (selUp ℤ_[2] (G ℚ Ω) (QZ 2) (qzG ℚ Ω 2 e) _ _ hle (shaFam ℚ Ω 2)
    (conjStable_shaFam ℚ Ω 2)).1
  have hker := kerTwo (G ℚ Ω) (qzG ℚ Ω 2 e) _ _ hle ((Base.contTw ℚ Ω 2).2.1 e) hidx
  rw [h1, h2]
  calc _ ≤ _ := hsel
    _ ≤ _ := add_le_add_right hker _
    _ = _ := add_comm _ _
