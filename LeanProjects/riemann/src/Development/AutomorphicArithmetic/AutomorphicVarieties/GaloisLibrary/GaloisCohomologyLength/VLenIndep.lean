import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.GaloisCohomologyLength.LevelInertiaLeLevelDec

open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.GaloisCohomology UpperTheory.V.LDataCardLeFinrank

theorem UpperTheory.V.LDataCardLeFinrank.vLenIndep :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (D D' : LData F Ω l) (e : ℤ), D.S = D'.S ∧ VLen D e = VLen D' e := by
  intro F Ω _ _ _ _ _ l _ D D' e
  have hS : D.S = D'.S := Finset.coe_injective (D.hS.trans D'.hS.symm)
  refine ⟨hS, ?_⟩
  obtain ⟨S, hS₁, A, hA, chi, hchi⟩ := D
  obtain ⟨S', hS₂, A', hA', chi', hchi'⟩ := D'
  dsimp only at hS
  subst hS
  have hc : chi = chi' := by
    refine MonoidHom.ext fun x => ?_
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
    exact DFunLike.congr_fun (hchi.trans hchi'.symm) g
  subst hc
  rfl
