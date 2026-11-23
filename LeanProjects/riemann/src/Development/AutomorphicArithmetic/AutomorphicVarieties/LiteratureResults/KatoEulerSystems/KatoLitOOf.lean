import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KatoEulerSystems.KatoNOfKato

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Published.Kato Polynomial
open CongruenceSubgroup UpperTheory.V.Alg
open scoped Matrix MatrixGroups ModularForm

namespace UpperTheory.V.Lit

def KatoLitO : Prop :=
  ∀ (k M : ℕ), 2 ≤ k → 0 < M → ∀ (χ : DirichletCharacter ℂ M) (f : CuspForm (Gamma1 M) (k : ℤ)), Primitive k M χ f →
    ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ι : Qbar l ≃+* ℂ),
    ∃ V : G ℚ Ω →* GL (Fin 2) ↥(coefF f ι), Continuous V ∧ FrobPoly k M χ f ι (toBar V) ∧ (l ≠ 2 → OrdPoly 0 (1 - (k : ℤ)) (toBar V) →
      ∀ (K : Type) [Field K] [NumberField K] [IsAbelianGalois ℚ K] [Algebra K Ω] [IsScalarTower ℚ K Ω] (r : ℕ),
        1 ≤ r → r ≤ k - 1 → 2 * r ≠ k →
        ∀ (T : Submodule ℤ_[l] (Fin 2 → ↥(coefF f ι))) (hT : IsLat (tw V (cycE ℚ Ω (coefF f ι) ^ r)) T),
          (SelAll ((Loc.colRep (tw V (cycE ℚ Ω (coefF f ι) ^ r))).comp
              (AlgEquiv.restrictScalarsHom ℚ : G K Ω →* G ℚ Ω)) T (fun s => hT.stable _)).Finite)

def KatoO : Prop :=
  ∀ (k : ℕ), 2 ≤ k → ∀ (g : Newform k) (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω]
    (ι : Qbar l ≃+* ℂ), FiniteDimensional ℚ_[l] ↥(coefField g ι) ∧
    ∃ V : G ℚ Ω →* GL (Fin 2) ↥(coefField g ι), Continuous V ∧ g.Att ι (toBar V) ∧ (l ≠ 2 → OrdPoly 0 (1 - (k : ℤ)) (toBar V) →
      ∀ (K : Type) [Field K] [NumberField K] [IsAbelianGalois ℚ K] [Algebra K Ω] [IsScalarTower ℚ K Ω] (r : ℕ),
        1 ≤ r → r ≤ k - 1 → 2 * r ≠ k →
        ∀ (T : Submodule ℤ_[l] (Fin 2 → ↥(coefField g ι))) (hT : IsLat (tw V (cycE ℚ Ω (coefField g ι) ^ r)) T),
          (Sel ((Loc.colRep (tw V (cycE ℚ Ω (coefField g ι) ^ r))).comp
              (AlgEquiv.restrictScalarsHom ℚ : G K Ω →* G ℚ Ω)) T (fun s => hT.stable _)).Finite)

end UpperTheory.V.Lit
