import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.CoefFieldEq
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.KatoUse

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Published.Kato Polynomial
open CongruenceSubgroup UpperTheory.V.Alg
open scoped Matrix MatrixGroups ModularForm

namespace UpperTheory.V.Lit

def OrdPoly {l : ℕ} [Fact l.Prime] {Ω : Type} [Field Ω] [Algebra ℚ Ω] (a b : ℤ) (V : G ℚ Ω →* GL (Fin 2) (Qbar l)) : Prop :=
  ∃ (A : ValuationSubring Ω) (N : ℕ), A.valuation (l : Ω) < 1 ∧ 1 ≤ N ∧ ∀ s ∈ Ine (F := ℚ) A, (∀ ζ : Ω, ζ ^ N = 1 → s ζ = ζ) →
    (V s : Matrix (Fin 2) (Fin 2) (Qbar l)).charpoly =
      (X - C ((cycBar ℚ Ω l s ^ a : (Qbar l)ˣ) : Qbar l)) * (X - C ((cycBar ℚ Ω l s ^ b : (Qbar l)ˣ) : Qbar l))

def KatoLitN : Prop :=
  ∀ (k M : ℕ), 2 ≤ k → 0 < M → ∀ (χ : DirichletCharacter ℂ M) (f : CuspForm (Gamma1 M) (k : ℤ)), Primitive k M χ f →
    ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ι : Qbar l ≃+* ℂ),
    ∃ V : G ℚ Ω →* GL (Fin 2) ↥(coefF f ι), Continuous V ∧ FrobPoly k M χ f ι (toBar V) ∧ (OrdPoly 0 (1 - (k : ℤ)) (toBar V) →
      ∀ (K : Type) [Field K] [NumberField K] [IsAbelianGalois ℚ K] [Algebra K Ω] [IsScalarTower ℚ K Ω] (r : ℕ),
        1 ≤ r → r ≤ k - 1 → 2 * r ≠ k →
        ∀ (T : Submodule ℤ_[l] (Fin 2 → ↥(coefF f ι))) (hT : IsLat (tw V (cycE ℚ Ω (coefF f ι) ^ r)) T),
          (SelAll ((Loc.colRep (tw V (cycE ℚ Ω (coefF f ι) ^ r))).comp
              (AlgEquiv.restrictScalarsHom ℚ : G K Ω →* G ℚ Ω)) T (fun s => hT.stable _)).Finite)

def KatoN : Prop :=
  ∀ (k : ℕ), 2 ≤ k → ∀ (g : Newform k) (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω]
    (ι : Qbar l ≃+* ℂ), FiniteDimensional ℚ_[l] ↥(coefField g ι) ∧
    ∃ V : G ℚ Ω →* GL (Fin 2) ↥(coefField g ι), Continuous V ∧ g.Att ι (toBar V) ∧ (OrdPoly 0 (1 - (k : ℤ)) (toBar V) →
      ∀ (K : Type) [Field K] [NumberField K] [IsAbelianGalois ℚ K] [Algebra K Ω] [IsScalarTower ℚ K Ω] (r : ℕ),
        1 ≤ r → r ≤ k - 1 → 2 * r ≠ k →
        ∀ (T : Submodule ℤ_[l] (Fin 2 → ↥(coefField g ι))) (hT : IsLat (tw V (cycE ℚ Ω (coefField g ι) ^ r)) T),
          (Sel ((Loc.colRep (tw V (cycE ℚ Ω (coefField g ι) ^ r))).comp
              (AlgEquiv.restrictScalarsHom ℚ : G K Ω →* G ℚ Ω)) T (fun s => hT.stable _)).Finite)

def KatoUseN : Prop :=
  ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ι : Qbar l ≃+* ℂ) (e : ℕ), 1 ≤ e →
    ∀ (f : Af.Newform (2 * e + 1)) (W : G ℚ Ω →* GL (Fin 2) (Qbar l)), Continuous W →
      f.Att ι (Af.tw W (cycBar ℚ Ω l ^ (-(e : ℤ)))) → OrdPoly (e : ℤ) (-(e : ℤ)) W →
      ∀ (M : ℕ) (φ : G ℚ Ω →* (Qbar l)ˣ), 1 ≤ M → Af.KillsMu M φ → Af.BlochKatoSelmerVanishes l (Loc.colRep (Af.tw W φ))

structure InpN : Prop extends U3.CohInp where
  lemM : LemmaM
  lemM' : LemmaM'
  lemP : LemmaP
  kato : KatoUseN
  adK : Af.AdVanishK
  adQ : Af.AdVanishQ
  newAut : Af.NewformAut
  number : Af.CongruenceNumberRankThree

end UpperTheory.V.Lit
