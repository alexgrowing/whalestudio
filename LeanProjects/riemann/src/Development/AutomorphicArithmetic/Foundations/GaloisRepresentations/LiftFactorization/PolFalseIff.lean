import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.InertiaQuadraticRamification.ThreeApartOf
import Development.AutomorphicArithmetic.Foundations.Convolution.SphericalIdeles.RamDefs
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.CyclicStrongAtCusp

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp GlobalTheory.GalCut GlobalTheory.RealGal GlobalTheory.UnitaryBC UpperTheory.V.Published UpperTheory.Gal.UnramifiedFromSplittingCriterion UpperTheory.ConvolutionTheory.Sph

namespace UpperTheory.Gal.AbelianGaloisNormality

def FieldOK (l : ℕ) (E : Type) [Field E] [NumberField E] [IsCMField E] : Prop :=
  (∃ x : E, ∃ d : ℕ, 0 < d ∧ x ^ 2 = -(d : E)) ∧ Even (Module.finrank ℚ (maximalRealSubfield E)) ∧
    (∀ w : HeightOneSpectrum (𝓞 E), Algebra.IsUnramifiedAt (𝓞 (maximalRealSubfield E)) w.asIdeal) ∧
    (∀ w : HeightOneSpectrum (𝓞 E), ((l : ℕ) : 𝓞 E) ∈ w.asIdeal → IsSplitAt w) ∧
    ∃ w₁ w₂ w₃ : HeightOneSpectrum (𝓞 E), ((l : ℕ) : 𝓞 E) ∈ w₁.asIdeal ∧ ((l : ℕ) : 𝓞 E) ∈ w₂.asIdeal ∧
      ((l : ℕ) : 𝓞 E) ∈ w₃.asIdeal ∧ GlobalTheory.Cong.Apart w₁ w₂ ∧ GlobalTheory.Cong.Apart w₁ w₃ ∧ GlobalTheory.Cong.Apart w₂ w₃

def Spl {E : Type} [Field E] [NumberField E] (Ω : Type) [Field Ω] [Algebra E Ω] (M : Type) [Field M] [Algebra M Ω]
    (T : Set (HeightOneSpectrum (𝓞 E))) : Prop :=
  ∀ t ∈ T, ∀ A : ValuationSubring Ω, IsPlaceOver A t → ∀ g ∈ Dec (F := E) A, Fixes M g

def SplTop {E : Type} [Field E] [NumberField E] (M : Type) [Field M] [NumberField M] [IsCMField M] [Algebra E M]
    (T : Set (HeightOneSpectrum (𝓞 E))) : Prop :=
  ∀ w : HeightOneSpectrum (𝓞 M), w.under (𝓞 E) ∈ T → IsSplitAt w

def Pol (c : Bool) {E : Type} [Field E] [NumberField E] [IsCMField E] {a : ℕ} (π : CuspSub E a) : Prop :=
  (CG.mk π).IsRegAlg ∧ ∃ χ : HChar (maximalRealSubfield E), GlobalTheory.ContraPair.PolarizedPair π χ ∧ (c = true → χ = quadChar E ^ a)

inductive Layers (Ω : Type) [Field Ω] (E : Type) [Field E] [NumberField E] [Algebra E Ω] :
    ∀ (M : Type) [Field M] [NumberField M] [Algebra M Ω] [Algebra E M], Prop
  | refl : Layers Ω E E
  | step (X Y : Type) [Field X] [NumberField X] [Algebra X Ω] [Algebra E X] [Field Y] [NumberField Y] [IsCMField Y] [Algebra Y Ω]
      [Algebra E Y] [Algebra X Y] [IsScalarTower E X Y] [IsScalarTower X Y Ω] :
      Layers Ω E X → IsGalois X Y → (Module.finrank X Y).Prime → Layers Ω E Y

def Disjoint' {E Ω : Type} (M : Type) [Field E] [Field M] [Field Ω] [Algebra E Ω] [Algebra M Ω] (N : Subgroup (G E Ω)) : Prop :=
  ∀ g : G E Ω, ∃ x n : G E Ω, Fixes M x ∧ n ∈ N ∧ g = x * n

def Reach (Ω : Type) [Field Ω] (l : ℕ) (c : Bool) {a : ℕ} :
    ℕ → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [Algebra E Ω], CuspSub E a → Prop
  | 0 => fun E _ _ _ _ π => FieldOK l E ∧ GlobalTheory.GalCut.Good l π
  | k + 1 => fun E _ _ _ _ π => ∀ T : Set (HeightOneSpectrum (𝓞 E)), T.Finite →
      {Q : QCM E Ω | Spl Ω ↥Q.K T ∧ (k = 0 → SplTop ↥Q.K T) ∧ RamOff T Q ∧
        ∃ P : CuspSub ↥Q.K a, IsLiftUnr π P ∧ Pol c P ∧ Reach Ω l c k ↥Q.K P}.Infinite

def BCFam : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ), l.Prime →
    ∀ a : ℕ, 1 ≤ a → ∀ (c : Bool) (π : CuspSub E a), Pol c π → Reach Ω l c 3 E π

def BCGood : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ), l.Prime →
    ∀ a : ℕ, 1 ≤ a → ∀ (c : Bool) (π : CuspSub E a), Pol c π → ∀ S : Set (HeightOneSpectrum (𝓞 E)), S.Finite →
    ∀ N : Subgroup (G E Ω), IsOpen (N : Set (G E Ω)) →
    ∃ (M : Type) (_ : Field M) (_ : NumberField M) (_ : IsCMField M) (_ : Algebra M Ω) (_ : IsAlgClosure M Ω)
      (_ : Algebra E M) (_ : IsScalarTower E M Ω), Layers Ω E M ∧ Disjoint' M N ∧ Spl Ω M S ∧ SplTop M S ∧ FieldOK l M ∧
      ∃ P : CuspSub M a, IsLiftUnr π P ∧ Pol c P ∧ GlobalTheory.GalCut.Good l P

abbrev Rel (a : ℕ) : Type 1 :=
  ∀ (K M : Type) [Field K] [NumberField K] [IsCMField K] [Field M] [NumberField M] [IsCMField M] [Algebra K M],
    CuspSub K a → CuspSub M a → Prop

structure Rel.Tower {a : ℕ} (R : Rel a) : Prop where
  refl : ∀ (K : Type) [Field K] [NumberField K] [IsCMField K] (π : CuspSub K a), R K K π π
  layer : ∀ (K M : Type) [Field K] [NumberField K] [IsCMField K] [Field M] [NumberField M] [IsCMField M] [Algebra K M]
    [IsGalois K M], (Module.finrank K M).Prime → ∀ (π : CuspSub K a) (P : CuspSub M a), IsLiftUnr π P → R K M π P
  trans : ∀ (K M L : Type) [Field K] [NumberField K] [IsCMField K] [Field M] [NumberField M] [IsCMField M] [Field L] [NumberField L]
    [IsCMField L] [Algebra K M] [Algebra M L] [Algebra K L] [IsScalarTower K M L] (π : CuspSub K a) (P : CuspSub M a)
    (U : CuspSub L a), R K M π P → R M L P U → R K L π U

def TowerLift : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (a : ℕ), 1 ≤ a →
    ∀ (π : CuspSub E a) (S : Set (HeightOneSpectrum (𝓞 E))), (∀ u ∉ S, ∃ B, (CG.mk π).HasSat u B) →
    ∀ X : Fld E Ω, UnramifiedFromSplittingCriterion.Tower S X →
    ∃ P : CuspSub X.K a, IsLiftUnr π P ∧ (∀ c, Pol c π → Pol c P) ∧ ∀ R : Rel a, R.Tower → R E X.K π P

def BCLocal : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (a : ℕ), 1 ≤ a →
    ∀ (π : CuspSub E a) (ι : Type) [Finite ι]
    (v : ι → HeightOneSpectrum (𝓞 (maximalRealSubfield E))) (A : ι → ValuationSubring Ω), Function.Injective v →
    (∀ i, IsPlaceOver (A i) (v i)) → ∀ V : ∀ i, Subgroup (Dec (F := maximalRealSubfield E) (A i)),
    (∀ i, IsOpen (V i : Set (Dec (F := maximalRealSubfield E) (A i)))) →
    (∀ i, commutator (Dec (F := maximalRealSubfield E) (A i)) ≤ V i) →
    ∀ T : Set (HeightOneSpectrum (𝓞 (maximalRealSubfield E))), T.Finite → (∀ i, v i ∉ T) →
    ∀ N : Subgroup (G E Ω), IsOpen (N : Set (G E Ω)) →
    ∃ X : Fld E Ω, GlobalTheory.AboveL.SolvDisj X.K N ∧
      (∀ i (g : Dec (F := maximalRealSubfield E) (A i)),
        Fixes (maximalRealSubfield X.K) (g : G (maximalRealSubfield E) Ω) ↔ g ∈ V i) ∧
      (∀ t ∈ T, ∀ B : ValuationSubring Ω, IsPlaceOver B t → ∀ g ∈ Dec (F := maximalRealSubfield E) B,
        Fixes (maximalRealSubfield X.K) g) ∧
      ∃ P : CuspSub X.K a, IsLiftUnr π P ∧ (∀ c, Pol c π → Pol c P) ∧ ∀ R : Rel a, R.Tower → R E X.K π P

section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a l : ℕ} {π : CuspSub E a}

end

end UpperTheory.Gal.AbelianGaloisNormality
