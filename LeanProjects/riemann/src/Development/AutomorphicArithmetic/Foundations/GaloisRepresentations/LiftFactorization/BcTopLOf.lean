import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LiftFactorization.RamLiftOf

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp GlobalTheory.GalCut GlobalTheory.RealGal GlobalTheory.UnitaryBC UpperTheory.V.Published UpperTheory.Gal.UnramifiedFromSplittingCriterion UpperTheory.ConvolutionTheory.Sph

namespace UpperTheory.Gal.AbelianGaloisNormality

def Ab (F Ω M : Type) [Field F] [Field Ω] [Algebra F Ω] [Field M] [Algebra M Ω] : Prop :=
  ∀ g h : G F Ω, Fixes M (g * h * g⁻¹ * h⁻¹)

def SqFix (Ω Y M : Type) [Field Ω] [Field Y] [Algebra Y Ω] [Field M] [Algebra M Ω] : Prop :=
  ∃ (x : Ω) (n : ℤ), x ^ 2 = (n : Ω) ∧ ∀ (F : Type) [Field F] [Algebra F Ω] (g : G F Ω), Fixes Y g → g x = x → Fixes M g

def Three {E : Type} [Field E] [NumberField E] (M : Type) [Field M] [NumberField M] [IsCMField M] [Algebra E M]
    (t : HeightOneSpectrum (𝓞 E)) : Prop :=
  ∃ w₁ w₂ w₃ : HeightOneSpectrum (𝓞 M), w₁.under (𝓞 E) = t ∧ w₂.under (𝓞 E) = t ∧ w₃.under (𝓞 E) = t ∧
    GlobalTheory.Cong.Apart w₁ w₂ ∧ GlobalTheory.Cong.Apart w₁ w₃ ∧ GlobalTheory.Cong.Apart w₂ w₃

def BCTop : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ), l.Prime →
    ∀ a : ℕ, 1 ≤ a → ∀ (π : CuspSub E a) (Z : Set (HeightOneSpectrum (𝓞 E))), Z.Finite →
    ∀ N : Subgroup (G E Ω), IsOpen (N : Set (G E Ω)) →
    ∃ (M : Type) (_ : Field M) (_ : NumberField M) (_ : IsCMField M) (_ : Algebra M Ω) (_ : IsAlgClosure M Ω)
      (_ : Algebra E M) (_ : IsScalarTower E M Ω), Layers Ω E M ∧
      (∀ (F : Type) [Field F] [Algebra F Ω], Ab F Ω E → Ab F Ω M) ∧ GlobalTheory.AboveL.SolvDisj M N ∧
      Spl Ω M (Z ∪ {t | ((l : ℕ) : 𝓞 E) ∈ t.asIdeal}) ∧ SplTop M Z ∧ FieldOK l M ∧
      (∀ t ∈ Z ∪ {t | ((l : ℕ) : 𝓞 E) ∈ t.asIdeal}, Three M t) ∧
      ∃ P : CuspSub M a, IsLiftUnr π P ∧ (∀ c, Pol c π → Pol c P) ∧ GlobalTheory.GalCut.Good l P ∧ ∀ R : Rel a, R.Tower → R E M π P

def BCTopL : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ), l.Prime →
    ∀ a : ℕ, 1 ≤ a → ∀ (π : CuspSub E a) (Z : Set (HeightOneSpectrum (𝓞 E))), Z.Finite →
    ∀ N : Subgroup (G E Ω), IsOpen (N : Set (G E Ω)) →
    ∃ (M : Type) (_ : Field M) (_ : NumberField M) (_ : IsCMField M) (_ : Algebra M Ω) (_ : IsAlgClosure M Ω)
      (_ : Algebra E M) (_ : IsScalarTower E M Ω), GlobalTheory.AboveL.SolvDisj M N ∧
      Spl Ω M (Z ∪ {t | ((l : ℕ) : 𝓞 E) ∈ t.asIdeal}) ∧ SplTop M Z ∧ FieldOK l M ∧
      (∀ t ∈ Z ∪ {t | ((l : ℕ) : 𝓞 E) ∈ t.asIdeal}, Three M t) ∧
      ∃ P : CuspSub M a, IsLift π P ∧ (∀ c, Pol c π → Pol c P) ∧ GlobalTheory.GalCut.Good l P

def Quad1Sq : Prop :=
  ∀ (E Y Ω : Type) [Field E] [NumberField E] [Field Y] [NumberField Y] [IsCMField Y] [Field Ω] [Algebra E Y] [Algebra Y Ω]
    [IsAlgClosure Y Ω] (δ : Y), RealStep E Ω δ → ∀ T : Set (HeightOneSpectrum (𝓞 Y)), T.Finite →
    ∃ Q : QCM Y Ω, Step1 T Q ∧ SqFix Ω Y ↥Q.K

def Step0Sq : Prop :=
  ∀ (E Y Ω : Type) [Field E] [Field Y] [Field Ω] [Algebra E Y] [Algebra E Ω] [Algebra Y Ω] [IsScalarTower E Y Ω] (δ : Y),
    RealStep E Ω δ → SqFix Ω E Y

def AbStep : Prop :=
  ∀ (F Ω Y M : Type) [Field F] [Field Ω] [Algebra F Ω] [Field Y] [Algebra Y Ω] [Field M] [Algebra M Ω], SqFix Ω Y M →
    Ab F Ω Y → Ab F Ω M

def AbGal : Prop :=
  ∀ (E Ω M : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] [Field M] [NumberField M] [Algebra M Ω]
    [Algebra E M] [IsScalarTower E M Ω], Ab E Ω M → IsAbelianGalois E M ∧ IsSolvable (M ≃ₐ[E] M)

def SatAll (a : ℕ) : Rel a := fun K M _ _ _ _ _ _ _ π P =>
  ∀ (w : HeightOneSpectrum (𝓞 M)) (f : ℕ) (B : Multiset ℂˣ), normV w = normV (w.under (𝓞 K)) ^ f →
    (CG.mk π).HasSat (w.under (𝓞 K)) B → (CG.mk P).HasSat w (B.map (· ^ f))

def SatTower : Prop := RamSph → ∀ a : ℕ, 1 ≤ a → (SatAll a).Tower

end UpperTheory.Gal.AbelianGaloisNormality
