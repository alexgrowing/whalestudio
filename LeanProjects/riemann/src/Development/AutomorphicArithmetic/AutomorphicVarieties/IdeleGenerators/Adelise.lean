import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.WeightChange

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Base
open scoped Matrix

namespace UpperTheory.V.Sd

def Adelise : Prop :=
  ∀ (k N : ℕ) [NeZero N], 2 ≤ k → ∀ (χ : DirichletCharacter ℂ N) (g : Eigenform k N χ), ∃ (ω : HChar ℚ) (φ : TR.Sm ℚ 2),
    IsOfFinOrder ω ∧ (∀ w : Pl ℚ, ¬ normV w ∣ N → ω.UnrAt w ∧ ((ω.val w : ℂˣ) : ℂ) = χ (normV w : ZMod N)) ∧
    IsEigHol k (fun w => N.factorization (normV w)) ω φ (fun w => g.a (normV w)) ∧ TR.IsCuspForm φ

def PStab : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (w : Pl F) (V : Type) [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (GL (Fin 2) (w.adicCompletion F)) V) (x : V) (a b : ℂ), x ≠ 0 → x ∈ Hi.fixd ρ (K1 w 0) →
    Uop w ρ 0 x = (a + b) • x → (normV w : ℂ) • ρ (Matrix.GeneralLinearGroup.scalar (Fin 2) (atFin w (unif w))) x = (a * b) • x →
    b ≠ (normV w : ℂ) * a → HasU w ρ 1 a

end UpperTheory.V.Sd
