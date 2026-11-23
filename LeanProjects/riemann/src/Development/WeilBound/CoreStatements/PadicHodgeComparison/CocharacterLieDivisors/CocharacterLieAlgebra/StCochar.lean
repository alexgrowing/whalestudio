import Development.WeilBound.CoreStatements.PadicHodgeComparison.CocharacterLieDivisors.StGalW

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp Polynomial
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.AutomorphicGaloisHodgeTate.Div

def HTCochar : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (l : ℕ) [Fact l.Prime] (N n : ℕ) (V : G E Ω →* GL (Fin N) (Qbar l)), Continuous V → HTLac V n →
    ∃ (K' : Type) (_ : Field K') (_ : IsAlgClosed K') (_ : Algebra (Qbar l) K')
      (P : Matrix (Fin N) (Fin N) K') (k : Fin N → ℤ) (e : Fin n → ℤ),
      IsUnit P.det ∧ Function.Injective e ∧ IsLac (fun i => ((e i : ℤ) : ℚ)) ∧ (∀ i, ∃ j, k j = e i) ∧
      ∀ f : MvPolynomial (Fin N × Fin N) (Qbar l),
        (∀ g : G E Ω, MvPolynomial.eval (fun p : Fin N × Fin N => (V g : Matrix (Fin N) (Fin N) (Qbar l)) p.1 p.2) f = 0) →
        ∀ t : K', t ≠ 0 →
          MvPolynomial.eval (fun p : Fin N × Fin N => (P * Matrix.diagonal (fun j => t ^ (k j)) * P⁻¹) p.1 p.2)
            (MvPolynomial.map (algebraMap (Qbar l) K') f) = 0

def CocharToLie : Prop := HTCochar → SenWLac

end PositivityTheory.AutomorphicGaloisHodgeTate.Div
