import Formalism.GradedWeylDivisibility.StatementD

noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf.ShapeCovering

open MvPolynomial Formalism.GradedWeylDivisibility

def covY (K : Type) [Field K] (m : ℕ) (i : Fin (m + 1)) : MvPolynomial (Fin (m + 1) × Fin (m + 1)) K :=
  (-1) ^ (i : ℕ) * Matrix.det (fun a b : Fin m => (X (i.succAbove a, b.castSucc) : MvPolynomial _ K))

def FirstColumnPolynomialsSpan : Prop :=
  ∀ (K : Type) [Field K] (m P : ℕ) (F : MvPolynomial (Fin (m + 1) × Fin (m + 1)) K), 1 ≤ m →
    (F ∈ dualWeyl K (m + 1) (m + 1) (fun t => if t = 0 then P else 0) ↔
      ∃ f : MvPolynomial (Fin (m + 1)) K, f.IsHomogeneous P ∧ rename (fun i => (i, (0 : Fin (m + 1)))) f = F)

def SignedMinorPolynomialsSpan : Prop :=
  ∀ (K : Type) [Field K] (m Q : ℕ) (F : MvPolynomial (Fin (m + 1) × Fin (m + 1)) K), 1 ≤ m →
    (F ∈ dualWeyl K (m + 1) (m + 1) (fun t => if t = Fin.last m then 0 else Q) ↔
      ∃ f : MvPolynomial (Fin (m + 1)) K, f.IsHomogeneous Q ∧ aeval (covY K m) f = F)

def SignedMinorsAlgIndependent : Prop :=
  ∀ (K : Type) [Field K] (m : ℕ), 1 ≤ m → AlgebraicIndependent K (covY K m)

def IncidenceRelation : Prop :=
  ∀ (K : Type) [Field K] (m : ℕ), 1 ≤ m → ∑ i, X (i, (0 : Fin (m + 1))) * covY K m i = 0

def SignedMinorsCofactorTransform : Prop :=
  ∀ (K : Type) [Field K] (m : ℕ) (g : Matrix (Fin (m + 1)) (Fin (m + 1)) K) (i : Fin (m + 1)), IsUnit g.det →
    rowAct K g (covY K m i) = C g.det * ∑ j, C (g⁻¹ j i) * covY K m j

def CovL5adj : Prop :=
  ∀ (K : Type) [Field K] (m : ℕ) (g : Matrix (Fin (m + 1)) (Fin (m + 1)) K) (i : Fin (m + 1)),
    rowAct K g (covY K m i) = ∑ j, C (g.adjugate j i) * covY K m j

end Formalism.MainNotions.flipOneThree.Pf.ShapeCovering
