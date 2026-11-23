import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTameInertiaElementAtTwistPrime

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys

namespace GlobalTheory.IndefiniteRowSideFullHecke.ResidualBoundAdmissible

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂} (X : NTw D.R D.host D.what₂ D.LL0 N)

def OrdLE (i : X.Tw) (M : ℕ) (ι : Type) (n : ℕ) (F : abelian₂ X i M ι) : Prop :=
  ∀ G : MvPolynomial ι (X.O0 i), toLam X i M ι G = F →
    ∃ m : ι →₀ ℕ, m.degree ≤ n ∧ IsUnit (MvPolynomial.coeff m G)

def AdmPl (H : Subgroup (GE N)) (S : Finset (PlE D.host)) (P : PlE D.host) : Prop :=
  P ∉ S ∧ IsSplitPl D.host P ∧ DecV N P ≤ H

variable {X} (bkP : BKPh X)

def ResidualBoundOn (i : X.Tw) (Sg : Set (X.Sig i)) : Prop :=
  nu X i = 0 → (∀ s ∈ Sg, GalHyp bkP i s) →
    ∃ R : ℕ, ∀ M : ℕ, 4 * D.R.r * R + 1 < X.l i ^ M →
      ∀ (H : Subgroup (GE N)) (S : Finset (PlE D.host))
        (d : PlE D.host → (GE N →* Multiplicative (ZMod (X.l i ^ M)))), AdmFam X i M H S d →
      ∀ z : GE N, IsTameInertiaElementAtTwistPrime X i z →
      ∀ H' : Subgroup (GE N), IsOpen (H' : Set (GE N)) → H'.Normal →
      ∀ A : Finset (PlE D.host),
        ∃ (P : Fin R ⊕ Fin R → PlE D.host) (Q : Finset (PlE D.host)),
          (∀ q, AdmPl H S (P q)) ∧
          SlopeTestRemainingChoices X i M A P (fun q => d (P q)) ∧
          Steps X i M H' z P (fun q => d (P q)) ∧
          IsQ P Q ∧
          ∀ s ∈ Sg, ∀ (a : ℕ) (Φ : Matrix (Fin a) (Fin a) (abelian₂ X i M (Fin R ⊕ Fin R))),
            Computes bkP i s M (fun q => d (P q)) Q Φ →
              OrdLE X i M (Fin R ⊕ Fin R) (4 * D.R.r * R) Φ.det

def ResidualBound (i : X.Tw) : Prop := ResidualBoundOn bkP i {s | goodS bkP i s}

end GlobalTheory.IndefiniteRowSideFullHecke.ResidualBoundAdmissible

end
