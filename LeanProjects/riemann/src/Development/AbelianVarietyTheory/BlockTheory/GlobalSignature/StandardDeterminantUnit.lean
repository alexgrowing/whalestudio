import Mathlib
import Formalism.LocalToGlobal.Columns.AbelianHostFieldConditions
import Formalism.LocalToGlobal.Columns.StdLatUnimodular
import Formalism.LocalToGlobal.Columns.DecoFin
import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth

open NumberField IsDedekindDomain

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.StandardDeterminantUnit

open Formalism.L2.Col

section Generic

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}
  {ST SG : Finset (HeightOneSpectrum (𝓞 E))}

def StdAtAll (d : DecoSet E n ST SG) : Prop :=
  ∀ P ∈ ST, d.1.at P = stdAt E n P

def DetUnitAt (d : DecoSet E n ST SG) (Q : HeightOneSpectrum (𝓞 E)) : Prop :=
  ∀ g : Sp E n ≃ₗ[E] Sp E n, (∀ x : Sp E n, g x ∈ d.1.at Q ↔ x ∈ stdAt E n Q) →
    Q.valuation E (LinearMap.det (g : Sp E n →ₗ[E] Sp E n)) = 1

def SplitNonConj (ST : Finset (HeightOneSpectrum (𝓞 E))) : Prop :=
  ∀ P ∈ ST, ∀ Q ∈ ST, Q ≠ conjPrime₂ P

variable (E n ST SG) in

def HasStdReps : Prop :=
  ∀ d : DecoSet E n ST SG, ∃ ga : UF E n, StdAtAll (((ga, 1) : UF E n × GLG E n SG) • d)

variable (E n ST SG) in

def StdDetUnit : Prop :=
  ∀ d : DecoSet E n ST SG, StdAtAll d → ∀ P ∈ ST, DetUnitAt d P ∧ DetUnitAt d (conjPrime₂ P)

end Generic

def Representatives : Prop :=
  ∀ (X : Fields), X.Ok → ∀ (Pr : Primes X), Pr.Ok → ∀ (u : Pr.Word) (n : ℕ) (SG : Finset (HeightOneSpectrum (𝓞 X.E)))
    (d : DecoSet X.E n (Pr.vT u) SG), ∃ ga : UF X.E n, ∀ P ∈ Pr.vT u,
      ((((ga, 1) : UF X.E n × GLG X.E n SG) • d).1.at P = stdAt X.E n P)

def RepresentativesDet : Prop :=
  ∀ (X : Fields), X.Ok → ∀ (Pr : Primes X), Pr.Ok → ∀ (u : Pr.Word) (n : ℕ) (SG : Finset (HeightOneSpectrum (𝓞 X.E))),
    StdDetUnit X.E n (Pr.vT u) SG

def RepresentativesSplit : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (n : ℕ) (ST SG : Finset (HeightOneSpectrum (𝓞 E))),
    SplitNonConj ST → HasStdReps E n ST SG

theorem splitNonConj_vT {X : Fields} {Pr : Primes X} (hPr : Pr.Ok) (u : Pr.Word) : SplitNonConj (Pr.vT u) := by
  intro P hP Q hQ h
  apply conj_piT_notMem hPr u ⟨Q, hQ⟩
  change cO X.E (Pr.piT u) ∈ Q.asIdeal
  rw [h, mem_conjP, cO_cO]
  exact decoFin_mem_of_mem_divs hP

theorem representatives_of_split (h : RepresentativesSplit) : Representatives :=
  fun X _ _ hPr u n SG d => h X.E n _ SG (splitNonConj_vT hPr u) d

end GlobalTheory.IndefiniteRowSideFullHecke.StandardDeterminantUnit
