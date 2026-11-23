import Mathlib
import Formalism.PadicSubsetSums.CentralIdempotents.IsConstituent
import Formalism.PadicSubsetSums.CentralIdempotents.GaloisConjCentralIdempotent

open Formalism.IrreducibleCountingLemmas.TYPES CategoryTheory Polynomial
namespace PI.GreenHCLabel

variable (K : Type) [Field K] [Fintype K] [DecidableEq K]

def HCDisjoint : Prop :=
  ∀ (n s s' : ℕ) (b : Fin n → Fin s) (b' : Fin n → Fin s')
    (lam : ∀ c : Fin s, FDRep ℂ (GL {i // b i = c} K)) (lam' : ∀ c : Fin s', FDRep ℂ (GL {i // b' i = c} K)),
    Function.Surjective b → Function.Surjective b' →
    (∀ c, Simple (lam c) ∧ IsCuspidal K (lam c)) → (∀ c, Simple (lam' c) ∧ IsCuspidal K (lam' c)) →
    ∀ τ : FDRep ℂ (GL (Fin n) K), Simple τ → IsConstituent τ (hcRep K b lam) → IsConstituent τ (hcRep K b' lam') →
    ∃ (π : Fin s ≃ Fin s') (e : ∀ c, {i // b i = c} ≃ {i // b' i = π c}), ∀ c, Nonempty (transp (e c) (lam c) ≅ lam' (π c))

def LabelTransp (C : LabelConv K) : Prop :=
  ∀ (ι κ : Type) [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] (e : ι ≃ κ) (τ : FDRep ℂ (GL ι K)) (P : K[X]),
    HasCuspLabel C τ P ↔ HasCuspLabel C (transp e τ) P

def LabelIso (C : LabelConv K) : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (τ τ' : FDRep ℂ (GL ι K)) (P : K[X]),
    Nonempty (τ ≅ τ') → HasCuspLabel C τ P → HasCuspLabel C τ' P

def TranspKeeps : Prop :=
  ∀ (ι κ : Type) [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] (e : ι ≃ κ) (τ : FDRep ℂ (GL ι K)),
    (Simple τ → Simple (transp e τ)) ∧ (IsCuspidal K τ → IsCuspidal K (transp e τ))

def CuspLabelAny (C : LabelConv K) : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] [Nonempty ι] (τ : FDRep ℂ (GL ι K)), Simple τ → IsCuspidal K τ →
    ∃! P : K[X], HasCuspLabel C τ P

variable {K}

end PI.GreenHCLabel
