import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SchurStep
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SatakeLifts.PairOfLiftAlt

noncomputable section

open NumberField IsDedekindDomain ValuativeRel Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.CuspRep
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.Gal.TP.Loc

def SatU {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} (U : Submodule ℂ (GlobalTheory.UnitaryBC.UA E n → ℂ))
    (w : HeightOneSpectrum (𝓞 E)) (B : Multiset ℂˣ) : Prop :=
  ∃ τ : SmIrr (GL (Fin n) (w.adicCompletion E)), UpperTheory.TP.CompAt U w τ ∧ HasSatGL w τ.ρ B

def CompUnit : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (U : Submodule ℂ (GlobalTheory.UnitaryBC.UA E n → ℂ)),
    GlobalTheory.UnitaryBC.IsAutRepU U → ∀ w, GlobalTheory.UnitaryBC.IsSplitAt w → ∀ τ : SmIrr (GL (Fin n) (w.adicCompletion E)),
      UpperTheory.TP.CompAt U w τ → IsUnitarisable τ.ρ

def PullGood : Prop :=
  ∀ (k k' : Type) [Field k] [TopologicalSpace k] [IsTopologicalRing k] [Field k'] [TopologicalSpace k'] [IsTopologicalRing k']
    (c : k →+* k'), Continuous c → Function.Surjective c → ∀ (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (GL (Fin n) k') V),
    (IsSmooth ρ → IsSmooth (ρ.comp (Matrix.GeneralLinearGroup.map c) : Representation ℂ (GL (Fin n) k) V)) ∧
    (ρ.IsIrreducible → Representation.IsIrreducible (ρ.comp (Matrix.GeneralLinearGroup.map c) : Representation ℂ (GL (Fin n) k) V)) ∧
    (IsUnitarisable ρ → IsUnitarisable (ρ.comp (Matrix.GeneralLinearGroup.map c) : Representation ℂ (GL (Fin n) k) V))

def PairSat : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n d : ℕ), 2 * n < d → ∀ (v : Pl (maximalRealSubfield E)) (t : E →ₐ[maximalRealSubfield E] Fv (maximalRealSubfield E) v)
    (χX χW : Chr (maximalRealSubfield E) E) (τ : SmIrr (GL (Fin n) ((splitPrime t).adicCompletion E)))
    (τ' : SmIrr (GL (Fin d) ((splitPrime t).adicCompletion E))), UpperTheory.TP.LocPair t χX χW τ τ' → IsUnitarisable τ.ρ →
    UnrAt χX (splitPrime t) → UnrAt χW (splitPrime t) → ∀ B : Multiset ℂˣ, HasSatGL (splitPrime t) τ.ρ B →
      HasSatGL (splitPrime t) τ'.ρ (B.map (· * (val χX (splitPrime t) * (val χW (splitPrime t))⁻¹)) +
        seg (splitPrime t) (val χX (splitPrime t)) (d - n))

def LiftSatU : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n d : ℕ), 2 * n < d → ∀ (Bs : Base (maximalRealSubfield E) E) (χX χW : Chr (maximalRealSubfield E) E)
    (mX mW : InfinitePlace (maximalRealSubfield E) → ℤ) (lam : InfinitePlace (maximalRealSubfield E) → Formalism.BasicNotions.DomWeight n)
    (U : Submodule ℂ (GlobalTheory.UnitaryBC.UA E n → ℂ)) (U' : Submodule ℂ (GlobalTheory.UnitaryBC.UA E d → ℂ)),
    GlobalTheory.UnitaryBC.IsAutRepU U → UpperTheory.TP.IsLift Bs χX χW mX mW lam U U' →
    ∀ w, GlobalTheory.UnitaryBC.IsSplitAt w → UnrAt χX w → UnrAt χW w → ∀ B : Multiset ℂˣ, SatU U w B →
      SatU U' w (B.map (· * (val χX w * (val χW w)⁻¹)) + seg w (val χX w) (d - n))

end UpperTheory.Gal.TP.Loc

end
