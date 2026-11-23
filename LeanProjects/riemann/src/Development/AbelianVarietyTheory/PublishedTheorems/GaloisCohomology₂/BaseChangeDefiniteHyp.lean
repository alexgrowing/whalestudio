import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeIsobaric
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsDiscreteUOfIsDiscrete
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTheRecOfIsRec

noncomputable section

open NumberField IsDedekindDomain Matrix Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.CuspRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCWords GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.TheRec

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.BCWords

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n c : ℕ} {N : Fin c → ℕ}

def IsIsobaricComp (V : ∀ i, Submodule ℂ (Sm E (N i))) (w : HeightOneSpectrum (𝓞 E))
    (P : SmIrr (GL (Fin n) (w.adicCompletion E))) : Prop :=
  ∃ (A : ValuationSubring (AlgebraicClosure E)) (h : IsPlaceOver A w) (rc : IrrGL (w.adicCompletion E) → WD h)
    (σ : ∀ i, SmIrr (GL (Fin (N i)) (w.adicCompletion E))), IsTheRec h rc ∧ (∀ i, IsLocCompGL (V i) w (σ i)) ∧
    rc (IrrGL.of P.ρ P.smooth P.irred) = sumList (List.ofFn fun i => rc (IrrGL.of (σ i).ρ (σ i).smooth (σ i).irred))

structure IsIsobaricBaseChange (π : Submodule ℂ (UA E n → ℂ)) (h : ∑ i, N i = n) (V : ∀ i, Submodule ℂ (Sm E (N i))) : Prop where

  pos : ∀ i, 0 < N i

  discrete : ∀ i, IsDiscreteU (V i)

  csd : ∀ i, PairedGL (V i) (V i) GlobalTheory.ContraPair.conjOp

  unram : ∀ (w : HeightOneSpectrum (𝓞 E)) (P : SmIrr (GL (Fin n) (w.adicCompletion E))), IsIsobaricComp V w P →
    IsUnramU π w → GlobalTheory.LGrp.IsSpherical P.ρ (GlobalTheory.LFun.KGL w n) ∧ IsUnramBC π w P

  split : ∀ (w : HeightOneSpectrum (𝓞 E)) (P : SmIrr (GL (Fin n) (w.adicCompletion E))), IsIsobaricComp V w P →
    IsSplitAt w → IsCompAlong π (locU n w) ((cLoc w).comp (locU n w).subtype) P.ρ

  weight : ∃ W₁ W₂ : Submodule ℂ (Sm E n), IsInfSubquot h V W₁ W₂ ∧
    ∀ τ lam, HasWeightAt π τ lam → QuotHasInfChar W₁ W₂ τ (infOfWeight lam)

end GlobalTheory.BCWords

namespace GlobalTheory.Published

def BaseChangeDefiniteHyp : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E],
    (∀ w : HeightOneSpectrum (𝓞 E), Algebra.IsUnramifiedAt (𝓞 (maximalRealSubfield E)) w.asIdeal) →
    ∀ (p : ℕ), p.Prime → ∀ S : Set (HeightOneSpectrum (𝓞 (maximalRealSubfield E))), S.Finite →
    (∀ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 (maximalRealSubfield E)) ∈ S → IsSplitAt w) →
    (∀ v : HeightOneSpectrum (𝓞 (maximalRealSubfield E)), (p : 𝓞 (maximalRealSubfield E)) ∈ v.asIdeal → v ∈ S) →
    ∀ n : ℕ, 1 ≤ n → ∀ π : Submodule ℂ (UA E n → ℂ), IsAutRepU π →
      ∃ (c : ℕ) (N : Fin c → ℕ) (h : ∑ i, N i = n) (V : ∀ i, Submodule ℂ (Sm E (N i))), IsIsobaricBaseChange π h V

end GlobalTheory.Published

end
