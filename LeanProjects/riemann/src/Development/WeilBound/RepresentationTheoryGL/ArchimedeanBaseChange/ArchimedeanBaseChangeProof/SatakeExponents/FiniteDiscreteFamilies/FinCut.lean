import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.FiniteDiscreteFamilies.RunFinOf

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC
open PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.One PositivityTheory.Rg.Rs

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.BcB.F.F5

def LevelFactor : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : HeightOneSpectrum (𝓞 E)) (c n : ℕ)
  (N : Fin c → ℕ) (h : ∑ i, N i = n) (K : Subgroup (GL (Fin n) (w.adicCompletion E))),
  IsOpen (K : Set (GL (Fin n) (w.adicCompletion E))) →
  ∃ Ki : ∀ i, Subgroup (GL (Fin (N i)) (w.adicCompletion E)),
    (∀ i, IsOpen (Ki i : Set (GL (Fin (N i)) (w.adicCompletion E)))) ∧
    (GlobalTheory.LFun.KGL w n ≤ K → ∀ i, GlobalTheory.LFun.KGL w (N i) ≤ Ki i) ∧
    ∀ σ : ∀ i, SmIrr (GL (Fin (N i)) (w.adicCompletion E)), GlobalTheory.LGrp.IsSpherical (locProd h w σ) K →
      ∀ i, GlobalTheory.LGrp.IsSpherical (σ i).ρ (Ki i)

def FinDiscN : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ)
  (Kf : ∀ w : HeightOneSpectrum (𝓞 E), Subgroup (GL (Fin N) (w.adicCompletion E))) (W : Submodule ℂ (Kinf E N → ℂ))
  (m : (E →+* ℂ) → Multiset ℂ), IsLevel Kf → FiniteDimensional ℂ W →
  ∃ (k : ℕ) (σ : Fin k → ∀ w : HeightOneSpectrum (𝓞 E), SmIrr (GL (Fin N) (w.adicCompletion E))),
    ∀ (V : Submodule ℂ (Sm E N)) (σ' : ∀ w : HeightOneSpectrum (𝓞 E), SmIrr (GL (Fin N) (w.adicCompletion E))),
      IsDiscrete V → (∀ w, IsLocCompGL V w (σ' w)) → (∀ τ, HasInfCharGL V τ (m τ)) →
      (∀ w, GlobalTheory.LGrp.IsSpherical (σ' w).ρ (Kf w)) → HasKType W V →
      ∃ j, ∀ w, GlobalTheory.LocGL.IrrGL.of (σ j w).ρ (σ j w).smooth (σ j w).irred =
        GlobalTheory.LocGL.IrrGL.of (σ' w).ρ (σ' w).smooth (σ' w).irred

def FinFamOf : Prop := LevelFactor → FinDiscN → FinFam

end PositivityTheory.Rg.BcB.F.F5

end
