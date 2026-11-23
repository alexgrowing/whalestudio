import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.FiniteDiscreteFamilies.FinCut

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.BcB.F.F5.Bo

def LocUniq : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) (V : Submodule ℂ (Sm E N)),
  IsDiscrete V → ∀ (w : HeightOneSpectrum (𝓞 E)) (σ σ' : SmIrr (GL (Fin N) (w.adicCompletion E))),
    IsLocCompGL V w σ → IsLocCompGL V w σ' →
      GlobalTheory.LocGL.IrrGL.of σ.ρ σ.smooth σ.irred = GlobalTheory.LocGL.IrrGL.of σ'.ρ σ'.smooth σ'.irred

def LocIso : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) (V V' : Submodule ℂ (Sm E N)),
  SpectralAccumulation.IsoV V V' → ∀ (w : HeightOneSpectrum (𝓞 E)) (σ : SmIrr (GL (Fin N) (w.adicCompletion E))),
    IsLocCompGL V w σ → IsLocCompGL V' w σ

def globL {E : Type} [Field E] [NumberField E] {N : ℕ} (Kf : ∀ w : HeightOneSpectrum (𝓞 E), Subgroup (GL (Fin N) (w.adicCompletion E))) :
    Subgroup (GL (Fin N) (Af E)) :=
  ⨅ w, (Kf w).comap (Matrix.GeneralLinearGroup.map (n := Fin N) (pLoc E w))

def GlobFix : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ)
  (Kf : ∀ w : HeightOneSpectrum (𝓞 E), Subgroup (GL (Fin N) (w.adicCompletion E))) (W : Submodule ℂ (Kinf E N → ℂ)),
  IsLevel Kf → (∀ᶠ w in Filter.cofinite, Kf w = GlobalTheory.LFun.KGL w N) → ∀ (V : Submodule ℂ (Sm E N)) (σ' : ∀ w : HeightOneSpectrum (𝓞 E), SmIrr (GL (Fin N) (w.adicCompletion E))),
    IsDiscrete V → (∀ w, IsLocCompGL V w (σ' w)) → (∀ w, GlobalTheory.LGrp.IsSpherical (σ' w).ρ (Kf w)) → HasKType W V →
      IsOpen (globL Kf : Set (GL (Fin N) (Af E))) ∧ SpectralAccumulation.HasType (globL Kf) W V

def FinIso : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) (K : Subgroup (GL (Fin N) (Af E)))
  (W : Submodule ℂ (Kinf E N → ℂ)) (m : (E →+* ℂ) → Multiset ℂ), IsOpen (K : Set (GL (Fin N) (Af E))) →
  FiniteDimensional ℂ W → ∃ V₀ : Finset (Submodule ℂ (Sm E N)), (∀ V ∈ V₀, IsDiscrete V) ∧
    ∀ V : Submodule ℂ (Sm E N), IsDiscrete V → SpectralAccumulation.HasType K W V → (∀ τ, HasInfCharGL V τ (m τ)) →
      ∃ V' ∈ V₀, SpectralAccumulation.IsoV V V'

def FinDiscNOf : Prop := LocUniq → LocIso → GlobFix → FinIso → FinDiscN

end PositivityTheory.Rg.BcB.F.F5.Bo

end
