import Mathlib
import Development.WeilBound.CoreStatements.AutomorphicKernels.ResidualSpectrumHilbertSum.ResidualSpectrumTensors.Development

noncomputable section

open NumberField IsDedekindDomain
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.RSHS.LeviInductionForms

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {N : ℕ}

def LocMaps (I : Submodule ℂ (Sm E N)) (w : HeightOneSpectrum (𝓞 E)) {X : Type} [AddCommGroup X] [Module ℂ X]
    (ρ : Representation ℂ (GL (Fin N) (w.adicCompletion E)) X) : Type :=
  {F : X →ₗ[ℂ] Sm E N // (∀ v, F v ∈ I) ∧ ∀ g v, F (ρ g v) = finRep E N (locGL E N w g) (F v)}

def LeviMaps {c : ℕ} {n : Fin c → ℕ} (T : Submodule ℂ ((∀ i, GA E (n i)) → ℂ)) (w : HeightOneSpectrum (𝓞 E))
    {X : Type} [AddCommGroup X] [Module ℂ X]
    (ρ : Representation ℂ (∀ i, GL (Fin (n i)) (w.adicCompletion E)) X) : Type :=
  {Φ : X →ₗ[ℂ] ((∀ i, GA E (n i)) → ℂ) // (∀ v, Φ v ∈ T) ∧
    ∀ g v, Φ (ρ g v) = fun m => Φ v fun i => m i * finGL E (n i) (locGL E (n i) w (g i))}

end PositivityTheory.RSHS.LeviInductionForms

end
