import Mathlib
import Development.WeilBound.CoreStatements.AutomorphicKernels.ResidualSpectrumHilbertSum.ResidualSpectrumTensors.LeviMaps
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSplitAtOfIsSplitPl

noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.Rs.C3.Fl

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E]

def wPart (N : ℕ) (w : HeightOneSpectrum (𝓞 E)) : GA E N →* GL (Fin N) (w.adicCompletion E) :=
  Matrix.GeneralLinearGroup.map ((pLoc E w).comp (pFin E))

abbrev iota (N : ℕ) (w : HeightOneSpectrum (𝓞 E)) : GL (Fin N) (w.adicCompletion E) →* GA E N :=
  (finGL E N).comp (locGL E N w)

def awayPart (N : ℕ) (w : HeightOneSpectrum (𝓞 E)) (g : GA E N) : GA E N :=
  g * (iota N w (wPart N w g))⁻¹

def fixedSub {G X : Type} [Group G] [AddCommGroup X] [Module ℂ X] (ρ : Representation ℂ G X) (C : Subgroup G) :
    Submodule ℂ X where
  carrier := {v | ∀ c ∈ C, ρ c v = v}
  add_mem' := fun {u v} hu hv c hc => by rw [map_add, hu c hc, hv c hc]
  zero_mem' := fun c _ => map_zero _
  smul_mem' := fun z v hv c hc => by rw [map_smul, hv c hc]

def rtw {c : ℕ} {n : Fin c → ℕ} (w : HeightOneSpectrum (𝓞 E)) (x : ∀ i, GL (Fin (n i)) (w.adicCompletion E))
    (t : (∀ i, GA E (n i)) → ℂ) : (∀ i, GA E (n i)) → ℂ :=
  fun m => t fun i => m i * iota (n i) w (x i)

end PositivityTheory.Rg.Rs.C3.Fl

end
