import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.LieSumDecompositions.SplitInv
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PIndMap

noncomputable section

open NumberField IsDedekindDomain
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs

namespace PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.BlockDerivatives

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def yp {a : ℕ} (k : Kinf E a) (g : GL (Fin a) (Af E)) : GA E a := infGL E a (Unitary.toUnits k) * finGL E a g

def lsF (r s : ℕ) (F : Sm E (r + s)) (k : Kinf E (r + s)) (g : GL (Fin (r + s)) (Af E)) : Set (Sm E r) :=
  {ℓ | ∃ m₂ : GA E s, ∀ m₁, ℓ.1 m₁ = F.1 (lev (Ad E) r s (m₁, m₂) * yp k g)}

def rsF (r s : ℕ) (F : Sm E (r + s)) (k : Kinf E (r + s)) (g : GL (Fin (r + s)) (Af E)) : Set (Sm E s) :=
  {ℓ | ∃ m₁ : GA E r, ∀ m₂, ℓ.1 m₂ = F.1 (lev (Ad E) r s (m₁, m₂) * yp k g)}

def LS {r s : ℕ} (U : Submodule ℂ (Sm E (r + s))) (T : Sm E (r + s) →ₗ[ℂ] Sm E (r + s)) : Submodule ℂ (Sm E r) :=
  Submodule.span ℂ {ℓ | ∃ ψ ∈ U, ∃ k g, ℓ ∈ lsF r s (T ψ) k g}

def RS {r s : ℕ} (U : Submodule ℂ (Sm E (r + s))) (T : Sm E (r + s) →ₗ[ℂ] Sm E (r + s)) : Submodule ℂ (Sm E s) :=
  Submodule.span ℂ {ℓ | ∃ ψ ∈ U, ∃ k g, ℓ ∈ rsF r s (T ψ) k g}

theorem lsF_sub_LS {r s : ℕ} {U : Submodule ℂ (Sm E (r + s))} {T : Sm E (r + s) →ₗ[ℂ] Sm E (r + s)} {ψ : Sm E (r + s)}
    (hψ : ψ ∈ U) (k : Kinf E (r + s)) (g : GL (Fin (r + s)) (Af E)) : lsF r s (T ψ) k g ⊆ LS U T :=
  fun _ h => Submodule.subset_span ⟨ψ, hψ, k, g, h⟩

theorem rsF_sub_RS {r s : ℕ} {U : Submodule ℂ (Sm E (r + s))} {T : Sm E (r + s) →ₗ[ℂ] Sm E (r + s)} {ψ : Sm E (r + s)}
    (hψ : ψ ∈ U) (k : Kinf E (r + s)) (g : GL (Fin (r + s)) (Af E)) : rsF r s (T ψ) k g ⊆ RS U T :=
  fun _ h => Submodule.subset_span ⟨ψ, hψ, k, g, h⟩

end PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.BlockDerivatives

end
