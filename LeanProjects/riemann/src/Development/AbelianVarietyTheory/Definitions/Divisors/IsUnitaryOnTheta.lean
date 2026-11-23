import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.DatumVec

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct Kronecker

namespace GlobalTheory.WeilParts

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def NonSplitAt (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)) (ε : AF D.host.F) : Prop :=
  IsPlaceIdem D v ε ∧ ¬ ∃ e : AE D, IsSplitIdem D e ∧ e + cA D e = algebraMap (AF D.host.F) (AE D) ε

def SuppPl (ε : AF D.host.F) (V : HSp D) (g : GA D V) : Prop :=
  ∀ i j, algebraMap (AF D.host.F) (AE D) ε * (Formalism.L2.Theta.mt V g - 1) i j = (Formalism.L2.Theta.mt V g - 1) i j

def UnramAt (ε : AF D.host.F) (χ : (AE D)ˣ →* Circle) : Prop :=
  ∀ x : (AE D)ˣ, algebraMap (AF D.host.F) (AE D) ε * ((x : AE D) - 1) = (x : AE D) - 1 →
    finPart D (x : AE D) ∈ intAE D → finPart D ((x⁻¹ : (AE D)ˣ) : AE D) ∈ intAE D → χ x = 1

def FixesVacAt (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E))
    (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ))
    (v : HeightOneSpectrum (𝓞 D.host.F)) (ε : AF D.host.F) : Prop :=
  ∀ g h, SuppPl ε S g → SuppPl ε T h →
    (∀ u, u ∈ (latO S T ΛS ΛT fun w => w = v) ↔ actO S T g h u ∈ (latO S T ΛS ΛT fun w => w = v)) →
    ∀ f, IsThetaFunO ψ S T f → (∀ u ∈ (latO S T ΛS ΛT fun w => w = v), heisO ψ S T u f = f) → om (g, h) f = f

def detPlus {m n : ℕ} (sS : Matrix (Fin n) (Fin n) ℂ) (sT : Matrix (Fin m) (Fin m) ℂ) (a' : Matrix (Fin n) (Fin n) ℂ)
    (b : Matrix (Fin m) (Fin m) ℂ) : ℂ :=
  ((1 / 2 : ℂ) • ((1 + sT ⊗ₖ sSᵀ) * (b ⊗ₖ a'ᵀ)) + (1 / 2 : ℂ) • (1 - sT ⊗ₖ sSᵀ)).det

def VacCharPlus (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D)
    (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) : Prop :=
  ∀ (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ),
    (∀ τ, IsCartanInv (gramAt D S τ) (sS τ)) → (∀ τ, IsCartanInv (gramAt D T τ) (sT τ)) →
    ∀ g ∈ GinfC S, ∀ h ∈ GinfC T,
      (∀ τ, sS τ * compAt θ τ (Formalism.L2.Theta.mt S g) = compAt θ τ (Formalism.L2.Theta.mt S g) * sS τ) →
      (∀ τ, sT τ * compAt θ τ (Formalism.L2.Theta.mt T h) = compAt θ τ (Formalism.L2.Theta.mt T h) * sT τ) →
      ∀ f, IsThetaFunO ψ S T f → (∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) f) →
        om (g, h) f = (∏ τ, detPlus (sS τ) (sT τ) (compAt θ τ (Formalism.L2.Theta.mt S g⁻¹)) (compAt θ τ (Formalism.L2.Theta.mt T h))) • f

structure IsUnitaryOnTheta (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D)
    (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) : Prop where
  pres : ∀ p f, IsThetaFunO ψ S T f → IsThetaFunO ψ S T (om p f)
  cont : ∀ f, IsThetaFunO ψ S T f → ∀ w, Continuous fun p : GA D S × GA D T => om p f w
  unit : ∀ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), μ.IsAddHaarMeasure →
    IsAddFundamentalDomain (ratL T S) 𝓕 μ → ∀ p f, IsThetaFunO ψ S T f →
      ∫⁻ w in 𝓕, ‖om p f w‖ₑ ^ 2 ∂μ = ∫⁻ w in 𝓕, ‖f w‖ₑ ^ 2 ∂μ

structure IsFinWeil (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E))
    (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (χS χT : (AE D)ˣ →* Circle)
    (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) : Prop extends IsUnitaryOnTheta ψ S T om where
  triv : ∀ g ∈ GinfC S, ∀ h ∈ GinfC T, ∀ f, IsThetaFunO ψ S T f → om (g, h) f = f
  Heisenberg₂ : ∀ g ∈ GfC S, ∀ h ∈ GfC T, ∀ w₀ f, IsThetaFunO ψ S T f →
    om (g, h) (heisO ψ S T w₀ f) = heisO ψ S T (actO S T g h w₀) (om (g, h) f)
  split : ∀ e, IsSplitIdem D e → ∀ g h, SuppAt e S g → SuppAt e T h → ∀ x y, IsDetAt e S g x → IsDetAt e T h y →
    ∃ r : ℝ, 0 < r ∧ ∀ ℓ : (WO S T → ℂ) →ₗ[ℂ] ℂ,
      (∀ u : WO S T, (∀ i j, cA D e * u i j = u i j) → ∀ f, IsThetaFunO ψ S T f → ℓ (heisO ψ S T u f) = ℓ f) →
      ∀ f, IsThetaFunO ψ S T f → ℓ (om (g, h) f) = (r : ℂ) * (splitFacO χS χT x y : ℂ) * ℓ f
  inert : ∀ v ε, NonSplitAt D v ε → FixesVacAt ψ S T ΛS ΛT om v ε

structure IsInfWeil (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D)
    (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) : Prop extends IsUnitaryOnTheta ψ S T om where
  triv : ∀ g ∈ GfC S, ∀ h ∈ GfC T, ∀ f, IsThetaFunO ψ S T f → om (g, h) f = f
  Heisenberg₂ : ∀ g ∈ GinfC S, ∀ h ∈ GinfC T, ∀ w₀ f, IsThetaFunO ψ S T f →
    om (g, h) (heisO ψ S T w₀ f) = heisO ψ S T (actO S T g h w₀) (om (g, h) f)
  vac : VacCharPlus ψ θ S T om

def IsEtaTilde (D : D7) (η : (AE D)ˣ →* Circle) : Prop :=
  IsHeckeChar D η ∧ UnramEverywhere D η ∧ ResEta D η 1 ∧ ∀ τ, HasInfExp D η τ (1 / 2)

end GlobalTheory.WeilParts

end
