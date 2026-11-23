import Formalism.LocalToGlobal.IndefiniteReal.DatumVec

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.IndefR.Datum
open scoped TensorProduct ComplexOrder

namespace Formalism.IndefR.Fin

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

abbrev latAll (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E))
    (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) : AddSubgroup (WO S T) :=
  latO S T ΛS ΛT fun _ => True

def PlaceLatDual (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D)
    (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)),
    IsSelfDualC S ΛS → IsSelfDualC T ΛT →
    (∀ e' : AE D, IsSplitIdem D e' → ∀ u ∈ latAll S T ΛS ΛT, u.map (fun a => e' * a) ∈ latAll S T ΛS ΛT) ∧
    (∀ e' : AE D, IsSplitIdem D e' → ∀ (g : GA D S) (h : GA D T), SuppAt e' S g → SuppAt e' T h →
      ∃ k : ℕ, 0 < k ∧ ∀ t ∈ latAll S T ΛS ΛT, k • actO S T g h t ∈ latAll S T ΛS ΛT) ∧
    ∀ (P : Finset (Formalism.L2.DIV.Pl D.host.E)) (e : AE D), IsIdemSum e P →
      (∀ y : WO S T, IsHalf (cA D e) y →
        ((∀ x ∈ latAll S T ΛS ΛT, IsHalf e x → ψ (symplO S T x y) = 1) ↔ y ∈ latAll S T ΛS ΛT)) ∧
      (∀ x : WO S T, IsHalf e x →
        ((∀ y ∈ latAll S T ΛS ΛT, IsHalf (cA D e) y → ψ (symplO S T x y) = 1) ↔ x ∈ latAll S T ΛS ΛT)) ∧
      (∀ k : ℕ, 0 < k → ∀ e₁ : AE D, (e₁ = e ∨ e₁ = cA D e) →
        ∃ R : Finset (WO S T), ∀ u ∈ latAll S T ΛS ΛT, IsHalf e₁ u →
          ∃ r ∈ R, ∃ v ∈ latAll S T ΛS ΛT, IsHalf e₁ v ∧ u = r + k • v) ∧
      ∀ e₁ : AE D, (e₁ = e ∨ e₁ = cA D e) → ∀ x : WO S T, IsHalf e₁ x → ∃ k : ℕ, 0 < k ∧ k • x ∈ latAll S T ΛS ΛT

def PlaceModelAt (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D)
    (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)),
    IsSelfDualC S ΛS → IsSelfDualC T ΛT →
    ∀ (P : Finset (Formalism.L2.DIV.Pl D.host.E)) (e : AE D), IsIdemSum e P →
    ∀ f₀ : WO S T → ℂ, IsThetaFunO ψ S T f₀ →
      (∀ u ∈ latAll S T ΛS ΛT, (IsHalf e u ∨ IsHalf (cA D e) u) → heisO ψ S T u f₀ = f₀) →
      ∀ e₁ : AE D, (e₁ = e ∨ e₁ = cA D e) →
        ∃ Tm, IsPlaceModel ψ (symplO S T) (heisO ψ S T) e₁ (latAll S T ΛS ΛT) 1 f₀ Tm ∧
          (∀ Tm', IsPlaceModel ψ (symplO S T) (heisO ψ S T) e₁ (latAll S T ΛS ΛT) 1 f₀ Tm' →
            ∀ Φ, IsSBHalf e₁ (latAll S T ΛS ΛT) Φ → Tm' Φ = Tm Φ) ∧
          (∀ Φ, IsSBHalf e₁ (latAll S T ΛS ΛT) Φ → IsThetaFunO ψ S T (Tm Φ)) ∧
          ∀ Φ, IsSBHalf e₁ (latAll S T ΛS ΛT) Φ → ∀ u : WO S T, (∀ i j, (e + cA D e) * u i j = 0) →
            heisO ψ S T u f₀ = f₀ → heisO ψ S T u (Tm Φ) = Tm Φ

def SplitLin (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle)
    (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om →
    ∀ (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)),
    IsSelfDualC S ΛS → IsSelfDualC T ΛT →
    ∀ (P : Finset (Formalism.L2.DIV.Pl D.host.E)) (e : AE D), IsIdemSum e P →
    ∀ f₀ : WO S T → ℂ, IsThetaFunO ψ S T f₀ →
    (∀ u ∈ latAll S T ΛS ΛT, (IsHalf e u ∨ IsHalf (cA D e) u) → heisO ψ S T u f₀ = f₀) →
    ∀ Tm, IsPlaceModel ψ (symplO S T) (heisO ψ S T) e (latAll S T ΛS ΛT) 1 f₀ Tm →
    ∀ e₁ : AE D, IsSplitIdem D e₁ → e₁ * e = e₁ →
    ∀ (g : GA D S) (h : GA D T), SuppAt e₁ S g → SuppAt e₁ T h →
    ∀ x y : (AE D)ˣ, IsDetAt e₁ S g x → IsDetAt e₁ T h y →
      ∃ r : ℝ, 0 < r ∧
        (∀ Φ, IsSBHalf e (latAll S T ΛS ΛT) Φ →
          om (g, h) (Tm Φ) = ((r : ℂ) * (splitFacO χS χT x y : ℂ)) • Tm (fun t => Φ (actO S T g⁻¹ h⁻¹ t))) ∧
        ((∀ t : WO S T, IsHalf e t → (actO S T g h t ∈ latAll S T ΛS ΛT ↔ t ∈ latAll S T ΛS ΛT)) →
          (∃ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsCovolOne (ratL T S) μ 𝓕 ∧ nrm2 μ 𝓕 f₀ = 1) → r = 1)

end Formalism.IndefR.Fin

end
