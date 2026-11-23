import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne
import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.LocalBaseChange.ExponentSeparationLemma.ExponentSeparation

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL ValuativeRel

namespace PositivityTheory.Lbc

def LiftExponent : Prop :=
  ∀ (Λ' Λ : Type) [CommGroup Λ'] [CommGroup Λ] (θ : Λ' ≃* Λ') (Nm : Λ' →* Λ), Nm.comp θ.toMonoidHom = Nm →
    ∀ (ι : Type) [Fintype ι] (W' : ι → Type) [∀ i, AddCommGroup (W' i)] [∀ i, Module ℂ (W' i)]
      [∀ i, FiniteDimensional ℂ (W' i)] (ρ' : ∀ i, Representation ℂ Λ' (W' i)) (A : ∀ i, W' i →ₗ[ℂ] W' i),
      (∀ i l, A i ∘ₗ ρ' i l = ρ' i (θ l) ∘ₗ A i) →
    ∀ (κ : Type) [Fintype κ] (W : κ → Type) [∀ j, AddCommGroup (W j)] [∀ j, Module ℂ (W j)]
      [∀ j, FiniteDimensional ℂ (W j)] (ρ : ∀ j, Representation ℂ Λ (W j)) (m : κ → ℝ), (∀ j, 0 ≤ m j) →
    ∀ (C : Submonoid Λ'), (∀ l : Λ', ∃ a ∈ C, ∃ b ∈ C, l = a * b⁻¹) → ∀ (l₀ : Λ') (c₀ : ℂ), c₀ ≠ 0 →
      (∀ c ∈ C, ∑ i, LinearMap.trace ℂ (W' i) (A i ∘ₗ ρ' i (l₀ * c)) =
        c₀ * ∑ j, (m j : ℂ) * LinearMap.trace ℂ (W j) (ρ j (Nm (l₀ * c)))) →
      ∀ ξ : Λ →* ℂ, (∃ j, 0 < m j ∧ genEig (ρ j) ξ ≠ ⊥) → ∃ i, genEig (ρ' i) (ξ.comp Nm) ≠ ⊥

def torusChar {k : Type} [Field k] {n : ℕ} (ξ : Fin n → (kˣ →* ℂˣ))
    (t : ∀ _ : Fin n, GL (Fin 1) k) : ℂ :=
  ∏ a, ((ξ a (Matrix.GeneralLinearGroup.det (t a)) : ℂˣ) : ℂ)

def SupportOfExponent : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (n : ℕ) (hd : ∑ _a : Fin n, 1 = n) (V : Type) [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin n) k) V), IsSmooth π → IsAdmissible π → π.IsIrreducible →
    ∀ (ξ : Fin n → (kˣ →* ℂˣ)) (hξ : ∀ a, IsSmoothChar (ξ a)),
    (∃ v : Jacquet π (unipRad k (stdBlocks (fun _ : Fin n => 1) hd)), v ≠ 0 ∧
      ∀ t : Levi k (fun _ : Fin n => Fin 1),
        v ∈ Module.End.maxGenEigenspace (jac (stdBlocks (fun _ : Fin n => 1) hd) π t) (torusChar ξ t)) →
    HasSupport π (Finset.univ.val.map fun a => IrrGL.ofChar (ξ a) (hξ a))

def GenericPrincipalSeries : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k]
    (n : ℕ) (ξ : Fin n → (kˣ →* ℂˣ)) (hξ : ∀ a, IsSmoothChar (ξ a)) (x : IrrGL k)
    (hd : ∑ a, (IrrGL.ofChar (ξ a) (hξ a)).1 = x.1),
    IsGeneric x.rep → HasSupport x.rep (Finset.univ.val.map fun a => IrrGL.ofChar (ξ a) (hξ a)) →
    (∀ a b, ξ a / ξ b ≠ absPow k 1) →
    Nonempty (x.rep.Equiv (prodIrr (fun a => IrrGL.ofChar (ξ a) (hξ a)) hd))

def UnitaryExponentBound : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (n : ℕ) (ξ : Fin n → (kˣ →* ℂˣ)) (hξ : ∀ a, IsSmoothChar (ξ a))
    (hd : ∑ a, (IrrGL.ofChar (ξ a) (hξ a)).1 = n),
    (prodIrr (fun a => IrrGL.ofChar (ξ a) (hξ a)) hd).IsIrreducible →
    IsUnitarisable (prodIrr (fun a => IrrGL.ofChar (ξ a) (hξ a)) hd) →
    IsGeneric (prodIrr (fun a => IrrGL.ofChar (ξ a) (hξ a)) hd) →
    ∀ a, ∃ s : ℝ, |s| < 1 / 2 ∧ ∀ x : kˣ, ‖((ξ a x : ℂˣ) : ℂ)‖ = ‖((absPow k (s : ℂ) x : ℂˣ) : ℂ)‖

def NormUnlinked : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (E : Type) [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
    (Nm : Eˣ →* Fˣ), (∀ x, absPow F 1 (Nm x) = absPow E 1 x) →
    ∀ (χ ψ : Fˣ →* ℂˣ) (s t : ℝ), |s| < 1 / 2 → |t| < 1 / 2 →
      (∀ x, ‖((χ x : ℂˣ) : ℂ)‖ = ‖((absPow F (s : ℂ) x : ℂˣ) : ℂ)‖) →
      (∀ x, ‖((ψ x : ℂˣ) : ℂ)‖ = ‖((absPow F (t : ℂ) x : ℂˣ) : ℂ)‖) →
      χ.comp Nm / ψ.comp Nm ≠ absPow E 1

def PinLift : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (E : Type) [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] [CharZero E]
    (Nm : Eˣ →* Fˣ), (∀ x, absPow F 1 (Nm x) = absPow E 1 x) →
    ∀ (n : ℕ) (ξ : Fin n → (Fˣ →* ℂˣ)) (hξ : ∀ a, IsSmoothChar (ξ a))
      (hξN : ∀ a, IsSmoothChar ((ξ a).comp Nm)) (hd : ∑ a, (IrrGL.ofChar (ξ a) (hξ a)).1 = n),
    (prodIrr (fun a => IrrGL.ofChar (ξ a) (hξ a)) hd).IsIrreducible →
    IsUnitarisable (prodIrr (fun a => IrrGL.ofChar (ξ a) (hξ a)) hd) →
    IsGeneric (prodIrr (fun a => IrrGL.ofChar (ξ a) (hξ a)) hd) →
    ∀ (x : IrrGL E) (hdE : ∑ a, (IrrGL.ofChar ((ξ a).comp Nm) (hξN a)).1 = x.1),
    IsGeneric x.rep → HasSupport x.rep (Finset.univ.val.map fun a => IrrGL.ofChar ((ξ a).comp Nm) (hξN a)) →
    Nonempty (x.rep.Equiv (prodIrr (fun a => IrrGL.ofChar ((ξ a).comp Nm) (hξN a)) hdE))

end PositivityTheory.Lbc

end
