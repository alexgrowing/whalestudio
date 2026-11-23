import Development.WeilBound.RepresentationTheoryGL.HolomorphicDiscreteSeries.WeightOccurrence.OccSome
import Development.WeilBound.CoreStatements.BranchingTraces.BranchingComatrices.OneLeDiff

noncomputable section

open MeasureTheory Matrix Finset
open scoped InnerProductSpace ComplexConjugate

namespace PositivityTheory.RgHe.SM

open Formalism.REAL Formalism.MainNotions.S PositivityTheory.UnitaryDecomposition Formalism.FourierDecayAlt.P.CapelliAbstractCharacter CompanionTheory.D.DSIC

def wordSpan {V : Type} [AddCommGroup V] [Module ℂ V] {m : ℕ} (E : Fin m → Fin m → Module.End ℂ V) (L : ℕ) :
    Submodule ℂ (Module.End ℂ V) :=
  Submodule.span ℂ {T | ∃ w : List (Fin m × Fin m), w.length ≤ L ∧ T = (w.map fun p => E p.1 p.2).prod}

open Classical in

def ap {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {S : Submodule ℂ H} (T : Module.End ℂ S) (x : H) : H :=
  if hx : x ∈ S then (T ⟨x, hx⟩ : H) else 0

def phi {n : ℕ} {H H' : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [NormedAddCommGroup H'] [InnerProductSpace ℂ H']
    {S : Submodule ℂ H} (E : Fin (n + 1) → Fin (n + 1) → Module.End ℂ S) (e : Fin n ⊕ Unit ≃ Fin (n + 1)) (P : H →L[ℂ] H')
    (η : H) : Fin n → H' :=
  fun c => P (ap (E (e (Sum.inl c)) (zi e)) η)

def AlgId : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (N : ℕ) (E : Fin (N + 2) → Fin (N + 2) → Module.End ℂ V)
    (ι : Fin (N + 1) → Fin (N + 2)) (z : Fin (N + 2)), GlRel E → Function.Injective ι → (∀ a, ι a ≠ z) →
    ∀ (u : ℂ) (v : V), qdet E u v = qdet (fun a b => E (ι a) (ι b)) (u - 1) (Tm E u z z v) -
      ∑ c, Th (fun a b => E (ι a) (ι b)) (u - 1) (fun l => E (ι l) z (E z (ι c) v)) c

def ThMap : Prop :=
  ∀ (V V' : Type) [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V'] (N : ℕ)
    (E : Fin (N + 1) → Fin (N + 1) → Module.End ℂ V) (E' : Fin (N + 1) → Fin (N + 1) → Module.End ℂ V') (f : V →ₗ[ℂ] V'),
    (∀ a b x, f (E a b x) = E' a b (f x)) → ∀ (u : ℂ) (X : Fin (N + 1) → V) (x : Fin (N + 1)),
      f (Th E u X x) = Th E' u (fun l => f (X l)) x ∧ f (qdet E u (X x)) = qdet E' u (f (X x))

def KeyId : Prop :=
  ∀ (V V' : Type) [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V'] (N : ℕ)
    (E : Fin (N + 2) → Fin (N + 2) → Module.End ℂ V) (E' : Fin (N + 1) → Fin (N + 1) → Module.End ℂ V')
    (ι : Fin (N + 1) → Fin (N + 2)) (z : Fin (N + 2)) (f : V →ₗ[ℂ] V'), GlRel E → Function.Injective ι → (∀ a, ι a ≠ z) →
    (∀ a b x, f (E (ι a) (ι b) x) = E' a b (f x)) → ∀ (w cG : ℂ), (∀ x, qdet E (w + 1) x = cG • x) → (∀ y, qdet E' w y = 0) →
    ∀ v, cG • f v = -∑ c, Th E' w (fun l => f (E (ι l) z (E z (ι c) v))) c

def Grow : Prop :=
  ∀ (m : ℕ) (ε : Fin m → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Matrix (Fin m) (Fin m) ℂ → (H →L[ℂ] H)) (S : Submodule ℂ H) (E : Fin m → Fin m → Module.End ℂ S), 1 ≤ m → IsSmMod ε σ S E → IsURepOn (UJset ε) σ →
    ∀ (L : ℕ) (T : Module.End ℂ S), T ∈ wordSpan E L → ∀ v : S, ∃ C : ℝ, ∀ g : UJ ε,
      ‖ap T (σ (um g) v)‖ ≤ C * hs (um g) ^ L

def Zero : Prop :=
  ∀ (n : ℕ) (ε : Fin (n + 1) → Bool) (ε' : Fin n → Bool) (e : Fin n ⊕ Unit ≃ Fin (n + 1)) (H : Type) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (π : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ → (H →L[ℂ] H)) (S : Submodule ℂ H)
    (E : Fin (n + 1) → Fin (n + 1) → Module.End ℂ S), Fits ε ε' e → 1 ≤ n → IsSmMod ε π S E → IsURepOn (UJset ε) π → Dense (S : Set H) →
    ∀ (ν : Measure (UJ ε')), ν.IsHaarMeasure → ∀ (c : UJ ε' → ℂ) (L : ℕ) (C : ℝ), Continuous c →
    (∀ h, ‖c h‖ ≤ C * hs (um h) ^ (-((n : ℝ) ^ 2 + 1 + L))) →
    (∀ a b : H, ∫ h : UJ ε', c h * ⟪b, π (emb e (um h)) a⟫_ℂ ∂ν = 0) →
    ∀ T ∈ wordSpan E L, ∀ (η : S) (b : H), Integrable (fun h : UJ ε' => c h * ⟪b, ap T (π (emb e (um h)) η)⟫_ℂ) ν ∧
      ∫ h : UJ ε', c h * ⟪b, ap T (π (emb e (um h)) η)⟫_ℂ ∂ν = 0

def PhiEq : Prop :=
  ∀ (n : ℕ) (ε : Fin (n + 1) → Bool) (ε' : Fin n → Bool) (e : Fin n ⊕ Unit ≃ Fin (n + 1)) (H H' : Type)
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [NormedAddCommGroup H'] [InnerProductSpace ℂ H']
    (π : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ → (H →L[ℂ] H)) (σ : Matrix (Fin n) (Fin n) ℂ → (H' →L[ℂ] H'))
    (S : Submodule ℂ H) (E : Fin (n + 1) → Fin (n + 1) → Module.End ℂ S) (P : H →L[ℂ] H'), Fits ε ε' e → IsSmMod ε π S E → IsURepOn (UJset ε) π →
    Intertw ε' e π σ P → ∀ η ∈ S, phi E e P η ∈ SmT ε' σ ∧
      ∀ h : UJ ε', phi E e P (π (emb e (um h)) η) = actT σ (um h) (phi E e P η)

def Irr : Prop :=
  ∀ (m : ℕ) (ε : Fin m → Bool) (K : Type) [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    (σ : Matrix (Fin m) (Fin m) ℂ → (K →L[ℂ] K)), IsURepOn (UJset ε) σ → IsIrredOn (UJset ε) σ →
    ∀ u w : K, u ≠ 0 → w ≠ 0 → ∃ g : UJ ε, ⟪w, σ (um g) u⟫_ℂ ≠ 0

end PositivityTheory.RgHe.SM
