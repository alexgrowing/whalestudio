import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.BernsteinExponentBounds.IsInvForm
import Development.WeilBound.CoreStatements.AutomorphicKernels.BernsteinUnitaryProducts.IrreducibleAdmissibleReps.Assembly

noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib

namespace PositivityTheory.RgUd.Prod

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

abbrev sc (n : ℕ) (x : kˣ) : GL (Fin n) k := GeneralLinearGroup.scalar (Fin n) x

def LFin {n : ℕ} (A : GRep k n) : Prop :=
  ∀ a : A.V, ∃ U : Submodule ℂ A.V, FiniteDimensional ℂ U ∧ a ∈ U ∧ ∀ (x : kˣ), ∀ u ∈ U, A.ρ (sc n x) u ∈ U

def IsTopD (ψ : AddChar k Circle) {n h : ℕ} (π : GRep k (n + h)) : Prop :=
  Nontrivial (derivB ψ h π).V ∧ ∀ (n' h' : ℕ) (e : n + h = n' + h'), h < h' → Subsingleton (derivB ψ h' (π.cast e)).V

variable (k)

def LFDeriv : Prop :=
  ∀ (ψ : AddChar k Circle), Continuous ψ → ∀ (n j : ℕ) (π : GRep k (n + j)), IsSmooth π.ρ → IsAdmissible π.ρ →
    LFin (derivB ψ j π)

def CentralSub : Prop :=
  ∀ (n : ℕ) (A : GRep k n), IsSmooth A.ρ → LFin A → ∀ (x : kˣ) (c : ℂ) (a : A.V), a ≠ 0 → A.ρ (sc n x) a = c • a →
    ∃ (W : Subrepresentation A.ρ) (ω : kˣ →* ℂˣ), W ≠ ⊥ ∧ HasCentralChar W.toRepresentation ω ∧ (ω x : ℂ) = c

def EigProd : Prop :=
  ∀ (r t : ℕ) (A : GRep k r) (B : GRep k t), IsSmooth A.ρ → IsSmooth B.ρ → LFin A → LFin B →
    ∀ (x : kˣ) (c : ℂ) (f : (A.prod B).V), f ≠ 0 → (A.prod B).ρ (sc (r + t) x) f = c • f →
      ∃ (cA cB : ℂ), c = cA * cB ∧ (∃ a : A.V, a ≠ 0 ∧ A.ρ (sc r x) a = cA • a) ∧
        ∃ b : B.V, b ≠ 0 ∧ B.ρ (sc t x) b = cB • b

def EigFilt : Prop :=
  ∀ (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin n) k) V) (ℓ : ℕ)
    (F : ℕ → Subrepresentation ρ), Antitone F → F 0 = ⊤ → F (ℓ + 1) = ⊥ → ∀ (x : kˣ) (c : ℂ) (v : V), v ≠ 0 →
      ρ (sc n x) v = c • v → ∃ i ≤ ℓ, ∃ w : (F i).toSubmodule ⧸ Submodule.comap (F i).toSubmodule.subtype (F (i + 1)).toSubmodule, w ≠ 0 ∧
        (subQuot (F i) (F (i + 1))) (sc n x) w = c • w

def PosProdD : Prop :=
  ∀ (ψ : AddChar k Circle), Continuous ψ → ψ ≠ 1 → ∀ (r t : ℕ) (π₁ : GRep k r) (π₂ : GRep k t),
    IsSmooth π₁.ρ → π₁.ρ.IsIrreducible → IsUnitarisable π₁.ρ → IsSmooth π₂.ρ → π₂.ρ.IsIrreducible →
    IsUnitarisable π₂.ρ → ∀ (n h : ℕ) (e : r + t = n + h), IsTopD ψ ((π₁.prod π₂).cast e) →
      ∀ (n' j : ℕ) (e' : r + t = n' + j), j < h → ∀ x : kˣ, nabs k x < 1 → ∀ (v : (derivB ψ j ((π₁.prod π₂).cast e')).V)
        (c : ℂ), v ≠ 0 → (derivB ψ j ((π₁.prod π₂).cast e')).ρ (sc n' x) v = c • v →
        ‖c‖ < nabs k x ^ ((n' : ℝ) * ((j : ℝ) - 1) / 2)

def TopProdD : Prop :=
  ∀ (ψ : AddChar k Circle), Continuous ψ → ψ ≠ 1 → ∀ (r t : ℕ) (π₁ : GRep k r) (π₂ : GRep k t),
    IsSmooth π₁.ρ → π₁.ρ.IsIrreducible → IsUnitarisable π₁.ρ → IsSmooth π₂.ρ → π₂.ρ.IsIrreducible →
    IsUnitarisable π₂.ρ → 0 < r + t →
    ∃ (n h : ℕ) (e : r + t = n + h), 0 < h ∧ IsTopD ψ ((π₁.prod π₂).cast e) ∧
      ∃ (r' t' : ℕ) (e₂ : r' + t' = n) (σ₁ : GRep k r') (σ₂ : GRep k t') (χ : GL (Fin n) k →* ℂˣ),
        IsSmooth σ₁.ρ ∧ σ₁.ρ.IsIrreducible ∧ IsUnitarisable σ₁.ρ ∧ IsSmooth σ₂.ρ ∧ σ₂.ρ.IsIrreducible ∧
        IsUnitarisable σ₂.ρ ∧ Nonempty ((derivB ψ h ((π₁.prod π₂).cast e)).ρ.Equiv (twist ((σ₁.prod σ₂).cast e₂).ρ χ))

end PositivityTheory.RgUd.Prod
