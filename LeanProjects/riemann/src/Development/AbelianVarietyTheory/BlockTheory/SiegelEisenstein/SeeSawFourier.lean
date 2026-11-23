import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsQuasiFam
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SplitWeil GlobalTheory.FinPl ValuativeRel
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.IndefiniteRowSideFullHecke.SeeSawLineFourier

variable {D : D7}

def nrm (L : HSp D) (ζ : Fin L.rank → D.host.E) : D.host.E := star ζ ⬝ᵥ L.gram *ᵥ ζ

def colQ {m : ℕ} (ζ : Fin m → D.host.E) : Matrix (Fin m) (Fin 1) D.host.E := replicateCol (Fin 1) ζ

def beta (S : HSp D) {L L'' : HSp D} (ζ₁ : Fin L.rank → D.host.E) (ζ : Fin L''.rank → D.host.E) (x : WO L S) : WO S L'' :=
  (rat (colQ ζ) : Mx D L''.rank 1) ⬝
    (adj (incA D (nrm L'' ζ)⁻¹ • (x ⬝ (rat (colQ ζ₁) : Mx D L.rank 1) : Mx D S.rank 1)) ⬝ gA S : Mx D 1 S.rank)

def OppLines (L L'' : HSp D) (ζ₁ : Fin L.rank → D.host.E) (ζ : Fin L''.rank → D.host.E) : Prop :=
  IsLineVec L ζ₁ ∧ IsLineVec L'' ζ ∧ nrm L ζ₁ = -nrm L'' ζ

section Local

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def weilChar (p : SplitPt D k) (ψ : AddChar (AF D.host.F) ℂ) (a : k) : ℂ := psiE ψ (incA D D.host.xi0 * p.sec a)

variable {p : SplitPt D k} {S T : HSp D} {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']

def atW (α : Frame p S n') (β : Frame p T n) (x : Matrix n n' k) : WO S T :=
  Matrix.map (β.b ⬝ (x ⬝ α.b') : Matrix (Fin T.rank) (Fin S.rank) k) p.sec

def IsModel (ψ : AddChar (AF D.host.F) ℂ) (α : Frame p S n') (β : Frame p T n)
    (M : (Matrix n n' k → ℂ) →ₗ[ℂ] (WO S T → ℂ)) : Prop :=
  ∀ Φ ∈ SB (Matrix n n' k), IsThetaFunO ψ S T (M Φ) ∧
    (∀ a : Matrix n n' k, M (fun x => Φ (x + a)) = heisO ψ S T (atW α β a) (M Φ)) ∧
    ∀ a' : WO S T, IsHalf (cA D p.e) a' →
      M (fun x => ψ (symplO S T (atW α β x) a') * Φ x) = heisO ψ S T a' (M Φ)

def IsLineFrame {L : HSp D} (ζ : Fin L.rank → D.host.E) (α : Frame p L (Fin 1)) : Prop :=
  α.b = replicateCol (Fin 1) fun i => p.pr (ratV ζ i)

def ofCol (f : (n → k) → ℂ) (x : Matrix n (Fin 1) k) : ℂ := f fun i => x i 0

def ofRow (g : (n → k) → ℂ) (x : Matrix (Fin 1) n k) : ℂ := g (x 0)

variable [MeasurableSpace k] [BorelSpace k]

def hat (p : SplitPt D k) (ψ : AddChar (AF D.host.F) ℂ) (ν : Measure k) (f : (n → k) → ℂ) (η : n → k) : ℂ :=
  ∫ y, f y * weilChar p ψ (-(η ⬝ᵥ y)) ∂(Measure.pi fun _ => ν)

end Local

def LineFourier (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
  ∀ (S L L'' : HSp D) (ζ₁ : Fin L.rank → D.host.E) (ζ : Fin L''.rank → D.host.E), OppLines L L'' ζ₁ ζ →
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k]
    [BorelSpace k] (ν : Measure k), ν.IsAddHaarMeasure →
  ∀ (p : SplitPt D k) (n : Type) [Fintype n] [DecidableEq n] (b : Frame p S n) (a₁ : Frame p L (Fin 1))
    (a : Frame p L'' (Fin 1)), IsLineFrame ζ₁ a₁ → IsLineFrame ζ a →
  ∀ M₁ : (Matrix n (Fin 1) k → ℂ) →ₗ[ℂ] (WO L S → ℂ), IsModel ψ a₁ b M₁ →
    ∃ M₂ : (Matrix (Fin 1) n k → ℂ) →ₗ[ℂ] (WO S L'' → ℂ), IsModel ψ b a M₂ ∧
      ∀ f ∈ SB (n → k), hat p ψ ν f ∈ SB (n → k) ∧
        ∀ x : WO L S, M₂ (ofRow (hat p ψ ν f)) (beta S ζ₁ ζ x) = M₁ (ofCol f) x

def SeeSawFourier (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
  ∀ (V₀ A L S X T L'' : HSp D) (o : OrthDec V₀ A L) (o'' : OrthDec X T L'')
    (ζ₁ : Fin L.rank → D.host.E) (ζ : Fin L''.rank → D.host.E), OppLines L L'' ζ₁ ζ →
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k]
    [BorelSpace k] (ν : Measure k), ν.IsAddHaarMeasure →
  ∀ (p : SplitPt D k) (n nA nT : Type) [Fintype n] [DecidableEq n] [Fintype nA] [DecidableEq nA] [Fintype nT]
    [DecidableEq nT] (b : Frame p S n) (bA : Frame p A nA) (b₀ : Frame p V₀ (nA ⊕ Fin 1)) (bT : Frame p T nT)
    (bX : Frame p X (nT ⊕ Fin 1)), IsSumFrame o ζ₁ bA b₀ → IsSumFrame o'' ζ bT bX →
  ∀ (M₁ : (Matrix n (nA ⊕ Fin 1) k → ℂ) →ₗ[ℂ] (WO V₀ S → ℂ)) (M₂ : (Matrix nT n k → ℂ) →ₗ[ℂ] (WO S T → ℂ)),
    IsModel ψ b₀ b M₁ → IsModel ψ b bT M₂ →
    ∃ N : (Matrix n nA k → ℂ) →ₗ[ℂ] (Matrix (nT ⊕ Fin 1) n k → ℂ) →ₗ[ℂ] (WO A S × WO S X → ℂ),
      (∀ Θ ∈ SB (Matrix (nT ⊕ Fin 1) n k), ∀ w : WO S X,
        IsModel ψ bA b ((LinearMap.funLeft ℂ ℂ fun u : WO A S => (u, w)).comp (N.flip Θ))) ∧
      (∀ Ψ ∈ SB (Matrix n nA k), ∀ u : WO A S,
        IsModel ψ b bX ((LinearMap.funLeft ℂ ℂ fun w : WO S X => (u, w)).comp (N Ψ))) ∧
      ∀ f ∈ SB (n → k), hat p ψ ν f ∈ SB (n → k) ∧ ∀ Ψ ∈ SB (Matrix n nA k), ∀ Φ ∈ SB (Matrix nT n k),
        ∀ (u : WO A S) (x' : WO S T) (x : WO L S),
          N Ψ (tensRow Φ (hat p ψ ν f)) (u, (o''.resT S).symm (x', beta S ζ₁ ζ x)) =
            M₂ Φ x' * M₁ (tensCol Ψ f) ((o.resS S).symm (u, x))

section Checks

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {p : SplitPt D k}
  {S T : HSp D} {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']

end Checks

end GlobalTheory.IndefiniteRowSideFullHecke.SeeSawLineFourier

end
