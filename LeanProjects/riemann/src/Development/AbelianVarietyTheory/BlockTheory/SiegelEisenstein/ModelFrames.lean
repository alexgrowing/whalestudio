import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsQuasiFam
import Development.AbelianVarietyTheory.Definitions.Foundations.SimpleSum

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.FinPl GlobalTheory.SplitWeil
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.IndefiniteRowSideFullHecke.ModelFrames

variable {D : D7}

section Local

variable {k : Type} [Field k] {n n' : Type} {c : ℕ}

def rowMat (c p : ℕ) (u : n' → k) : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k :=
  fromBlocks 0 0 (Matrix.of fun l s => if l.val + 1 = p then u s else 0) 0

def scal (γ : kˣ) (κ : ℕ → k) (t₁ : kˣ) (i : ℕ) : k := (t₁ : k) * ∏ j ∈ Finset.range i, κ j * ((γ⁻¹ : kˣ) : k)

def coef (σ : ℕ) (a : k) (i : ℕ) : k := if i < σ then 1 else if i = σ then a else -1

variable [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']
variable [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k]

def opRow (χ : AddChar k Circle) (ν : Measure k) (p : ℕ) (Φ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ)
    (x : Matrix (n ⊕ Fin 1) n' k) : ℂ :=
  GlobalTheory.RootEx.opE χ ν p (fun y => Φ (y + rowMat c p (x (Sum.inr 0)))) (x.submatrix Sum.inl id)

end Local

def jacobiWittDecomposition {S S₀ : HSp D} {σ : ℕ} (d : HypDec S S₀ (σ + 1)) (i : Fin (2 * σ + 1 + 1)) : Fin S.rank → D.host.E :=
  fun r => if h : i.val < σ + 1 then d.e r ⟨i.val, h⟩ else d.e' r ⟨2 * σ + 1 - i.val, by omega⟩

def besselWittDecomposition {S S₀ : HSp D} {σ : ℕ} (d : HypDec S S₀ σ) (z : Fin S₀.rank → D.host.E) (i : Fin (2 * σ + 1)) :
    Fin S.rank → D.host.E :=
  fun r => if h : i.val < σ then d.e r ⟨i.val, h⟩ else if h' : i.val = σ then (d.i₀ *ᵥ z) r
    else d.e' r ⟨2 * σ - i.val, by omega⟩

def normZ {σ : ℕ} (B : BesLev D σ) : D.host.E := star B.ζ ⬝ᵥ B.L.gram *ᵥ B.ζ

section Frames

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {p : SplitPt D k}
variable {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']

def loc (p : SplitPt D k) (a : D.host.E) : k := p.pr (incA D a)

def up {S T : HSp D} (α : Frame p S n') (β : Frame p T n) (x : Matrix n n' k) : WO S T :=
  Matrix.map ((β.b * x : Matrix (Fin T.rank) n' k) * α.b' : Matrix (Fin T.rank) (Fin S.rank) k) p.sec

def IsModel (ψ : AddChar (AF D.host.F) ℂ) {S T : HSp D} (α : Frame p S n') (β : Frame p T n)
    (I : SB (Matrix n n' k) →ₗ[ℂ] (WO S T → ℂ)) : Prop :=
  (∀ Φ, IsThetaFunO ψ S T (I Φ)) ∧
  (∀ t : WO S T, IsHalf p.e t → ∀ Φ Φ' : SB (Matrix n n' k), (∀ x, Φ'.1 x = Φ.1 (x + rd α β t)) →
    I Φ' = heisO ψ S T t (I Φ)) ∧
  ∀ t : WO S T, IsHalf (cA D p.e) t → ∀ Φ Φ' : SB (Matrix n n' k),
    (∀ x, Φ'.1 x = ψ (symplO S T (up α β x) t) * Φ.1 x) → I Φ' = heisO ψ S T t (I Φ)

def IsNormalJac {σ : ℕ} (J : JacLev D (σ + 1)) (N : D.host.E) (γ t₁ : kˣ) (α₀ : Frame p J.W₀ n')
    (α : Frame p J.W (n' ⊕ Fin (2 * σ + 1 + 1))) : Prop :=
  (∀ r j, α.b r (Sum.inl j) = (J.d.j0.map p.pr * α₀.b : Matrix _ n' k) r j) ∧
    ∀ r i, α.b r (Sum.inr i) = scal γ (coef σ (loc p (-(D.host.xi0 * N)))) t₁ i.val * loc p (jacobiWittDecomposition J.d i r)

def IsNormalBes {σ : ℕ} (B : BesLev D σ) (γ t₁ : kˣ) (β₁ : Frame p B.A n) (β : Frame p B.V (n ⊕ Fin (2 * σ + 1))) : Prop :=
  (∀ r j, β.b r (Sum.inl j) = ((B.d.j0 * B.o.jA : Mx D _ _).map p.pr * β₁.b : Matrix _ n k) r j) ∧
    ∀ r i, β.b r (Sum.inr i) =
      scal γ (coef σ (loc p (-normZ B))) t₁ i.val * loc p (besselWittDecomposition B.d (vecB B.o B.ζ) i r)

def IsCoreFrame {σ : ℕ} (B : BesLev D σ) (γ t₁ : kˣ) (β₁ : Frame p B.A n) (β₀ : Frame p B.V₀ (n ⊕ Fin 1)) : Prop :=
  (∀ r j, β₀.b r (Sum.inl j) = (B.o.jA.map p.pr * β₁.b : Matrix _ n k) r j) ∧
    ∀ r, β₀.b r (Sum.inr 0) = scal γ (coef σ (loc p (-normZ B))) t₁ σ * loc p (vecB B.o B.ζ r)

end Frames

def FlatSplitFB (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (σ : ℕ) (J : JacLev D (σ + 1)) (B : BesLev D σ) (s : StepFB ψ J B)
    (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k]
    [BorelSpace k] (p : SplitPt D k) (χ : AddChar k Circle) (γ t₁ : kˣ) (ν : Measure k), ν.IsAddHaarMeasure →
    (∀ a, (χ a : ℂ) = psiE ψ (p.sec ((γ : k) * a))) →
    ∀ (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']
      (α₀ : Frame p J.W₀ n') (α : Frame p J.W (n' ⊕ Fin (2 * σ + 1 + 1)))
      (β₁ : Frame p B.A n) (β₀ : Frame p B.V₀ (n ⊕ Fin 1)) (β : Frame p B.V (n ⊕ Fin (2 * σ + 1))),
      IsNormalJac J (normZ B) γ t₁ α₀ α → IsNormalBes B γ t₁ β₁ β → IsCoreFrame B γ t₁ β₁ β₀ →
      ∀ I : SB (Matrix (n ⊕ Fin (2 * σ + 1)) (n' ⊕ Fin (2 * σ + 1 + 1)) k) →ₗ[ℂ] (WO J.W B.V → ℂ), IsModel ψ α β I →
        ∃ I₀ : SB (Matrix (n ⊕ Fin 1) n' k) →ₗ[ℂ] (WO J.W₀ B.V₀ → ℂ), IsModel ψ α₀ β₀ I₀ ∧
          ∀ Φ, ∃ h : opRow χ ν (σ + 1) Φ.1 ∈ SB (Matrix (n ⊕ Fin 1) n' k), flatFB s (I Φ) = I₀ ⟨_, h⟩

example {k : Type} [Field k] (γ t₁ : kˣ) (κ : ℕ → k) (i : ℕ) : (γ : k) * scal γ κ t₁ (i + 1) = κ i * scal γ κ t₁ i := by
  simp only [scal, Finset.prod_range_succ, Units.val_inv_eq_inv_val]
  field_simp

example {k : Type} [Field k] (a : k) : (scal 1 (coef 1 a) 1 0, scal 1 (coef 1 a) 1 1, scal 1 (coef 1 a) 1 2,
    scal 1 (coef 1 a) 1 3) = (1, 1, a, -a) := by
  simp [scal, coef, Finset.prod_range_succ]

end GlobalTheory.IndefiniteRowSideFullHecke.ModelFrames

end
