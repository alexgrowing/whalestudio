import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
import Development.AbelianVarietyTheory.Definitions.Foundations.SimpleSum

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.FinPl GlobalTheory.SplitWeil ValuativeRel
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.IndefiniteRowSideFullHecke.WeightedNormColumns

section Scalars

variable {k : Type} [Field k]

def kaSrc (ρ : ℕ) (N : k) (i : ℕ) : k := if i < ρ then 1 else if i = ρ then -N else -1

def kaTgt (ρ : ℕ) (cst : k) (i : ℕ) : k := if i + 1 < ρ then 1 else if i + 1 = ρ then cst else -1

def IsNormalScal (ξ : k) (κ : ℕ → k) {c : ℕ} (t : Fin c → k) : Prop :=
  ∀ i j : Fin c, j.val = i.val + 1 → t j = ξ⁻¹ * κ i.val * t i

end Scalars

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def xiW (p : SplitPt D k) : k := p.pr (incA D D.host.xi0)

def IsWeilChar (p : SplitPt D k) (ψ : AddChar (AF D.host.F) ℂ) (χ : AddChar k Circle) : Prop :=
  ∀ a, (χ a : ℂ) = psiE ψ (p.sec (xiW p * a))

def normW (p : SplitPt D k) {ρ : ℕ} (B : BesLev D ρ) : k := p.pr (incA D (star B.ζ ⬝ᵥ B.L.gram *ᵥ B.ζ))

def srcVec (p : SplitPt D k) {ρ : ℕ} (B : BesLev D ρ) (s : Fin (2 * ρ + 1)) (r : Fin B.V.rank) : k :=
  if h : s.val < ρ then p.pr (B.d.jX r ⟨s.val, h⟩)
  else if h' : s.val = ρ then p.pr ((B.d.j0 *ᵥ ratV (vecB B.o B.ζ)) r)
  else p.pr (B.d.jY r ⟨2 * ρ - s.val, by have := s.2; omega⟩)

def tgtVec (p : SplitPt D k) {ρ : ℕ} (J : JacLev D ρ) (s : Fin (2 * ρ)) (r : Fin J.W.rank) : k :=
  if h : s.val < ρ then p.pr (J.d.jX r ⟨s.val, h⟩)
  else (xiW p)⁻¹ * p.pr (J.d.jY r ⟨2 * ρ - 1 - s.val, by have := s.2; omega⟩)

variable {p : SplitPt D k} {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']

def NormalBF {ρ : ℕ} (B : BesLev D ρ) (J : JacLev D ρ) (αA : Frame p B.A n') (β₀ : Frame p J.W₀ n)
    (α : Frame p B.V (n' ⊕ Fin (2 * ρ + 1))) (β : Frame p J.W (n ⊕ Fin (2 * ρ))) : Prop :=
  ∃ (t' : Fin (2 * ρ + 1) → k) (t : Fin (2 * ρ) → k),
    IsNormalScal (xiW p) (kaSrc ρ (normW p B)) t' ∧ IsNormalScal (xiW p) (kaTgt ρ (normW p B)) t ∧
    t' ⟨ρ, by omega⟩ = 1 ∧ (∀ i : Fin (2 * ρ), i.val = 0 → t i = t' 0) ∧
    α.b = fromCols ((B.d.j0 * B.o.jA).map p.pr * αA.b) (Matrix.of fun r s => t' s * srcVec p B s r) ∧
    β.b = fromCols (J.d.j0.map p.pr * β₀.b) (Matrix.of fun r s => t s * tgtVec p J s r)

def IsModel (ψ : AddChar (AF D.host.F) ℂ) {S T : HSp D} {m m' : Type} [Fintype m] [DecidableEq m] [Fintype m']
    [DecidableEq m'] (α : Frame p S m') (β : Frame p T m) (M : SB (Matrix m m' k) →ₗ[ℂ] (WO S T → ℂ)) : Prop :=
  (∀ Φ, IsThetaFunO ψ S T (M Φ)) ∧
  (∀ x : WO S T, IsHalf p.e x → ∀ Φ Φ' : SB (Matrix m m' k),
    (∀ u, Φ'.1 u = Φ.1 (u + rd α β x)) → M Φ' = heisO ψ S T x (M Φ)) ∧
  (∀ y : WO S T, IsHalf (cA D p.e) y → ∀ Φ Φ' : SB (Matrix m m' k),
    (∀ u : WO S T, IsHalf p.e u → Φ'.1 (rd α β u) = ψ (symplO S T u y) * Φ.1 (rd α β u)) →
      M Φ' = heisO ψ S T y (M Φ))

def zCol (n' : Type) (ρ : ℕ) (b : n → k) : Matrix (n ⊕ Fin (2 * ρ)) (n' ⊕ Fin (2 * ρ + 1)) k :=
  fromBlocks 0 (Matrix.of fun r i => if i.val = ρ then b r else 0) 0 0

variable [MeasurableSpace k] [BorelSpace k]

def flatE (χ : AddChar k Circle) (ν : Measure k) (ρ : ℕ)
    (Φ : Matrix (n ⊕ Fin (2 * ρ)) (n' ⊕ Fin (2 * ρ + 1)) k → ℂ) (x : Matrix n (n' ⊕ Fin 1) k) : ℂ :=
  GlobalTheory.RootEx.opE χ ν (ρ + 1) (fun y => Φ (y + zCol n' ρ fun r => x r (Sum.inr 0))) (x.submatrix id Sum.inl)

omit [Fintype n] [DecidableEq n] in
theorem zCol_zero (ρ : ℕ) : zCol n' ρ (fun _ : n => (0 : k)) = 0 := by
  ext (r | r) (s | s) <;> simp [zCol]

theorem flatE_zero (χ : AddChar k Circle) (ν : Measure k) (ρ : ℕ)
    (Φ : Matrix (n ⊕ Fin (2 * ρ)) (n' ⊕ Fin (2 * ρ + 1)) k → ℂ) (x₀ : Matrix n n' k) :
    flatE χ ν ρ Φ (fromCols x₀ 0) = GlobalTheory.RootEx.opE χ ν (ρ + 1) Φ x₀ := by
  have h : (fun r => fromCols x₀ (0 : Matrix n (Fin 1) k) r (Sum.inr 0)) = fun _ => 0 := rfl
  rw [flatE, h, zCol_zero]
  simp only [add_zero]
  rfl

def FlatSplitBF (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (ρ : ℕ) (B : BesLev D ρ) (J : JacLev D ρ) (s : StepBF ψ B J)
    (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k]
    [BorelSpace k] (p : SplitPt D k) (χ : AddChar k Circle), IsWeilChar p ψ χ →
    ∀ (ν : Measure k), ν.IsAddHaarMeasure →
    ∀ (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']
      (αA : Frame p B.A n') (α₀ : Frame p B.V₀ (n' ⊕ Fin 1)) (β₀ : Frame p J.W₀ n)
      (α : Frame p B.V (n' ⊕ Fin (2 * ρ + 1))) (β : Frame p J.W (n ⊕ Fin (2 * ρ))),
      IsSumFrame B.o B.ζ αA α₀ → NormalBF B J αA β₀ α β →
      ∀ M : SB (Matrix (n ⊕ Fin (2 * ρ)) (n' ⊕ Fin (2 * ρ + 1)) k) →ₗ[ℂ] (WO B.V J.W → ℂ), IsModel ψ α β M →
        ∃ M₀ : SB (Matrix n (n' ⊕ Fin 1) k) →ₗ[ℂ] (WO B.V₀ J.W₀ → ℂ), IsModel ψ α₀ β₀ M₀ ∧
          ∀ Φ : SB (Matrix (n ⊕ Fin (2 * ρ)) (n' ⊕ Fin (2 * ρ + 1)) k),
            ∃ h : flatE χ ν ρ Φ.1 ∈ SB (Matrix n (n' ⊕ Fin 1) k), flatBF s (M Φ) = M₀ ⟨flatE χ ν ρ Φ.1, h⟩

example {k : Type} [Field k] (ξ N : k) (hξ : ξ ≠ 0) : IsNormalScal ξ (kaSrc 1 N) ![ξ, 1, -(ξ⁻¹ * N)] := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [kaSrc]

example {k : Type} [Field k] (ξ N : k) (hξ : ξ ≠ 0) : IsNormalScal ξ (kaTgt 1 N) ![ξ, N] := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [kaTgt]
  field_simp

end GlobalTheory.IndefiniteRowSideFullHecke.WeightedNormColumns

end
