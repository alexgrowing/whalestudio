import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsParahoricVec
import Development.AbelianVarietyTheory.Definitions.Foundations.SecondCountableAndT2LocalField
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LeviRep

noncomputable section

open MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThetaGL ValuativeRel

namespace PositivityTheory.Tls2.Ming3

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {r n : ℕ} {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

def Equi (μ : kˣ →* ℂˣ) (σ : Representation ℂ (GL (Fin r) k) V) (π : Representation ℂ (GL (Fin n) k) W)
    (B : SB (Matrix (Fin n) (Fin r) k) →ₗ[ℂ] W →ₗ[ℂ] V) : Prop :=
  ∀ (g : GL (Fin r) k) (h : GL (Fin n) k) (Φ Φ' : SB (Matrix (Fin n) (Fin r) k)),
    (Φ' : Matrix (Fin n) (Fin r) k → ℂ) = om μ g h Φ → ∀ F : W, B Φ' (π h F) = σ g (B Φ F)

def VanRk (B : SB (Matrix (Fin n) (Fin r) k) →ₗ[ℂ] W →ₗ[ℂ] V) (j : ℕ) : Prop :=
  ∀ Φ : SB (Matrix (Fin n) (Fin r) k), (∀ x : Matrix (Fin n) (Fin r) k, x.rank < j → Φ.1 x = 0) → B Φ = 0

def ballM (c : kˣ) (x₀ : Matrix (Fin n) (Fin r) k) : Set (Matrix (Fin n) (Fin r) k) :=
  {x | ∀ i l, valuation k (x i l - x₀ i l) ≤ valuation k (c : k)}

variable (k n r) in

def idem (j : ℕ) : Matrix (Fin n) (Fin r) k := Matrix.of fun i l => if (i : ℕ) = l ∧ (l : ℕ) < j then 1 else 0

def IsGerm [MeasurableSpace k] (ν : Measure k) (B : SB (Matrix (Fin n) (Fin r) k) →ₗ[ℂ] W →ₗ[ℂ] V)
    (x₀ : Matrix (Fin n) (Fin r) k) (w : W) (v : V) : Prop :=
  ∃ c : kˣ, ∀ Φ : SB (Matrix (Fin n) (Fin r) k), (∀ x, Φ.1 x ≠ 0 → x ∈ ballM c x₀) →
    B Φ w = (∫ x, Φ.1 x ∂volM ν (Fin n) (Fin r)) • v

def ParLaw {t : ℕ} (μ : kˣ →* ℂˣ) (σ : Representation ℂ (GL (Fin r) k) V) (π : Representation ℂ (GL (Fin (r + t)) k) W)
    (ev : W →ₗ[ℂ] V) : Prop :=
  ∀ (p : parab k (two (stdSum (rfl : r + t = r + t)))) (w : W), ev (π p w) =
    ((deltaHalf k (Two (Fin r) (Fin t)) (leviProj k (two (stdSum (rfl : r + t = r + t))) p) : ℂ) *
      (μ (Matrix.GeneralLinearGroup.det (leviProj k (two (stdSum (rfl : r + t = r + t))) p true : GL (Fin t) k)) : ℂ)) •
      σ (leviProj k (two (stdSum (rfl : r + t = r + t))) p false : GL (Fin r) k) (ev w)

end PositivityTheory.Tls2.Ming3

end
