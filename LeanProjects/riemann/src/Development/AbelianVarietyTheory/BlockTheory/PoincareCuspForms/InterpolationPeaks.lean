import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.BasePsiLeviLowerBound

namespace GlobalTheory.IndefiniteRowSideFullHecke.InterpolationPeaks

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates
open MeasureTheory Topology
open scoped ContDiff ENNReal

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

def bExp (X : Data E r) : ℝ := 5 * (X.Ψ.card : ℝ) * (r : ℝ) ^ 2

def leviR {n : ℕ} (g : V n → ℝ) (z : V n) (ξ : Fin n → ℂ) : ℝ :=
  (leviV n (fun w => ((g w : ℝ) : ℂ)) z ξ).re

def smoothPart (X : Data E r) (x0 : Frame X.Ψ r) (G L : Wt X.Ψ r) (ps : Frame X.Ψ r → ℝ)
    (z : V (nd X)) : ℝ :=
  phla X G (cpt X x0 z) - Real.log (densF X x0 z) - (nd X : ℝ) * phla X L (cpt X x0 z) + ps (cpt X x0 z)

def MarginAt (X : Data E r) (x0 : Frame X.Ψ r) (G L : Wt X.Ψ r) (ps : Frame X.Ψ r → ℝ) (m : ℝ) : Prop :=
  ∀ z ∈ OmF X x0, ∀ ξ : Fin (nd X) → ℂ,
    m * leviR (rhF X x0) z ξ ≤ leviR (smoothPart X x0 G L ps) z ξ

def StrictAt (X : Data E r) (x0 : Frame X.Ψ r) (G L : Wt X.Ψ r) (ps : Frame X.Ψ r → ℝ) : Prop :=
  (∃ η : ℝ, 0 < η ∧ ∀ z ∈ OmF X x0, ∀ ξ : Fin (nd X) → ℂ,
    2 * η * leviR (fun w => phla X L (cpt X x0 w)) z ξ ≤ leviR (smoothPart X x0 G L ps) z ξ) ∧
  ∀ z ∈ OmF X x0, ∀ ξ : Fin (nd X) → ℂ, ξ ≠ 0 → 0 < leviR (fun w => phla X L (cpt X x0 w)) z ξ

def HasMargin (X : Data E r) (G L : Wt X.Ψ r) (ps : Frame X.Ψ r → ℝ) (b : ℝ) : Prop :=
  ∃ m : ℝ, b < m ∧ ∀ x0, IsOrth X x0 → MarginAt X x0 G L ps m

def tFac {X : Data E r} (Xa : ArchInM X) : ℝ := 1 + Xa.c1 / Xa.a1

def InOrbit {X : Data E r} {Xa : ArchInM X} (Fl : FlatM X Xa) (x : Frame X.Ψ r) : Prop :=
  ∃ j, ∃ γ ∈ X.Γ, ∃ b ∈ Bor X.Ψ r, x = lact γ (rmul (Fl.xs j) b)

def ModeBound (X : Data E r) : Prop :=
  ∀ (G : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) (ps : Frame X.Ψ r → ℝ) (a : ℝ),
    0 ≤ a → IsInvFn X ps → cfwM X ps a → X.IsBddSec G P →
    (∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 → ∃ C A : ℝ, ∀ x ∈ X.dom, IsOrth X x →
      ENNReal.ofReal (X.pnorm G P x) ≤ ENNReal.ofReal (C * X.la1 x ^ (-A)) *
        ⨆ (z : V (nd X)) (_ : ‖z‖ < ρ) (_ : cpt X x z ∈ X.dom),
          ENNReal.ofReal (Real.exp (ps (cpt X x z) / 2))) →
    ∀ ξ, X.IsIso ξ → ∀ ν : X.Ψ → ℝ, ∀ x ∈ X.dom, X.fj G ξ ν P x ≠ 0 → a ≤ ∑ τ, ν τ

def PeakAt {X : Data E r} {Xa : ArchInM X} (Fl : FlatM X Xa) (G : Wt X.Ψ r) (ps : Frame X.Ψ r → ℝ)
    (b : ℝ) (x0 : Frame X.Ψ r) (z0 : V (nd X)) : Prop :=
  ∃ (F : V (nd X) → ℂ) (P : Frame X.Ψ r → ℂ), DifferentiableOn ℂ F (OmF X x0) ∧
    InAt X x0 (fun x => ENNReal.ofReal (Real.exp (-(phla X G x + ps x)))) b F ∧
    IsBEq X G P ∧ (∀ z ∈ OmF X x0, P (cpt X x0 z) = F z) ∧ F z0 ≠ 0 ∧
    ∀ x ∈ X.dom, InOrbit Fl x → (¬ ∃ β ∈ Bor X.Ψ r, x = rmul (cpt X x0 z0) β) → P x = 0

def InterpFor (b : ∀ {r : ℕ}, Data E r → ℝ) : Prop :=
  ∀ (r : ℕ) (X : Data E r) (Xa : ArchInM X) (Fl : FlatM X Xa), PropDisc X →
    HasMargin X Xa.Fp Xa.L (fun _ => 0) (b X) →
    ∀ v : Fin Fl.δ → ℂ, ∃ P ∈ X.SS Xa.Fp, ∀ j, P (Fl.xs j) = v j

def InterpGtFor (b : ∀ {r : ℕ}, Data E r → ℝ) : Prop :=
  ∀ (r : ℕ) (X : Data E r) (Xa : ArchInM X) (Fl : FlatM X Xa), PropDisc X → ModeBound X →
    HasMargin X Xa.Fp Xa.L (fun x => tFac Xa * Xa.ps0 x) (b X) →
    ∀ v : Fin Fl.δ → ℂ, ∃ P ∈ X.SSgt Xa.Fp Xa.c1, ∀ j, P (Fl.xs j) = v j

def CoreFor (b : ∀ {r : ℕ}, Data E r → ℝ) : Prop :=
  ∀ (r : ℕ) (X : Data E r) (Xa : ArchInM X) (Fl : FlatM X Xa) (G : Wt X.Ψ r) (ps : Frame X.Ψ r → ℝ)
    (x0 : Frame X.Ψ r) (z0 : V (nd X)) (m : ℝ),
    IsInvFn X ps → (∃ C : ℝ, ∀ x ∈ X.dom, ps x ≤ C) →
    IsOrth X x0 → ContDiffOn ℝ ∞ (fun z => ps (cpt X x0 z)) (OmF X x0) →
    z0 ∈ OmF X x0 → InOrbit Fl (cpt X x0 z0) →
    b X < m → MarginAt X x0 G Xa.L ps m → StrictAt X x0 G Xa.L ps →
    PeakAt Fl G ps (b X) x0 z0

variable (E)

def InterpStatement : Prop := InterpFor (E := E) bExp

def InterpGtStatement : Prop := InterpGtFor (E := E) bExp

def CoreStatement : Prop := CoreFor (E := E) bExp

def StrictStatement : Prop :=
  ∀ (r : ℕ) (X : Data E r) (Xa : ArchInM X) (t : ℝ), 0 ≤ t → t * Xa.rr ≤ 2 * Xa.T →
    ∀ x0, IsOrth X x0 → StrictAt X x0 Xa.Fp Xa.L (fun x => t * Xa.ps0 x)

def Statement : Prop :=
  InterpStatement E ∧ InterpGtStatement E ∧ CoreStatement E ∧ StrictStatement E

variable {E}

theorem four_lt_bExp (X : Data E r) (hf : 0 < X.Ψ.card) (hr : 0 < r) :
    4 * (X.Ψ.card : ℝ) * (r : ℝ) ^ 2 < bExp X := by
  have h1 : (0 : ℝ) < X.Ψ.card := by exact_mod_cast hf
  have h2 : (0 : ℝ) < r := by exact_mod_cast hr
  have : 0 < (X.Ψ.card : ℝ) * (r : ℝ) ^ 2 := by positivity
  unfold bExp; nlinarith

theorem factor_mul_firstMinimum {X : Data E r} (Xa : ArchInM X) : tFac Xa * Xa.a1 = Xa.c1 + Xa.a1 := by
  have := Xa.frame_theta_weight_pos.ne'
  unfold tFac; field_simp; ring

theorem tFac_range {X : Data E r} (Xa : ArchInM X) : 0 ≤ tFac Xa ∧ tFac Xa * Xa.rr ≤ 2 * Xa.T := by
  have h1 := Xa.frame_theta_weight_pos
  have h2 := Xa.frame_theta_const_pos
  refine ⟨by unfold tFac; positivity, ?_⟩
  rw [mul_comm]; exact Xa.rr_le

theorem peak_of_interpGt (h : InterpGtStatement E) (X : Data E r) (Xa : ArchInM X) (Fl : FlatM X Xa)
    (hd : PropDisc X) (hm : ModeBound X)
    (hq : HasMargin X Xa.Fp Xa.L (fun x => tFac Xa * Xa.ps0 x) (bExp X)) (j : Fin Fl.δ) :
    ∃ P ∈ X.SSgt Xa.Fp Xa.c1, ∀ j', P (Fl.xs j') ≠ 0 ↔ j' = j := by
  obtain ⟨P, hP, hv⟩ := h r X Xa Fl hd hm hq (fun j' => if j' = j then 1 else 0)
  refine ⟨P, hP, fun j' => ?_⟩
  rw [hv]; by_cases e : j' = j <;> simp [e]

end

end GlobalTheory.IndefiniteRowSideFullHecke.InterpolationPeaks
