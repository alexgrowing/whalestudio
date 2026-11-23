import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.StandardModuleConstituents
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.UPartBot

noncomputable section

open MeasureTheory Matrix Filter Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagLeviGroup GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.LeviFactor
open scoped InnerProductSpace Topology

namespace GlobalTheory.StdCon

variable {n a : ℕ}

def blockExt (j : Fin a → ℕ) (x : Fin a → ℝ) (l : ℕ) : ℝ :=
  ∑ i, if ∑ m ∈ Finset.Iio i, j m ≤ l ∧ l < ∑ m ∈ Finset.Iic i, j m then x i else 0

def derPart (ε : Fin n → Bool) (W : Flag n a) : Subgroup (UJ ε) where
  carrier := {g | g ∈ leviOne ε W ∧ (uMat g).det = 1 ∧ ∀ i, ∀ h : ∀ y ∈ W i, Matrix.toLin' (uMat g) y ∈ W i,
    LinearMap.det ((Matrix.toLin' (uMat g)).restrict h) = 1}
  one_mem' := ⟨(leviOne ε W).one_mem, by simp [uMat_one], fun i h => by
    rw [show (Matrix.toLin' (uMat (1 : UJ ε))).restrict h = 1 by ext y : 2; simp [uMat_one]]
    simp⟩
  mul_mem' := fun {g h} hg hh => ⟨(leviOne ε W).mul_mem hg.1 hh.1, by
    rw [uMat_mul, Matrix.det_mul, hg.2.1, hh.2.1, one_mul], fun i e => by
    have h1 : ∀ y ∈ W i, Matrix.toLin' (uMat g) y ∈ W i := fun y hy => (hg.1.1 i y hy).1
    have h2 : ∀ y ∈ W i, Matrix.toLin' (uMat h) y ∈ W i := fun y hy => (hh.1.1 i y hy).1
    rw [show (Matrix.toLin' (uMat (g * h))).restrict e =
      (Matrix.toLin' (uMat g)).restrict h1 * (Matrix.toLin' (uMat h)).restrict h2 by
        ext y : 2; simp [uMat_mul, Matrix.toLin'_mul], map_mul, hg.2.2, hh.2.2, one_mul]⟩
  inv_mem' := fun {g} hg => ⟨(leviOne ε W).inv_mem hg.1, by
    have := congrArg Matrix.det (uMat_mul_inv g)
    rwa [Matrix.det_mul, hg.2.1, one_mul, Matrix.det_one] at this, fun i e => by
    have h1 : ∀ y ∈ W i, Matrix.toLin' (uMat g) y ∈ W i := fun y hy => (hg.1.1 i y hy).1
    have : (Matrix.toLin' (uMat g)).restrict h1 * (Matrix.toLin' (uMat g⁻¹)).restrict e = 1 := by
      ext y : 2; simp [uMat_mul_inv]
    have h3 := congrArg LinearMap.det this
    rwa [map_mul, hg.2.2, one_mul, map_one] at h3⟩

def IsSph {ε : Fin n → Bool} (S : Subgroup (UJ ε)) {b : ℕ} (W₀ : Flag n b) (lam : Fin b → ℝ) (φ : UJ ε → ℂ) : Prop :=
  φ ∈ indFun S (fun _ => 1) W₀ (fun _ => (1 : ℂ →L[ℂ] ℂ)) (fun l => (lam l : ℂ)) ∧ ∀ k ∈ KG ε ⊓ S, φ k = 1

def reExt {ε : Fin n → Bool} (D : Datum ε) (b : ℕ) : Fin b → ℝ := fun l => blockExt D.j (fun i => (D.s i).re) l

def kCoef {ε : Fin n → Bool} {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] (f' f : UJ ε → V) (g : UJ ε) : ℂ :=
  ∫ k : KG ε, ⟪f' k, f (k * g)⟫_ℂ ∂muK ε

def LeviBound : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (b : ℕ) (W₀ : Flag n b), IsMinimalFlag ε W₀ → ∀ D : Datum ε,
    (∀ i, D.W i ∈ Set.range W₀) → ∀ φ, IsSph (ε := ε) ⊤ W₀ (reExt D b) φ →
    ∀ μ : Measure ↥(KG ε ⊓ D.M), μ.IsHaarMeasure → IsProbabilityMeasure μ →
    ∀ U : Submodule ℂ D.V, FiniteDimensional ℂ U → (∀ k ∈ KG ε ⊓ D.M, ∀ w ∈ U, D.σ (uMat k) w ∈ U) →
      ∃ c : ℝ, ∀ v ∈ U, ∀ w ∈ U, ∀ m ∈ D.M,
        ‖⟪w, D.σ (uMat m) v⟫_ℂ‖ ≤ c * ‖v‖ * ‖w‖ * ∫ κ : ↥(KG ε ⊓ D.M), ‖φ (κ * m)‖ ∂μ

def Growth : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (b : ℕ) (W₀ : Flag n b), IsMinimalFlag ε W₀ → ∀ D : Datum ε, D.IsStandard W₀ →
    ∀ f ∈ D.fns, IsKFinFun f → ∀ f' ∈ D.dualFns, IsKFinFun f' → ∃ (C : ℝ) (d : ℕ),
      ∀ x : Fin b → ℝ, Antitone x → (∀ l, 0 ≤ x l) → ∀ t, IsSplit ε W₀ x t →
        ‖kCoef f' f t‖ ≤ C * Real.exp (∑ l, (reExt D b l - (rho n (fun _ : Fin b => 1) l).re) * x l) * (1 + ‖x‖) ^ d

example (x : ℝ) : blockExt ![2] ![x] 1 = x ∧ blockExt ![2] ![x] 2 = 0 := by
  constructor <;> simp [blockExt]

theorem exists_isSph {ε : Fin n → Bool} {b : ℕ} {W₀ : Flag n b} (h : IsMinimalFlag ε W₀) (lam : Fin b → ℝ) :
    ∃ φ, IsSph (ε := ε) ⊤ W₀ lam φ := by
  obtain ⟨f, hf, h1, hK⟩ := exists_spherical h.1 (fun _ => le_rfl) (fun l => (lam l : ℂ))
  exact ⟨f, hf, fun k hk => by simpa [h1] using hK 1 k hk.1⟩

end GlobalTheory.StdCon

end
