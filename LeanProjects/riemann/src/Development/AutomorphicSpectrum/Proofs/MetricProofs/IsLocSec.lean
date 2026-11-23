import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.PullbackPullback
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ] {y : (Σ k, ι k) → Φ}
  {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N j : ℕ}

def xiDeg (M : FlagModel y Ψ N j) (τ : Ψ) (a : Fin N) : K → ℤ := fun k => ∑ p, xiCoef τ a p * M.dy p k

def aDeg (M : FlagModel y Ψ N j) (τ : Ψ) (a : Fin N) (k₀ : K) : Option K → ℤ := fun o =>
  match o with
  | none => 1
  | some k => if k = k₀ then 1 else -xiDeg M τ a k

def potA (M : FlagModel y Ψ N j) (τ : Ψ) (a : Fin N) (k₀ : K) : HermLine fun o : Option K => ι (o.getD k₀) :=
  fsHerm (fun o : Option K => ι (o.getD k₀)) (aDeg M τ a k₀)

def IsPtData (M : FlagModel y Ψ N j) (τ : Ψ) (a : Fin N) (k₀ : K) (ca cb : Fin N) {e : ℕ}
    (RW : AnLogRes (mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X)) ⊤ e) (x : RW.X) (z₀ z₁ : (Σ k, ι k) → ℂ)
    (F : FrameData ι Ψ N M.Ω M.blk) (h : Matrix (Fin N) (Fin N) ℂ) (t : ℂ) : Prop :=
  M.IsFrame F ∧ M.GoodAt F (mCoordIdeal (basePart M.blk z₀)) ∧ SameOrbit z₀ (fstPt k₀ (RW.lift x x)) ∧
    SameOrbit z₁ (sndPt k₀ (RW.lift x x)) ∧ IsBlockDiag j h ∧ h.det ≠ 0 ∧ t ≠ 0 ∧
    (∀ i, M.ExactAt F (τ, i) z₀ h) ∧ ∀ i, M.ExactAt F (τ, i) z₁ (h * (1 + Matrix.single cb ca t))

def IsLocSec (M : FlagModel y Ψ N j) {n e : ℕ} (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n) (τ : Ψ) (a : Fin N) (k₀ : K)
    (ca cb : Fin N) (RW : AnLogRes (mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X)) ⊤ e) (pr : RW.X → Rb.X) (x : RW.X)
    (ψ : OpenPartialHomeomorph RW.X (Fin e → ℂ)) (kb : Fin Rb.A.n) (σ : Fin n ↪ Fin e) (i₀ : Fin e) (V : Set RW.X)
    (u : RW.X → ℂ) : Prop :=
  (∃ F H, IsWChart M Rb τ a k₀ ca cb RW pr ψ kb σ i₀ F H) ∧ IsOpen V ∧ x ∈ V ∧ V ⊆ ψ.source ∧ V ⊆ RW.U x ∧
    RW.A.HoloOn V u ∧ (∀ y' ∈ V, u y' ≠ 0) ∧
    (∀ y' ∈ V, ψ y' i₀ = 0 ↔ SameOrbit (fstPt k₀ (RW.lift y' y')) (sndPt k₀ (RW.lift y' y'))) ∧
    ∀ y' ∈ V, ψ y' i₀ ≠ 0 → ∀ z₀ z₁ F h t, IsPtData M τ a k₀ ca cb RW y' z₀ z₁ F h t →
      Real.log ‖u y' * ψ y' i₀‖ - Real.log ((potA M τ a k₀).h (RW.lift x y')) = normRhs M τ a F z₀ z₁ h t

def diagSet (k₀ : K) {P J : Ideal (MRing fun o : Option K => ι (o.getD k₀))} {e : ℕ} (R : AnLogRes P J e) : Set R.X :=
  {x | SameOrbit (fstPt k₀ (R.lift x x)) (sndPt k₀ (R.lift x x))}

def diagSec {e : ℕ} {X : Type} [TopologicalSpace X] (ψ : X → OpenPartialHomeomorph X (Fin e → ℂ)) (i₀ : X → Fin e)
    (u : X → X → ℂ) : X → X → ℂ := fun x y' => u x y' * ψ x y' (i₀ x)

def secPot {κ : Type} [Fintype κ] {ρ : κ → Type} [∀ k, Fintype (ρ k)] {P J : Ideal (MRing ρ)} {e : ℕ}
    (R : AnLogRes P J e) (A : HermLine ρ) (V : R.X → Set R.X) (hV : ∀ x, IsOpen (V x)) (hm : ∀ x, x ∈ V x) (c : ℝ) :
    LocPot R.X where
  U := V
  isOpen_U := hV
  mem_U := hm
  φ x y' := Real.log (A.h (R.lift x y')) + c

end GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec
