import Mathlib
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Birational
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsSmoothHermTrivLine

open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top
open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter (pullHerm)

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.Top.Link

variable {Ψ : Type} [Fintype Ψ] {N : ℕ}

def reline (M : RootModel Ψ N) (xdeg : Ψ × Fin N → M.K → ℤ) (x : ℝ → Ψ × Fin N → HermLine M.ι)
    (x_deg : ∀ t r, (x t r).a = xdeg r) (x_smooth : ∀ t r, IsSmoothHerm (x t r))
    (x_conj : ∀ t r, IsConjInvariantH (x t r)) (A : HermLine M.ι) (A_smooth : IsSmoothHerm A)
    (A_conj : IsConjInvariantH A) : RootModel Ψ N :=
  { M with xdeg := xdeg, x := x, x_deg := x_deg, x_smooth := x_smooth, x_conj := x_conj, A := A,
           A_smooth := A_smooth, A_conj := A_conj }

theorem arMono_reline (M : RootModel Ψ N) {d₁ x₁ h₁ s₁ c₁ A₁ a₁ b₁ d₂ x₂ h₂ s₂ c₂ A₂ a₂ b₂}
    (II : IntersectionSystem) (t : ℝ) (m : Option (Ψ × Fin N) →₀ ℕ) (hx : ∀ r, x₁ t r = x₂ t r) (hA : A₁ = A₂) :
    (reline M d₁ x₁ h₁ s₁ c₁ A₁ a₁ b₁).arMono II t m = (reline M d₂ x₂ h₂ s₂ c₂ A₂ a₂ b₂).arMono II t m := by
  subst hA
  have hl : (reline M d₁ x₁ h₁ s₁ c₁ A₁ a₁ b₁).line t = (reline M d₂ x₂ h₂ s₂ c₂ A₁ a₂ b₂).line t := by
    funext o
    cases o with
    | none => rfl
    | some r => exact hx r
  unfold RootModel.arMono
  rw [hl]
  rfl

def pullModel (M₀ : RootModel Ψ N) {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {Ω : Type} [Field Ω]
    (y : (Σ k, J k) → Ω) (ha : IsArithVar (mCoordIdeal y) (dimFl Ψ N + 1)) (hb : Birational y)
    {κ : M₀.K → K} {v : (Σ k, M₀.ι k) → Σ k, J k} (hv : IsBlockMap κ v) (δ : ℕ) (hδ : 0 < δ) : RootModel Ψ N where
  K := K
  ι := J
  Ω := Ω
  y := y
  arith := ha
  birational := hb
  xdeg r := pullDeg κ (M₀.xdeg r)
  x t r := pullHerm hv (M₀.x t r)
  x_deg t r := by
    show pullDeg κ (M₀.x t r).a = _
    rw [M₀.x_deg]
  x_smooth t r := Chg.isSmoothHerm_pull hv (M₀.x_smooth t r)
  x_conj t r := Chg.isConj_pull hv (M₀.x_conj t r)
  kA := M₀.kA
  kA_pos := M₀.kA_pos
  A := pullHerm hv M₀.A
  A_smooth := Chg.isSmoothHerm_pull hv M₀.A_smooth
  A_conj := Chg.isConj_pull hv M₀.A_conj
  δ := δ
  δ_pos := hδ

end GlobalTheory.CompanionTheory.Ar.Top.Link
