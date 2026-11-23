import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.FWExist

noncomputable section

open NumberField Matrix ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.Pj
open scoped TensorProduct ContDiff

namespace GlobalTheory.HolRead

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def NegFirst (V : HSp D) (q : ℕ) (x : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) : Prop :=
  ∀ ρ, (x ρ)ᴴ * gramAt D V ρ * x ρ = diagonal fun c : Fin V.rank => if (c : ℕ) < q then (-1 : ℂ) else 1

def SmoothReal (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D) (φ : GA D V → ℂ) : Prop :=
  ∀ (k : ℕ) (τs : Fin k → D.what₂.Tau) (Xs : Fin k → Matrix (Fin V.rank) (Fin V.rank) ℂ),
    (∀ i, Xs i ∈ lieAt V (τs i)) → ∀ g,
      ContDiff ℝ ∞ fun t : Fin k → ℝ => φ (g * (List.ofFn fun i => oneP θ V (τs i) (Xs i) (t i)).prod)

def IsHolFor (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D)
    (x : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) (w : D.what₂.Tau → Fin V.rank → ℤ) (φ : GA D V → ℂ) : Prop :=
  SmoothReal θ V φ ∧
  (∀ ρ (c d : Fin V.rank), c < d → RderC θ V ρ (x ρ * Matrix.single c d 1 * (x ρ)⁻¹) φ = 0) ∧
  ∀ ρ (t : Fin V.rank → ℝ) g,
    φ (g * atTau θ V ρ (x ρ * diagonal (fun c => Complex.exp ((t c : ℂ) * Complex.I)) * (x ρ)⁻¹)) =
      Complex.exp (((∑ c, (w ρ c : ℝ) * t c : ℝ) : ℂ) * Complex.I) * φ g

def IsUnitFr {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r) (y : Frame X.Ψ r) : Prop :=
  ∀ τ : X.Ψ, gram τ.1 X.Gm (mat y τ) = diagonal fun a : Fin r => ((sgn X.p0 (a : ℕ) : ℝ) : ℂ)

def unitLie {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r) : Set (Frame X.Ψ r) :=
  {Z | ∀ τ : X.Ψ, (mat Z τ)ᴴ * (diagonal fun a : Fin r => ((sgn X.p0 (a : ℕ) : ℝ) : ℂ)) +
    (diagonal fun a : Fin r => ((sgn X.p0 (a : ℕ) : ℝ) : ℂ)) * mat Z τ = 0}

def expFr {E : Type} [Field E] {Ψ : Finset (E →+* ℂ)} {r : ℕ} (Z : Frame Ψ r) : Frame Ψ r :=
  fun τ => (NormedSpace.exp (mat Z τ) : Matrix (Fin r) (Fin r) ℂ)

open Classical in

def unitFr {E : Type} [Field E] {Ψ : Finset (E →+* ℂ)} {r : ℕ} (τ : Ψ) (c d : Fin r) : Frame Ψ r :=
  fun τ' a b => if τ' = τ ∧ a = c ∧ b = d then 1 else 0

def ModelOf (V : HSp D) {r : ℕ} (hr : V.rank = r) (X : Data D.host.E r) : Prop :=
  (∀ τ : D.host.E →+* ℂ, τ ∈ X.Ψ ↔ ∃ ρ, τ = tauE D ρ) ∧ ModelW V hr X

def FrIs (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D) {r : ℕ} (hr : V.rank = r)
    (X : Data D.host.E r) (x : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) (u : GA D V) (y : Frame X.Ψ r) : Prop :=
  ∀ (ρ : D.what₂.Tau) (τ : X.Ψ), τ.1 = tauE D ρ →
    mat y τ = Matrix.reindex (finCongr hr) (finCongr hr) (archM V (θ ρ) u * x ρ)

def BaseDict (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D) {r : ℕ} (hr : V.rank = r)
    {Comp : Type} (X : Comp → Data D.host.E r) (dict : GA D V → Σ k, Frame (X k).Ψ r) (Kf : Subgroup (GA D V))
    (x₀ : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) : Prop :=
  (∀ k, ModelOf V hr (X k) ∧ NegFirst V (X k).p0 x₀ ∧ ∃ g, (dict g).1 = k) ∧
  (∀ h, ∃ γ ∈ GQ V, FrIs θ V hr (X (dict h).1) x₀ (γ * h) (dict h).2 ∧
    ∀ u ∈ GinfC V, ∃ γ' ∈ (X (dict h).1).Γ, ∃ y : Frame (X (dict h).1).Ψ r,
      dict (h * u) = ⟨(dict h).1, lact γ' y⟩ ∧ FrIs θ V hr (X (dict h).1) x₀ (γ * h * u) y) ∧
  ∀ g g', (∃ γ' ∈ (X (dict g).1).Γ, dict g' = ⟨(dict g).1, lact γ' (dict g).2⟩) →
    ∃ γ ∈ GQ V, ∃ k ∈ Kf, g' = γ * g * k

def KillPair {n : ℕ} (ε : Fin n → Bool) (a b : Fin n) : Prop :=
  (ε a = true ∧ ε b = true ∧ a < b) ∨ (ε a = false ∧ ε b = false ∧ b < a) ∨ (ε a ≠ ε b ∧ b < a)

def wtCol {R : Ranks} (h : HCParam R) (p q c : ℕ) : ℤ :=
  ⌊if c < q then Formalism.L2.NTheta.lamAt h (p + c) - (p : ℚ) / 2 - ((q : ℚ) - 1) / 2 + (c : ℚ)
    else Formalism.L2.NTheta.lamAt h (c - q) + (q : ℚ) / 2 - ((p : ℚ) - 1) / 2 + ((c - q : ℕ) : ℚ)⌋

end GlobalTheory.HolRead
