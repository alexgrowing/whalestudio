import Mathlib
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Proportional

noncomputable section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology

namespace GlobalTheory.CompanionTheory.Ar.Top

variable {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N : ℕ}

def InWall (j : ℕ) (τ₀ : Ψ) (c₀ : ℝ) (lam : Wt Ψ N) : Prop :=
  ‖lam‖ ≤ 1 / 2 ∧ gap j lam τ₀ = 0 ∧ (∀ τ, τ ≠ τ₀ → c₀ ≤ gap j lam τ) ∧ CompactGapsGE j c₀ lam

def FrobShape (frob : ℕ → Ψ → ℕ → Ψ ⊕ Ψ) : Prop := ∀ p n τ τ', (frob p τ n).isLeft = (frob p τ' n).isLeft

def LabelInv (hh : RP Ψ N → ℝ) : Prop :=
  ∀ (σ : Equiv.Perm Ψ) (F : RP Ψ N), hh (rename (fun x : Ψ × Fin N => (σ x.1, x.2)) F) = hh F

def restTerm (j p : ℕ) (fr : ℕ → Ψ ⊕ Ψ) (k : ℕ) (Q : RP Ψ N) : ℝ :=
  if 2 ≤ k then Real.log p * k * ∑' n : ℕ, ((p : ℝ) ^ k)⁻¹ ^ (n + 1) * degFl (pLie j (k - 1) (fr n) * Q) else 0

def restSum (j : ℕ) (bad : Finset ℕ) (frob : ℕ → Ψ → ℕ → Ψ ⊕ Ψ) (B₀ : ℕ) (τ : Ψ) (k : ℕ) (Q : RP Ψ N) : ℝ :=
  ∑' p : ℕ, if p.Prime ∧ B₀ < p ∧ p ∉ bad then restTerm j p (frob p τ) k Q else 0

def IsDecomp (F : RP Ψ N) (Q : Ψ → ℕ → RP Ψ N) : Prop :=
  (∀ τ k, 1 ≤ k → k ≤ N → (Q τ k).IsHomogeneous (dimFl Ψ N + 1 - k)) ∧
    F = ∑ τ, ∑ k ∈ Finset.Icc 1 N, pk τ k * Q τ k

def muSmall (j : ℕ) : RP Ψ N :=
  if N - j ≤ j then ∑ τ, ∑ i ∈ Finset.univ.filter (fun i : Fin N => j ≤ (i : ℕ)), X (τ, i) else -∑ τ, pkLow j τ 1

def fibClass (j : ℕ) : RP Ψ N :=
  ∏ τ, ∏ ab ∈ Finset.univ.filter (fun ab : Fin N × Fin N => ab.1 < ab.2 ∧ ((ab.1 : ℕ) < j ↔ (ab.2 : ℕ) < j)),
    (X (τ, ab.2) - X (τ, ab.1))

def dimX (Ψ : Type) [Fintype Ψ] (N j : ℕ) : ℕ := Fintype.card Ψ * (j * (N - j))

def testPoly (j : ℕ) : RP Ψ N := muSmall j ^ (dimX Ψ N j + 1) * fibClass j

def testDeg (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) : ℝ :=
  degFl (muSmall j ^ dimX Ψ N j * fibClass j : RP Ψ N)

namespace RootTower

variable (T : RootTower Ψ N) (II : IntersectionSystem)

def ThmW : Prop :=
  ∀ c₀ > (0 : ℝ), ∃ C : ℝ, ∃ B₁ : ℕ, ∀ B : ℕ, B₁ ≤ B → ∀ τ₀ (lam : Wt Ψ N), InWall T.j τ₀ c₀ lam →
    |T.PB II B lam| ≤ C * Real.log B / B

def ThmB (hh : RP Ψ N → ℝ) : Prop :=
  ∃ C : ℝ, ∃ B₁ : ℕ, ∀ B : ℕ, B₁ ≤ B → ∃ α β : Ψ → ℝ, ∀ m : Ψ × Fin N →₀ ℕ, m.degree = dimFl Ψ N + 1 →
    |T.PPt II B (monomial m 1) - T.volT * (hh (monomial m 1) - ∑ τ, (α τ - β τ) * Sh T.j τ (monomial m 1) -
      ∑ τ, β τ * Tot τ (monomial m 1))| ≤ C * Real.log B / B

def ThmBA (hh : RP Ψ N → ℝ) : Prop :=
  ∃ C : ℝ, ∃ B₁ : ℕ, ∀ B : ℕ, B₁ ≤ B → ∃ α β : ℝ, ∀ m : Ψ × Fin N →₀ ℕ, m.degree = dimFl Ψ N + 1 →
    |T.PPt II B (monomial m 1) - T.volT * (hh (monomial m 1) - (α - β) * ∑ τ, Sh T.j τ (monomial m 1) -
      β * ∑ τ, Tot τ (monomial m 1))| ≤ C * Real.log B / B

def IdentAt (hh : RP Ψ N → ℝ) (frob : ℕ → Ψ → ℕ → Ψ ⊕ Ψ) (B₀ : ℕ) (A₀ b₀ : ℝ) : Prop :=
  ∀ τ (k : ℕ), 1 ≤ k → k ≤ N → ∀ Q : RP Ψ N, Q.IsHomogeneous (dimFl Ψ N + 1 - k) →
    T.PPt II B₀ (pk τ k * Q) = T.volT * (hh (pk τ k * Q) - A₀ * ∑ σ, Sh T.j σ (pk τ k * Q) -
      b₀ * ∑ σ, Tot σ (pk τ k * Q) + restSum T.j T.bad frob B₀ τ k Q)

def SlopeLower (C rd Lval : ℝ) : Prop :=
  ∀ B : ℕ, 128 ≤ B → 4 * Fintype.card Ψ * N ^ 2 ≤ B → T.bad.card ≤ B →
    -(C * Fintype.card Ψ * (min T.j (N - T.j) : ℕ) * bigLam B rd Lval) *
        (((dimX Ψ N T.j : ℝ) + 1) * (T.volT * testDeg Ψ N T.j)) ≤ T.PPt II B (testPoly T.j)

def LowerBoundAtBase (hh : RP Ψ N → ℝ) (frob : ℕ → Ψ → ℕ → Ψ ⊕ Ψ) (C rd Lval : ℝ) : Prop :=
  ∀ (B₀ : ℕ) (A₀ b₀ : ℝ), 128 ≤ B₀ → 4 * Fintype.card Ψ * N ^ 2 ≤ B₀ → T.bad.card ≤ B₀ →
    T.IdentAt II hh frob B₀ A₀ b₀ → -(C * bigLam B₀ rd Lval) ≤ A₀

def T1 : Prop :=
  ∀ (u : Wt Ψ N) (g : ℝ), WeightHyp T.j u g → ∀ B : ℕ, bigB0 u g < B + 1 → ∀ c,
    (∀ᶠ s in 𝓝[>] (0 : ℝ), (T.M B c).NefFib (T.lamS u s) s ∧ (T.M B c).Semipos (scale s) (T.lamS u s) s) ∧
    Tendsto (fun s => T.mbarTop II B c u s) (𝓝[>] 0) (𝓝 (T.PPc II B c (linRoot u ^ (dimFl Ψ N + 1)))) ∧
    Tendsto (fun s => T.mDeg B c u s) (𝓝[>] 0) (𝓝 (T.vol c * flagDeg u)) ∧ 0 < T.vol c * flagDeg u ∧
    Tendsto (fun s => T.mbarTop II B c u s / (((dimFl Ψ N : ℝ) + 1) * T.mDeg B c u s)) (𝓝[>] 0)
      (𝓝 (T.slope II B c u))

def bracket (rd Lval : ℝ) (B : ℕ) (u : Wt Ψ N) : ℝ :=
  bigLam B rd Lval * l1 u + (min T.j (N - T.j) : ℕ) * spread u

def T2 (C rd Lval : ℝ) : Prop :=
  ∀ (u : Wt Ψ N) (g : ℝ), WeightHyp T.j u g → ∀ B : ℕ, 128 ≤ B → bigB0 u g < B + 1 → T.bad.card ≤ B →
    -(C * ((dimFl Ψ N : ℝ) + 1) * (T.volT * flagDeg u) * T.bracket rd Lval B u) ≤ T.PB II B u

def MeanSlope (C rd Lval : ℝ) : Prop :=
  ∀ (u : Wt Ψ N) (g : ℝ), WeightHyp T.j u g → ∀ B : ℕ, 128 ≤ B → bigB0 u g < B + 1 → T.bad.card ≤ B →
    -(C * T.bracket rd Lval B u) ≤ (∑ c, T.slope II B c u) / (Fintype.card T.Comp : ℝ)

end RootTower

end GlobalTheory.CompanionTheory.Ar.Top
