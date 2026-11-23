import Mathlib
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.TheoremB

open MvPolynomial Filter Topology
open scoped Classical

noncomputable section

structure Shape where

  f : ℕ

  N : ℕ

  j : ℕ
  two_le_N : 2 ≤ N
  one_le_j : 1 ≤ j
  j_lt_N : j < N
  two_lt : 2 < f * (N - 1)

namespace Shape

variable (S : Shape)

theorem f_pos : 0 < S.f := by
  rcases Nat.eq_zero_or_pos S.f with h | h
  · have := S.two_lt; rw [h, zero_mul] at this; omega
  · exact h

abbrev Var : Type := Fin S.f × Fin S.N

abbrev Poly : Type := MvPolynomial S.Var ℝ

abbrev Emb : Type := Fin S.f × Bool

def tau0 : Fin S.f := ⟨0, S.f_pos⟩

def D : ℕ := S.f * (S.N * (S.N - 1) / 2)

def jp : ℕ := min S.j (S.N - S.j)

def top : Finset (Fin S.N) := Finset.univ.filter (fun i => (i : ℕ) < S.j)

def bot : Finset (Fin S.N) := Finset.univ.filter (fun i => S.j ≤ (i : ℕ))

def small : Finset (Fin S.N) := if S.j ≤ S.N - S.j then S.top else S.bot

def rho : S.Var →₀ ℕ := Finsupp.equivFunOnFinite.symm (fun v => (v.2 : ℕ))

def permVar (w : Fin S.f → Equiv.Perm (Fin S.N)) : S.Var ≃ S.Var :=
  Equiv.prodShear (Equiv.refl _) w

def sgn (w : Fin S.f → Equiv.Perm (Fin S.N)) : ℝ :=
  ∏ τ, ((Equiv.Perm.sign (w τ) : ℤ) : ℝ)

def intFl : S.Poly →ₗ[ℝ] ℝ :=
  ∑ w : Fin S.f → Equiv.Perm (Fin S.N),
    S.sgn w • ((lcoeff ℝ S.rho) ∘ₗ (rename (S.permVar w)).toLinearMap)

def Sh (τ : Fin S.f) : S.Poly →ₗ[ℝ] ℝ :=
  S.intFl ∘ₗ ∑ i ∈ S.top, (pderiv (τ, i) : Derivation ℝ S.Poly S.Poly).toLinearMap

def Tot (τ : Fin S.f) : S.Poly →ₗ[ℝ] ℝ :=
  S.intFl ∘ₗ ∑ i, (pderiv (τ, i) : Derivation ℝ S.Poly S.Poly).toLinearMap

def ShT : S.Poly →ₗ[ℝ] ℝ := ∑ τ, S.Sh τ

def TotT : S.Poly →ₗ[ℝ] ℝ := ∑ τ, S.Tot τ

def pSum (k : ℕ) (τ : Fin S.f) : S.Poly := ∑ i, X (τ, i) ^ k

def rankLie (σ : S.Emb) : ℕ := if σ.2 then S.N - S.j else S.j

def lieClass (m : ℕ) (σ : S.Emb) : S.Poly :=
  if σ.2 then (-1) ^ m * ∑ i ∈ S.bot, X (σ.1, i) ^ m else ∑ i ∈ S.top, X (σ.1, i) ^ m

def homog (d : ℕ) : Submodule ℝ S.Poly := homogeneousSubmodule S.Var ℝ d

def linForm (u : S.Var → ℝ) : S.Poly := ∑ v, C (u v) * X v

def Fu (u : S.Var → ℝ) : S.Poly := (-S.linForm u) ^ (S.D + 1)

def degU (u : S.Var → ℝ) : ℝ := S.intFl ((-S.linForm u) ^ S.D)

def gapAt (u : S.Var → ℝ) (τ : Fin S.f) : ℝ :=
  u (τ, ⟨S.j - 1, by have := S.j_lt_N; omega⟩) - u (τ, ⟨S.j, S.j_lt_N⟩)

def Dominant (u : S.Var → ℝ) : Prop := ∀ τ (a b : Fin S.N), a ≤ b → u (τ, b) ≤ u (τ, a)

def RegularDominant (u : S.Var → ℝ) : Prop := ∀ τ (a b : Fin S.N), a < b → u (τ, b) < u (τ, a)

def Regular (u : S.Var → ℝ) : Prop := ∀ τ (a b : Fin S.N), a ≠ b → u (τ, a) ≠ u (τ, b)

def maxAbs (u : S.Var → ℝ) : ℝ := ⨆ v, |u v|

def spread (u : S.Var → ℝ) (τ : Fin S.f) : ℝ := (⨆ i, u (τ, i)) - ⨅ i, u (τ, i)

def ubar (u : S.Var → ℝ) (τ : Fin S.f) : ℝ := (∑ i, u (τ, i)) / S.N

def cTau (u : S.Var → ℝ) (τ : Fin S.f) : ℝ := ∑ i ∈ S.top, u (τ, i) - S.j * S.ubar u τ

def sumAbs (u : S.Var → ℝ) (τ : Fin S.f) : ℝ := ∑ i, |u (τ, i)|

def B0 (u : S.Var → ℝ) (g : ℝ) : ℝ := 4 * S.f * S.N ^ 2 * (1 + S.maxAbs u / g)

structure WeightHyp (u : S.Var → ℝ) (g : ℝ) : Prop where
  g_pos : 0 < g
  regular_dominant : S.RegularDominant u
  gap_ge : ∀ τ, g ≤ S.gapAt u τ
  small_sep : ∀ τ, ∀ i ∈ S.small, ∀ l, l ≠ i → g ≤ |u (τ, i) - u (τ, l)|

def IsDecomp (F : S.Poly) (Q : Fin S.N → Fin S.f → S.Poly) : Prop :=
  (∀ k τ, (Q k τ).IsHomogeneous (S.D - k)) ∧
    F = ∑ k : Fin S.N, ∑ τ, S.pSum ((k : ℕ) + 1) τ * Q k τ

end Shape

open Shape

structure HostPrimes (S : Shape) where

  badNum : ℕ
  badNum_pos : 0 < badNum
  two_dvd_badNum : 2 ∣ badNum

  splits : ℕ → Bool

  frob : ℕ → Equiv.Perm S.Emb
  frob_conj : ∀ p (σ : S.Emb), frob p (σ.1, !σ.2) = ((frob p σ).1, !(frob p σ).2)
  frob_split : ∀ p (σ : S.Emb), p.Prime → ¬ p ∣ badNum → splits p = true →
    (frob p σ).2 = σ.2
  frob_inert : ∀ p (σ : S.Emb), p.Prime → ¬ p ∣ badNum → splits p = false →
    (frob p σ).2 = !σ.2

namespace HostPrimes

variable {S : Shape} (H : HostPrimes S)

def good (p : ℕ) : Prop := p.Prime ∧ ¬ p ∣ H.badNum

def kaP (p : ℕ) (τ : Fin S.f) : ℝ :=
  ∑' n : ℕ, ((p : ℝ) ^ (n + 1))⁻¹ * (S.rankLie ((H.frob p ^ (n + 1)) (τ, false)) : ℝ)

end HostPrimes

structure EndData (S : Shape) extends HostPrimes S where

  vol : ℝ
  vol_pos : 0 < vol

  PP : ℕ → S.Poly →ₗ[ℝ] ℝ

  hh : S.Poly →ₗ[ℝ] ℝ

  delta : ℕ → S.Poly →ₗ[ℝ] ℝ

  al : ℕ → Fin S.f → ℝ

  be : ℕ → Fin S.f → ℝ

  alM : ℕ → ℝ

  beM : ℕ → ℝ

  EE : ℕ → S.Poly →ₗ[ℝ] ℝ

  B1 : ℕ

  rd : ℝ
  one_le_rd : 1 ≤ rd

  LK : ℝ
  LK_nonneg : 0 ≤ LK

namespace EndData

variable {S : Shape} (V : EndData S)

def restTerm (p : ℕ) (Q : Fin S.N → Fin S.f → S.Poly) : ℝ :=
  Real.log p * V.vol * ∑ τ, ∑ k : Fin S.N,
    if 2 ≤ (k : ℕ) + 1 then
      ∑' n : ℕ, (((p : ℝ) ^ ((n + 1) * ((k : ℕ) + 1)))⁻¹ * (((k : ℕ) + 1 : ℕ) : ℝ) *
        S.intFl (S.lieClass k ((V.frob p ^ (n + 1)) (τ, false)) * Q k τ))
    else 0

def rest₂ (p : ℕ) (F : S.Poly) : ℝ :=
  if h : ∃ Q, S.IsDecomp F Q then V.restTerm p h.choose else 0

def rest (B0 : ℕ) (F : S.Poly) : ℝ :=
  ∑' p : {p : ℕ // V.good p ∧ B0 < p}, V.rest₂ p F

def goodIoc (B0 B : ℕ) : Finset ℕ := (Finset.Ioc B0 B).filter V.good

def aB (B0 : ℕ) (B : ℕ) : ℝ :=
  V.alM B - V.beM B + ∑ p ∈ V.goodIoc B0 B, Real.log p / ((p : ℝ) - 1)

def bB (B0 : ℕ) (B : ℕ) : ℝ :=
  V.beM B - (1 / (S.N : ℝ)) * ∑ p ∈ V.goodIoc B0 B, V.kaP p S.tau0 * Real.log p

def LocalHeightDeltaFormula : Prop :=
  ∀ p, V.good p → ∀ F ∈ S.homog (S.D + 1),
    V.delta p F = -(Real.log p / ((p : ℝ) - 1)) * V.vol * S.ShT F
      + ∑ τ, (V.kaP p τ * Real.log p / S.N) * V.vol * S.Tot τ F + V.rest₂ p F

def Prop6Add (B0 : ℕ) : Prop :=
  ∀ B : ℕ, B0 < B → ∀ F ∈ S.homog (S.D + 1),
    V.PP B0 F = V.PP B F + ∑ p ∈ V.goodIoc B0 B, V.delta p F

def CorBPrime : Prop :=
  (∀ B : ℕ, V.B1 ≤ B → ∀ F ∈ S.homog (S.D + 1),
    V.PP B F = V.vol * (V.hh F - ∑ τ, (V.al B τ - V.be B τ) * S.Sh τ F
      - ∑ τ, V.be B τ * S.Tot τ F) + V.EE B F) ∧
  ∃ CB : ℝ, ∀ B : ℕ, V.B1 ≤ B → 2 ≤ B → ∀ m : S.Var →₀ ℕ, (∑ v, m v) = S.D + 1 →
    |V.EE B (monomial m 1)| ≤ CB * Real.log B / B

def PropA : Prop :=
  ∃ C : ℝ, ∀ B : ℕ, V.B1 ≤ B → 2 ≤ B → ∀ τ,
    |V.al B τ - V.alM B| ≤ C * Real.log B / B ∧ |V.be B τ - V.beM B| ≤ C * Real.log B / B

structure EndInputs (B0 : ℕ) : Prop where
  corB : V.CorBPrime
  add6 : V.Prop6Add B0
  propA : V.PropA
  delta_formula_at_good_primes : V.LocalHeightDeltaFormula

def PropF (B0 : ℝ) : Prop :=
  ∀ τ, ∀ Q ∈ S.homog S.D, S.intFl Q = 1 →
    |V.PP ⌊B0⌋₊ (S.pSum 1 τ * Q)| ≤ V.vol * (4 * S.N * (Real.log (B0 * V.rd) + V.LK))

def Prop7cB (r0 B0 : ℝ) : Prop :=
  ∀ A0 : ℝ, Tendsto (V.aB ⌊B0⌋₊) atTop (𝓝 A0) → -A0 ≤ |r0| + 3 / 2 + 3 * Real.log B0

def HFlInput : Prop :=
  ∃ (A : Type) (_ : CommRing A) (_ : Algebra ℝ A) (adeg : A →ₗ[ℝ] ℝ) (xhat : S.Var → A),
    (∀ F, V.hh F = adeg (aeval xhat F)) ∧ ∀ τ, ∑ i, xhat (τ, i) = 0

def FlagHeightVanishesAtWalls : Prop :=
  (∀ u, S.Dominant u → (∃ τ, S.gapAt u τ = 0) → V.hh (S.Fu u) = 0) ∧
  ∀ u, S.Dominant u → 0 ≤ V.hh (S.Fu u)

end EndData

namespace Shape

variable (S : Shape)

def kap (u : S.Var → ℝ) (Q : Fin S.N → Fin S.f → S.Poly) (k : Fin S.N) (τ : Fin S.f)
    (γ : S.Poly) : ℝ :=
  (((k : ℕ) + 1 : ℕ) : ℝ) * S.intFl (γ * Q k τ) / (((S.D + 1 : ℕ) : ℝ) * S.degU u)

def PrimeSumDecompositionBound : Prop :=
  ∀ (u : S.Var → ℝ) (g : ℝ), S.Regular u → 0 < g →
    (∀ τ, ∀ i ∈ S.small, ∀ l, l ≠ i → g ≤ |u (τ, i) - u (τ, l)|) →
    ∀ Q, S.IsDecomp (S.Fu u) Q → ∀ σ : ℕ → ℕ → Fin S.f → S.Emb,
    ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime ∧ S.B0 u g < p) → ∀ M : ℕ,
      ∑ p ∈ P, Real.log p * ∑ τ, ∑ k : Fin S.N, (if 2 ≤ (k : ℕ) + 1 then
        ∑ n ∈ Finset.range M, ((p : ℝ) ^ ((n + 1) * ((k : ℕ) + 1)))⁻¹ *
          |S.kap u Q k τ (S.lieClass k (σ p (n + 1) τ))| else 0)
      ≤ 4 / (S.f * S.N) * S.jp * ∑ τ, S.spread u τ

end Shape

structure LimitData (S : Shape) where

  Mbar : (S.Var → ℝ) → ℚ → ℝ

  Ps : (S.Var → ℝ) → ℝ → ℝ

  shift : S.Var → ℝ

namespace LimitData

variable {S : Shape} (L : LimitData S)

def LimitPolynomialHypothesis (V : EndData S) (B0 : ℕ) : Prop :=
  (∃ q : MvPolynomial (Option S.Var) ℝ, ∀ lam s, L.Ps lam s = eval (fun o => Option.elim o s lam) q) ∧
  ∀ lam, L.Ps lam 0 = V.PP B0 (S.Fu lam)

def UniformSmallShiftDominance : Prop :=
  ∀ Λ : ℝ, ∃ C s0 : ℝ, 0 < s0 ∧ ∀ lam : S.Var → ℚ, (∑ v, |(lam v : ℝ)|) ≤ Λ →
    ∀ s : ℚ, 0 < s → (s : ℝ) ≤ s0 →
      S.Dominant (fun v => (lam v : ℝ) - s * L.shift v) →
      |L.Mbar (fun v => (lam v : ℝ)) s - L.Ps (fun v => (lam v : ℝ) - s * L.shift v) s| ≤ C * s

end LimitData

open EndData HostPrimes LimitData

def KaPSplit.Statement : Prop :=
  ∀ (S : Shape) (H : HostPrimes S) (p : ℕ), H.good p → H.splits p = true →
    ∀ τ, H.kaP p τ = S.j / ((p : ℝ) - 1)

def KaPInert.Statement : Prop :=
  ∀ (S : Shape) (H : HostPrimes S) (p : ℕ), H.good p → H.splits p = false →
    ∀ τ, H.kaP p τ = (((S.N - S.j : ℕ) : ℝ) * p + S.j) / ((p : ℝ) ^ 2 - 1)

def KaPBound.Statement : Prop :=
  ∀ (S : Shape) (H : HostPrimes S) (p : ℕ), H.good p →
    ∀ τ, 0 < H.kaP p τ ∧ H.kaP p τ ≤ S.N / ((p : ℝ) - 1)

def RestPWellDefined.Statement : Prop :=
  ∀ (S : Shape) (V : EndData S) (p : ℕ), V.good p →
    ∀ (F : S.Poly) (Q Q' : Fin S.N → Fin S.f → S.Poly), S.IsDecomp F Q → S.IsDecomp F Q' →
      V.restTerm p Q = V.restTerm p Q'

def RestPBound.Statement : Prop :=
  ∀ (S : Shape) (V : EndData S), ∀ F ∈ S.homog (S.D + 1),
    ∃ c : ℝ, ∀ p, V.good p → |V.rest₂ p F| ≤ c * Real.log p / (p : ℝ) ^ 2

def RestSummable.Statement : Prop :=
  ∀ (S : Shape) (V : EndData S) (B0 : ℕ), ∀ F ∈ S.homog (S.D + 1),
    Summable (fun p : {p : ℕ // V.good p ∧ B0 < p} => |V.rest₂ p F|)

def HeightSumIdentity.Statement : Prop :=
  ∀ (S : Shape) (V : EndData S) (B0 : ℕ), V.EndInputs B0 →
    ∃ EE' : ℕ → S.Poly → ℝ, (∀ F ∈ S.homog (S.D + 1), Tendsto (fun B => EE' B F) atTop (𝓝 0)) ∧
      ∀ B : ℕ, B0 < B → V.B1 < B → ∀ F ∈ S.homog (S.D + 1),
        V.PP B0 F = V.vol * (V.hh F - V.aB B0 B * S.ShT F - V.bB B0 B * S.TotT F)
          + ∑ p ∈ V.goodIoc B0 B, V.rest₂ p F + EE' B F

def ShTotIndependent.Statement : Prop :=
  ∀ S : Shape,
    LinearIndependent ℝ (fun i : Fin S.f ⊕ Fin S.f =>
      (Sum.elim (fun τ => S.Sh τ) (fun τ => S.Tot τ) i).domRestrict (S.homog (S.D + 1))) ∧
    LinearIndependent ℝ ![S.ShT.domRestrict (S.homog (S.D + 1)),
      S.TotT.domRestrict (S.homog (S.D + 1))]

def ShTotInvertiblePair.Statement : Prop :=
  ∀ S : Shape, ∃ F₁ ∈ S.homog (S.D + 1), ∃ F₂ ∈ S.homog (S.D + 1),
    S.ShT F₁ * S.TotT F₂ - S.TotT F₁ * S.ShT F₂ ≠ 0

def LimitsExist.Statement : Prop :=
  ∀ (S : Shape) (V : EndData S) (B0 : ℕ), V.EndInputs B0 →
    ∃ A0 b0 : ℝ, Tendsto (V.aB B0) atTop (𝓝 A0) ∧ Tendsto (V.bB B0) atTop (𝓝 b0)

def HeightTauIdentity.Statement : Prop :=
  ∀ (S : Shape) (V : EndData S) (B0 : ℕ), V.EndInputs B0 →
    ∀ A0 b0 : ℝ, Tendsto (V.aB B0) atTop (𝓝 A0) → Tendsto (V.bB B0) atTop (𝓝 b0) →
      ∀ F ∈ S.homog (S.D + 1),
        V.PP B0 F = V.vol * (V.hh F - A0 * S.ShT F - b0 * S.TotT F) + V.rest B0 F

def HeightEvaluation.Statement : Prop :=
  ∀ (S : Shape) (V : EndData S) (B0 : ℕ), V.EndInputs B0 →
    ∀ A0 b0 : ℝ, Tendsto (V.aB B0) atTop (𝓝 A0) → Tendsto (V.bB B0) atTop (𝓝 b0) →
      ∀ u : S.Var → ℝ,
        V.PP B0 (S.Fu u) = V.vol * V.hh (S.Fu u)
          + ((S.D + 1 : ℕ) : ℝ) * (V.vol * S.degU u)
            * ∑ τ, (A0 * S.cTau u τ + (S.j * A0 + S.N * b0) * S.ubar u τ)
          + V.rest B0 (S.Fu u)

def CBounds.Statement : Prop :=
  ∀ (S : Shape) (u : S.Var → ℝ) (τ : Fin S.f),
    (∀ a b : Fin S.N, a ≤ b → u (τ, b) ≤ u (τ, a)) →
      0 ≤ S.cTau u τ ∧ S.cTau u τ ≤ S.sumAbs u τ

def NormUbar.Statement : Prop :=
  ∀ (S : Shape) (u : S.Var → ℝ) (τ : Fin S.f),
    (∀ a b : Fin S.N, a ≤ b → u (τ, b) ≤ u (τ, a)) →
      (S.N : ℝ) * |S.ubar u τ| ≤ S.sumAbs u τ

def TermA.Statement : Prop :=
  ∀ (S : Shape) (V : EndData S), V.FlagHeightVanishesAtWalls → ∀ u, S.Dominant u → 0 ≤ V.vol * V.hh (S.Fu u)

def TermB.Statement : Prop :=
  ∀ (S : Shape) (V : EndData S) (u : S.Var → ℝ) (g : ℝ), S.WeightHyp u g → S.PrimeSumDecompositionBound →
    |V.rest ⌊S.B0 u g⌋₊ (S.Fu u)|
      ≤ 4 / (S.f * S.N) * ((S.D + 1 : ℕ) : ℝ) * (V.vol * S.degU u) * S.jp * ∑ τ, S.spread u τ

def TermC.Statement : Prop :=
  ∀ (S : Shape) (V : EndData S) (B0 : ℝ), 1 ≤ B0 → V.EndInputs ⌊B0⌋₊ → V.HFlInput →
    V.PropF B0 →
    ∀ A0 b0 : ℝ, Tendsto (V.aB ⌊B0⌋₊) atTop (𝓝 A0) → Tendsto (V.bB ⌊B0⌋₊) atTop (𝓝 b0) →
      |S.j * A0 + S.N * b0| ≤ 4 * S.N * (Real.log (B0 * V.rd) + V.LK)

def TermD.Statement : Prop :=
  ∀ r0 : ℝ, ∃ C : ℝ, ∀ (S : Shape) (V : EndData S) (B0 : ℝ), 4 * S.f * S.N ^ 2 ≤ B0 →
    V.Prop7cB r0 B0 → ∀ A0 : ℝ, Tendsto (V.aB ⌊B0⌋₊) atTop (𝓝 A0) →
      -C * Real.log B0 - C * ∑ p ∈ V.badNum.primeFactors, Real.log p / p ≤ A0

def PrimesLogSum.Statement : Prop :=
  ∃ C : ℝ, ∀ B0 : ℝ, 2 ≤ B0 → ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime) → (P.card : ℝ) ≤ B0 →
    ∑ p ∈ P, Real.log p / ((p : ℝ) - 1) ≤ C * Real.log B0

def TheoremTUpper.Statement : Prop :=
  ∀ r0 : ℝ, ∃ C : ℝ, ∀ (S : Shape) (V : EndData S) (u : S.Var → ℝ) (g : ℝ),
    S.WeightHyp u g → (V.badNum.primeFactors.card : ℝ) ≤ S.B0 u g →
    V.EndInputs ⌊S.B0 u g⌋₊ → V.HFlInput → V.FlagHeightVanishesAtWalls → V.PropF (S.B0 u g) →
    V.Prop7cB r0 (S.B0 u g) → S.PrimeSumDecompositionBound →
      -C * ((S.D + 1 : ℕ) : ℝ) * (V.vol * S.degU u) *
          ((Real.log (S.B0 u g * V.rd) + V.LK) * ∑ τ, S.sumAbs u τ + S.jp * ∑ τ, S.spread u τ)
        ≤ V.PP ⌊S.B0 u g⌋₊ (S.Fu u)

def NefAtBaseHeight.Statement : Prop :=
  ∀ (S : Shape) (u : S.Var → ℝ) (g : ℝ), S.WeightHyp u g →
    4 * S.f * S.N ^ 2 * S.maxAbs u + g ≤ (S.B0 u g - 2) * g ∧
    ∀ C7 : ℝ, 0 ≤ C7 → ∃ s1 : ℝ, 0 < s1 ∧ ∀ s : ℝ, 0 < s → s < s1 →
      ∀ u'' : S.Var → ℝ, (∀ v, |u'' v - u v| ≤ C7 * s / 2) →
        S.RegularDominant u'' ∧ 4 * S.f * S.maxAbs u'' ≤ (S.B0 u g - 2) * ⨅ τ, S.gapAt u'' τ

def LimitTheorem.Statement : Prop :=
  ∀ (S : Shape) (V : EndData S) (L : LimitData S) (B0 : ℕ) (u : S.Var → ℝ),
    L.LimitPolynomialHypothesis V B0 →
      Tendsto (fun s : ℚ => L.Ps (fun v => u v - s * L.shift v) s) (𝓝[>] 0)
        (𝓝 (V.PP B0 (S.Fu u)))

def TheoremTLower.Statement : Prop :=
  ∀ (S : Shape) (V : EndData S) (L : LimitData S) (u : S.Var → ℝ) (g : ℝ),
    S.WeightHyp u g → (∀ v, ∃ q : ℚ, u v = q) →
    L.LimitPolynomialHypothesis V ⌊S.B0 u g⌋₊ → L.UniformSmallShiftDominance →
      Tendsto (fun s : ℚ => L.Mbar u s) (𝓝[>] 0) (𝓝 (V.PP ⌊S.B0 u g⌋₊ (S.Fu u)))

def HeightLimitIdentity.Statement : Prop :=
  ∀ (S : Shape) (V : EndData S) (B0 : ℕ), V.EndInputs B0 → V.HFlInput →
    ∀ A0 b0 : ℝ, Tendsto (V.aB B0) atTop (𝓝 A0) → Tendsto (V.bB B0) atTop (𝓝 b0) →
      ∀ τ, ∀ Q ∈ S.homog S.D, S.intFl Q = 1 →
        S.j * A0 + S.N * b0 = -V.PP B0 (S.pSum 1 τ * Q) / V.vol

def FlagHeightZeroAtOne.Statement : Prop :=
  ∀ (S : Shape) (V : EndData S), V.HFlInput → ∀ τ (Q : S.Poly), V.hh (S.pSum 1 τ * Q) = 0

def Shape.ex : Shape := ⟨3, 2, 1, le_refl _, le_refl _, by norm_num, by norm_num⟩

def conjSwap (S : Shape) : Equiv.Perm S.Emb :=
  ⟨fun σ => (σ.1, !σ.2), fun σ => (σ.1, !σ.2), fun σ => by simp, fun σ => by simp⟩

def HostPrimes.ex : HostPrimes Shape.ex where
  badNum := 2
  badNum_pos := by norm_num
  two_dvd_badNum := dvd_refl _
  splits := fun p => p % 4 == 1
  frob := fun p => if p % 4 = 1 then 1 else conjSwap Shape.ex
  frob_conj := fun p σ => by
    by_cases h : p % 4 = 1 <;> simp [h, conjSwap]
  frob_split := fun p σ _ _ h => by
    have h' : p % 4 = 1 := by simpa using h
    simp [h']
  frob_inert := fun p σ _ _ h => by
    have h' : ¬ p % 4 = 1 := by simpa using h
    simp [h', conjSwap]

theorem HostPrimes.ex_good_split : HostPrimes.ex.good 5 ∧ HostPrimes.ex.splits 5 = true := by
  refine ⟨⟨by norm_num, by decide⟩, by decide⟩

theorem HostPrimes.ex_good_inert : HostPrimes.ex.good 3 ∧ HostPrimes.ex.splits 3 = false := by
  refine ⟨⟨by norm_num, by decide⟩, by decide⟩

def EndData.ex : EndData Shape.ex where
  toHostPrimes := HostPrimes.ex
  vol := 2
  vol_pos := by norm_num
  PP := fun _ => 0
  hh := (aeval (0 : Shape.ex.Var → ℝ)).toLinearMap
  delta := fun _ => 0
  al := fun _ _ => 0
  be := fun _ _ => 0
  alM := fun B => -∑ p ∈ (Finset.Ioc 1 B).filter HostPrimes.ex.good, Real.log p / ((p : ℝ) - 1)
  beM := fun _ => 0
  EE := fun _ => 0
  B1 := 0
  rd := 3
  one_le_rd := by norm_num
  LK := 1
  LK_nonneg := by norm_num

def Shape.exWeight : Shape.ex.Var → ℝ := fun v => if (v.2 : ℕ) = 0 then 1 else 0

theorem Shape.exWeight_hyp : Shape.ex.WeightHyp Shape.exWeight 1 := by
  refine ⟨by norm_num, ?_, ?_, ?_⟩
  · intro τ a b hab
    have ha : (a : ℕ) = 0 := by
      have : (b : ℕ) < 2 := b.isLt
      have : (a : ℕ) < (b : ℕ) := hab
      omega
    have hb : (b : ℕ) ≠ 0 := by
      have : (a : ℕ) < (b : ℕ) := hab
      omega
    simp [Shape.exWeight, ha, hb]
  · intro τ
    simp [Shape.gapAt, Shape.exWeight, Shape.ex]
  · intro τ i hi l hl
    rw [show Shape.ex.small = Shape.ex.top from if_pos (by decide)] at hi
    have hi' : (i : ℕ) < 1 := (Finset.mem_filter.mp hi).2
    have hi0 : (i : ℕ) = 0 := by omega
    have hl0 : (l : ℕ) ≠ 0 := by
      intro h; exact hl (Fin.ext (by omega))
    simp [Shape.exWeight, hi0, hl0]

def Shape.exDecompQ : Fin Shape.ex.N → Fin Shape.ex.f → Shape.ex.Poly :=
  fun k τ => if (k : ℕ) = 0 then X (τ, ⟨0, by decide⟩) ^ Shape.ex.D else 0

theorem Shape.exDecomp :
    Shape.ex.IsDecomp
      (∑ k : Fin Shape.ex.N, ∑ τ, Shape.ex.pSum ((k : ℕ) + 1) τ * Shape.exDecompQ k τ)
      Shape.exDecompQ := by
  refine ⟨fun k τ => ?_, rfl⟩
  by_cases hk : (k : ℕ) = 0
  · simp only [Shape.exDecompQ, hk, Nat.sub_zero, if_true]
    simpa using (isHomogeneous_X ℝ (τ, (⟨0, by decide⟩ : Fin Shape.ex.N))).pow Shape.ex.D
  · simp only [Shape.exDecompQ, hk]
    exact isHomogeneous_zero _ _ _

theorem EndData.ex_hfl : EndData.ex.HFlInput :=
  ⟨ℝ, inferInstance, inferInstance, LinearMap.id, 0, fun _ => rfl, fun _ => by simp⟩

theorem EndData.example_flag_height_vanishes : EndData.ex.FlagHeightVanishesAtWalls := by
  refine ⟨fun u _ _ => ?_, fun u _ => ?_⟩ <;>
    simp [EndData.ex, Shape.Fu, Shape.linForm]

theorem EndData.ex_propF : EndData.ex.PropF 1 := by
  intro τ Q _ _
  have h3 : (0 : ℝ) ≤ Real.log (1 * 3) := Real.log_nonneg (by norm_num)
  simp only [EndData.ex, LinearMap.zero_apply, abs_zero]
  have : (0 : ℝ) ≤ 4 * (Shape.ex.N : ℝ) * (Real.log (1 * 3) + 1) := by positivity
  linarith

theorem EndData.ex_prop7cB (r0 : ℝ) : EndData.ex.Prop7cB r0 1 := by
  intro A0 hA
  have h0 : EndData.ex.aB ⌊(1 : ℝ)⌋₊ = fun _ => 0 := by
    funext B
    simp [EndData.aB, EndData.goodIoc, EndData.ex]
  rw [h0] at hA
  have : A0 = 0 := tendsto_nhds_unique hA tendsto_const_nhds
  subst this
  have : (0 : ℝ) ≤ Real.log 1 := by simp
  have : (0 : ℝ) ≤ |r0| := abs_nonneg _
  linarith

def LimitData.ex : LimitData Shape.ex := ⟨fun _ _ => 0, fun _ _ => 0, 0⟩

theorem LimitData.example_limit_polynomial_hypothesis (B0 : ℕ) : LimitData.ex.LimitPolynomialHypothesis EndData.ex B0 :=
  ⟨⟨0, fun _ _ => by simp [LimitData.ex]⟩, fun _ => by simp [LimitData.ex, EndData.ex]⟩

theorem LimitData.example_uniform_small_shift_bound : LimitData.ex.UniformSmallShiftDominance :=
  fun _ => ⟨0, 1, by norm_num, fun _ _ _ _ _ _ => by simp [LimitData.ex]⟩

theorem Shape.exWeight_rat : ∀ v, ∃ q : ℚ, Shape.exWeight v = q := by
  intro v
  by_cases h : (v.2 : ℕ) = 0
  · exact ⟨1, by simp [Shape.exWeight, h]⟩
  · exact ⟨0, by simp [Shape.exWeight, h]⟩

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.TheoremB
