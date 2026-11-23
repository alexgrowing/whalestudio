import Formalism.WeightedDeltaMeans.LowerBoundLinearPower
import Formalism.WeightedDeltaMeans.LogBaseHeightBound
import Formalism.LocalToGlobal.LatticeGeometry.PluckerHadamard.StThmB
import Formalism.LocalRingCardinality.HeightBoundGeFourthPowerRank

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions MvPolynomial Filter Topology Finset

namespace Formalism.L2.Geo

section Alg

open Formalism.ShimuraLimitIdentity (Pol Sh Tot psumAt Kills)

def smallBlock (N j : ℕ) : Finset (Fin N) := univ.filter (fun i : Fin N => j ≤ i.val)

variable {Ψ : Type} [Fintype Ψ] {N : ℕ}

def a0Mu (j : ℕ) : Pol Ψ N := ∑ τ : Ψ, ∑ i ∈ smallBlock N j, X (τ, i)

def smallBlockPowerSum (j : ℕ) (τ : Ψ) (k : ℕ) : Pol Ψ N := ∑ i ∈ smallBlock N j, X (τ, i) ^ k

def blockVandermondePolynomial (τ : Ψ) (S : Finset (Fin N)) : Pol Ψ N :=
  ∏ a ∈ S, ∏ b ∈ S.filter (fun b => a < b), (X (τ, a) - X (τ, b))

def fibreVandermondeProduct (j : ℕ) (cf : ℝ) : Pol Ψ N :=
  C cf * ∏ τ : Ψ, (blockVandermondePolynomial τ (Formalism.ShimuraLimitIdentity.top N j) * blockVandermondePolynomial τ (smallBlock N j))

def a0F (j n : ℕ) (cf : ℝ) : Pol Ψ N := a0Mu j ^ (n + 1) * fibreVandermondeProduct j cf

def a0JP (j n : ℕ) (cf : ℝ) : Pol Ψ N := a0Mu j ^ n * fibreVandermondeProduct j cf

def a0n (Ψ : Type) [Fintype Ψ] (N j : ℕ) : ℕ := Fintype.card Ψ * (j * (N - j))

end Alg

section AlgStmt

open Formalism.ShimuraLimitIdentity (Pol Sh Tot psumAt Kills)

def LargestBlockVandermondeVanishes : Prop :=
  ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j n : ℕ) (cf : ℝ) (τ : Ψ),
    ∑ i ∈ Formalism.ShimuraLimitIdentity.top N j, pderiv (τ, i) (a0F (Ψ := Ψ) (N := N) j n cf) = 0

def TotalDerivativeValue : Prop :=
  ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j n : ℕ) (cf : ℝ) (τ : Ψ),
    ∑ i : Fin N, pderiv (τ, i) (a0F (Ψ := Ψ) (N := N) j n cf) =
      C (((n : ℝ) + 1) * ((N - j : ℕ) : ℝ)) * a0JP j n cf

def TestPolynomialHomogeneous : Prop :=
  ∀ (Ψ : Type) [Fintype Ψ] (N j : ℕ) (cf : ℝ), j ≤ N →
    (a0F (Ψ := Ψ) (N := N) j (a0n Ψ N j) cf).IsHomogeneous (Formalism.DegreeFormula.dimFl Ψ N + 1)

def FlagIntegralNonzero : Prop :=
  ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ), j ≤ N →
    degFlL Ψ N (a0JP (Ψ := Ψ) (N := N) j (a0n Ψ N j) 1) ≠ 0

def FlagIntegralAnnihilatesPowerSums : Prop :=
  ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ), Kills (degFlL Ψ N)

def RestTermBound : Prop :=
  ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (cf : ℝ) (Q : Ψ → ℕ → Pol Ψ N), j < N →
    a0F j (a0n Ψ N j) cf = ∑ σ : Ψ, ∑ k ∈ Icc 1 N, psumAt σ k * Q σ k →
    ∀ (τ τ' : Ψ) (k : ℕ), k ∈ Icc 2 N →
      |(k : ℝ) * degFlL Ψ N (smallBlockPowerSum j τ' (k - 1) * Q τ k)| ≤
        ((a0n Ψ N j : ℝ) + 1) * |degFlL Ψ N (a0JP j (a0n Ψ N j) cf)| *
          (2 * (((j * (N - j) : ℕ) : ℝ) + N)) ^ (k - 1) / (Nat.factorial k : ℝ)

def PrimeSumBound : Prop :=
  ∀ (Pr : Finset ℕ) (f N B0 X : ℝ) (K : ℕ), (∀ p ∈ Pr, p.Prime ∧ B0 < p) → 1 ≤ f → 2 ≤ N →
    4 * f * N ^ 2 ≤ B0 → 0 ≤ X → X ≤ 3 / 2 * N ^ 2 →
    ∑ p ∈ Pr, Real.log p *
      (f * ∑ k ∈ Icc 2 K, 2 * ((p : ℝ) ^ k)⁻¹ * X ^ (k - 1) / (Nat.factorial k : ℝ)) ≤ 8 / 5

def TwistShapeProp {Ψ : Type} [Fintype Ψ] {N : ℕ} (j : ℕ) (I : Pol Ψ N →ₗ[ℝ] ℝ) (vol : ℝ) (p : ℕ)
    (Q : Ψ → ℕ → Pol Ψ N) (rp : ℝ) : Prop :=
  ∃ (geo : Ψ → ℕ → ℝ) (Gt : ℕ → Ψ → ℕ → Pol Ψ N),
    rp = Real.log p * vol * ∑ τ : Ψ, ∑ k ∈ Icc 2 N, (k : ℝ) * geo τ k ∧
    (∀ τ k, HasSum (fun m : ℕ => (((p : ℝ) ^ k)⁻¹) ^ (m + 1) * I (Gt m τ k * Q τ k)) (geo τ k)) ∧
    ∀ m τ k, ∃ (τ' : Ψ) (s : ℝ) (H : Pol Ψ N), (s = 1 ∨ s = -1) ∧
      Gt m τ k = C s * smallBlockPowerSum j τ' (k - 1) + psumAt τ' (k - 1) * H

def RestBoundFromPrimeSum : Prop :=
  ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] [Nonempty Ψ] (N j : ℕ) (cf vol B0 restF : ℝ)
    (Q : Ψ → ℕ → Pol Ψ N) (Pr : ℕ → Finset ℕ) (rp : ℕ → ℝ),
    RestTermBound → PrimeSumBound → Kills (degFlL Ψ N) →
    j < N → 2 ≤ N → 0 < vol → 4 * (Fintype.card Ψ : ℝ) * (N : ℝ) ^ 2 ≤ B0 →
    a0F j (a0n Ψ N j) cf = ∑ σ : Ψ, ∑ k ∈ Icc 1 N, psumAt σ k * Q σ k →
    (∀ B, ∀ p ∈ Pr B, p.Prime ∧ B0 < p) →
    (∀ B, ∀ p ∈ Pr B, TwistShapeProp j (degFlL Ψ N) vol p Q (rp p)) →
    Tendsto (fun B => ∑ p ∈ Pr B, rp p) atTop (𝓝 restF) →
    |restF| ≤ 8 / 5 * (((a0n Ψ N j : ℝ) + 1) * vol * |degFlL Ψ N (a0JP j (a0n Ψ N j) cf)|)

def CauchyBinetHadamard : Prop :=
  ∀ (a b : ℕ) (Z : Matrix (Fin a) (Fin b) ℂ), (∀ i k, ‖Z i k‖ = 1) →
    1 / 2 * Real.log (Matrix.det (1 + Z * Z.conjTranspose)).re ≤ (a : ℝ) / 2 * Real.log (1 + b)

def LowerBoundFromTermBounds : Prop :=
  ∀ (Ψ : Type) [Fintype Ψ] [Nonempty Ψ] (N j jp n : ℕ) (PPF hhF restF vol J K1 Ca Λ : ℝ)
    (A0 b0 ShF TotF : Ψ → ℝ),
    N = j + jp → 1 ≤ jp → 2 * jp ≤ N → 0 < vol → 0 < J → 0 ≤ K1 → 0 ≤ Ca → 1 ≤ Λ →
    Real.log ((N : ℝ) + 1) ≤ Λ →
    PPF = vol * (hhF - (∑ τ, A0 τ * ShF τ) - (∑ τ, b0 τ * TotF τ)) + restF →
    (∀ τ, ShF τ = 0) → (∀ τ, TotF τ = ((n : ℝ) + 1) * jp * J) →
    -(((n : ℝ) + 1) * vol * J * (Ca * (Fintype.card Ψ : ℝ) * jp * Λ)) ≤ PPF →
    hhF ≤ ((n : ℝ) + 1) * J * ((Fintype.card Ψ : ℝ) * (jp / 2 * Real.log ((N : ℝ) + 1))) →
    |restF| ≤ 8 / 5 * (((n : ℝ) + 1) * vol * J) →
    (∀ τ, |(j : ℝ) * A0 τ + (N : ℝ) * b0 τ| ≤ K1 * N * Λ) →
    (∀ τ σ, A0 τ = A0 σ) →
    ∀ τ, -((2 * K1 + 2 * Ca + 21 / 5) * Λ) ≤ A0 τ

def LowerBoundHypothesis {Ψ : Type} (A0 : Ψ → ℝ) (K2 Λ : ℝ) : Prop := ∀ τ, -(K2 * Λ) ≤ A0 τ

end AlgStmt

section Geo

open Formalism.ShimuraLimitIdentity (Pol Sh Tot psumAt Kills)

variable {D : D7} {G : DV.Geo D.what₂.LL} {Lev : Type}
  {jC : ∀ (p : ℕ) [Fact p.Prime], PlL D p → (DV.KW p →+* ℂ)} {ng : NgPkg} {w : Dat D Lev}

structure ExtensionData (U : ShimU D G jC ng w) where

  Xb : U.Comp → G.Var

  PtX : U.Comp → Type

  bdX : ∀ c, PtX c → Prop

  htX : ∀ c, G.Adl (Xb c) → PtX c → ℝ

  degX : ∀ c, G.Adl (Xb c) → ℝ

  semiposX : ∀ c, G.Adl (Xb c) → Prop
  nefFibX : ∀ c, G.Adl (Xb c) → Prop
  ampleX : ∀ c, G.Adl (Xb c) → Prop

  muC : ℝ → ℝ → ℝ → ∀ c, G.Adl (Xb c)

  arLim : ℝ → U.Comp → ℝ

  degMu : U.Comp → ℝ

  meanU : U.Comp → ℝ

  fdeg : ℝ

def trivialExtensionData (U : ShimU D G jC ng w) : ExtensionData U where
  Xb := U.alg.Yv
  PtX := fun _ => Empty
  bdX := fun _ _ => False
  htX := fun _ _ _ => 0
  degX := fun _ _ => 0
  semiposX := fun _ _ => True
  nefFibX := fun _ _ => True
  ampleX := fun _ _ => False
  muC := fun B _ _ c => U.alg.Mbar B 0 0 c
  arLim := fun _ _ => 0
  degMu := fun _ => 1
  meanU := fun _ => 0
  fdeg := 1

section Props

variable (U : ShimU D G jC ng w) (X : ExtensionData U)

abbrev fA (D : D7) : ℝ := (Fintype.card D.what₂.Tau : ℝ)

abbrev jpA (w : Dat D Lev) : ℝ := ((w.N - w.j : ℕ) : ℝ)

abbrev nA (w : Dat D Lev) : ℕ := a0n D.what₂.Tau w.N w.j

def JA (w : Dat D Lev) (cf : ℝ) : ℝ := by
  classical
  exact degFlL D.what₂.Tau w.N (a0JP w.j (nA w) cf)

abbrev FA (w : Dat D Lev) (cf : ℝ) : Pol D.what₂.Tau w.N := a0F w.j (nA w) cf

def ZhangLowerXProp : Prop :=
  ∀ (c : U.Comp) (Lb : G.Adl (X.Xb c)), X.semiposX c Lb → X.nefFibX c Lb → X.ampleX c Lb →
    ∀ e : ℝ, (∀ y, e ≤ X.htX c Lb y) → ((G.dim (X.Xb c) : ℝ) + 1) * e * X.degX c Lb ≤ G.arTop (X.Xb c) Lb

def DimXProp : Prop := ∀ c, G.dim (X.Xb c) = nA w

def CuspBundlePosProp : Prop :=
  ∀ B : ℝ, 4 * fA D ≤ B - 2 → ∀ ep t' : ℝ, 0 < ep → ep ≤ 1 → 0 < t' → t' ≤ 1 → ∀ c,
    X.semiposX c (X.muC B ep t' c) ∧ X.nefFibX c (X.muC B ep t' c) ∧ X.ampleX c (X.muC B ep t' c)

def HtInteriorProp (Ch K rd Lchi : ℝ) : Prop :=
  ∀ B : ℝ, 4 * fA D * (w.N : ℝ) ^ 2 ≤ B → ∀ ep t' : ℝ, 0 < ep → ep ≤ 1 → 0 < t' → t' ≤ 1 → ∀ c y, ¬ X.bdX c y →
    -(Ch * fA D * jpA w * (Real.log (B * rd) + Lchi)) - ep * K ≤ X.htX c (X.muC B ep t' c) y

def HtBoundaryProp (Ch K rd Lchi : ℝ) : Prop :=
  ∀ B : ℝ, 4 * fA D * (w.N : ℝ) ^ 2 ≤ B → ∀ ep t' : ℝ, 0 < ep → ep ≤ 1 → 0 < t' → t' ≤ 1 → ∀ c y, X.bdX c y →
    -(Ch * fA D * jpA w * (Real.log (B * rd) + Lchi)) - ep * K ≤ X.htX c (X.muC B ep t' c) y

def StokesLimitProp (K : ℝ) : Prop :=
  ∀ B : ℝ, 4 * fA D ≤ B - 2 → ∀ (c : U.Comp) (a : ℝ),
    (∀ ep t' : ℝ, 0 < ep → ep ≤ 1 → 0 < t' → t' ≤ 1 →
      ((nA w : ℝ) + 1) * (a - ep * K) * X.degX c (X.muC B ep t' c) ≤ G.arTop (X.Xb c) (X.muC B ep t' c)) →
    ((nA w : ℝ) + 1) * (a - X.meanU c / 2) * X.degMu c ≤ X.arLim B c

def CuspMeanProp (Cu rd Lchi : ℝ) : Prop :=
  1 ≤ w.N - w.j → 3 * (w.N - w.j) + 1 ≤ w.N → ∀ B : ℝ, 4 * fA D * (w.N : ℝ) ^ 2 ≤ B → ∀ c,
    X.meanU c ≤ Cu * fA D * jpA w * (Real.log (B * rd) + Lchi)

def PushDownProp (PPf : Pol D.what₂.Tau w.N →ₗ[ℝ] ℝ) (cf B : ℝ) : Prop :=
  PPf (FA w cf) = cf * X.fdeg * ∑ c, X.arLim B c ∧
    (∀ c, cf * X.fdeg * X.degMu c = U.cx.volC c * JA w cf) ∧ ∀ c, 0 < X.degMu c

def PolarTie (h : w.Indef) (lev : Finset ℕ) (hlev : ∀ p ∈ lev, p.Prime) (B : ℝ)
    (PPf : Pol D.what₂.Tau w.N →ₗ[ℝ] ℝ) : Prop :=
  (∀ (P : Pol D.what₂.Tau w.N) (d : ℕ), d ≠ WeightThresholdDefs.dimY (YU U h lev hlev) + 1 → P.IsHomogeneous d → PPf P = 0) ∧
    ∀ lam : Wts w, PPf (Formalism.DegreeFormula.linRoot lam ^ (WeightThresholdDefs.dimY (YU U h lev hlev) + 1)) = product_first_partition.PB (YU U h lev hlev) B lam

def GrassmannianHeightBound (E : ExtThmB U) (cf : ℝ) : Prop :=
  0 < JA w cf → ∀ e : ℝ, (∀ Z : Matrix (Fin (w.N - w.j)) (Fin w.j) ℂ, (∀ a b, ‖Z a b‖ = 1) →
      1 / 2 * Real.log (Matrix.det (1 + Z * Z.conjTranspose)).re ≤ e) →
    E.hFl (FA w cf) ≤ ((nA w : ℝ) + 1) * JA w cf * (fA D * e)

end Props

section Assembly

variable (U : ShimU D G jC ng w)

def SlopeLowerBoundFromPluckerHeights : Prop :=
  ∀ (X : ExtensionData U) (PPf : Pol D.what₂.Tau w.N →ₗ[ℝ] ℝ) (cf B rd Lchi Ch Cu K : ℝ),
    0 < Fintype.card D.what₂.Tau → 1 ≤ w.N - w.j → 3 * (w.N - w.j) + 1 ≤ w.N →
    4 * fA D * (w.N : ℝ) ^ 2 ≤ B → 1 ≤ rd → 0 ≤ Lchi → 0 ≤ Ch → 0 ≤ Cu → 0 < JA w cf →
    ZhangLowerXProp U X → DimXProp U X → CuspBundlePosProp U X → HtInteriorProp U X Ch K rd Lchi →
    HtBoundaryProp U X Ch K rd Lchi → StokesLimitProp U X K → CuspMeanProp U X Cu rd Lchi →
    PushDownProp U X PPf cf B →
    -(((nA w : ℝ) + 1) * U.cx.vol * JA w cf *
        ((Ch + Cu / 2) * fA D * jpA w * (Real.log (B * rd) + Lchi))) ≤ PPf (FA w cf)

open Classical in

def LowerBoundOnShimura : Prop :=
  ∀ (h : w.Indef) (lev : Finset ℕ) (hlev : ∀ p ∈ lev, p.Prime) (E : ExtThmB U) (X : ExtensionData U)
    (PPf : Pol D.what₂.Tau w.N →ₗ[ℝ] ℝ) (rest : Pol D.what₂.Tau w.N → ℝ) (A0 b0 : D.what₂.Tau → ℝ)
    (cf B0 rd Lchi Ch Cu K K1 : ℝ) (Q : Pol D.what₂.Tau w.N) (Qd : D.what₂.Tau → ℕ → Pol D.what₂.Tau w.N)
    (Pr : ℕ → Finset ℕ) (rp : ℕ → ℝ),

    LargestBlockVandermondeVanishes → TotalDerivativeValue → TestPolynomialHomogeneous → FlagIntegralAnnihilatesPowerSums → RestTermBound → PrimeSumBound → RestBoundFromPrimeSum →
    CauchyBinetHadamard → LowerBoundFromTermBounds → SlopeLowerBoundFromPluckerHeights U →

    0 < Fintype.card D.what₂.Tau → 1 ≤ w.N - w.j → 3 * (w.N - w.j) + 1 ≤ w.N →
    4 * fA D * (w.N : ℝ) ^ 2 ≤ B0 → 1 ≤ rd → 0 ≤ Lchi → 0 ≤ K1 → 0 ≤ Ch → 0 ≤ Cu → 0 < JA w cf →

    PolarTie U h lev hlev B0 PPf →
    (∀ F : Pol D.what₂.Tau w.N, F.IsHomogeneous (Formalism.DegreeFormula.dimFl D.what₂.Tau w.N + 1) →
      PPf F = U.cx.vol * (E.hFl F - (∑ τ, A0 τ * Sh (degFlL D.what₂.Tau w.N) w.j τ F)
        - (∑ τ, b0 τ * Tot (degFlL D.what₂.Tau w.N) τ F)) + rest F) →

    Q.IsHomogeneous (Formalism.DegreeFormula.dimFl D.what₂.Tau w.N) → degFlL D.what₂.Tau w.N Q = 1 →
    (∀ τ, E.hFl (psumAt τ 1 * Q) = 0) → (∀ τ, rest (psumAt τ 1 * Q) = 0) →
    (∀ τ, |PPf (psumAt τ 1 * Q)| ≤ U.cx.vol * (K1 * (w.N : ℝ) * (Real.log (B0 * rd) + Lchi))) →

    (∀ τ σ, A0 τ = A0 σ) →

    FA w cf = ∑ σ, ∑ k ∈ Icc 1 w.N, psumAt σ k * Qd σ k →
    (∀ B, ∀ p ∈ Pr B, p.Prime ∧ B0 < p) →
    (∀ B, ∀ p ∈ Pr B, TwistShapeProp w.j (degFlL D.what₂.Tau w.N) U.cx.vol p Qd (rp p)) →
    Tendsto (fun B => ∑ p ∈ Pr B, rp p) atTop (𝓝 (rest (FA w cf))) →

    ZhangLowerXProp U X → DimXProp U X → CuspBundlePosProp U X → HtInteriorProp U X Ch K rd Lchi →
    HtBoundaryProp U X Ch K rd Lchi → StokesLimitProp U X K → CuspMeanProp U X Cu rd Lchi →
    PushDownProp U X PPf cf B0 → GrassmannianHeightBound U E cf →
    LowerBoundHypothesis A0 (2 * K1 + 2 * Ch + Cu + 21 / 5) (Real.log (B0 * rd) + Lchi)

end Assembly

theorem threeLe_of_params {L : SizeData₂ D} (P : ParameterChoice' D L) (w : Dat D Lev) (i : ℕ) (hi : 1 ≤ i)
    (hN : w.N = D.R.r) (hj : w.j = (D.R.sigW i).1) : 3 * (w.N - w.j) + 1 ≤ w.N := by
  have h := P.three_q_le i hi
  have hm := D.R.two_le_m
  rw [hN, hj]
  unfold Ranks.sigW Ranks.r at *
  simp only at *
  omega

end Geo

end Formalism.L2.Geo
