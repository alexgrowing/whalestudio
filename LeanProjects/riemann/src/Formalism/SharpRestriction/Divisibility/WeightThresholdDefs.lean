import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.DataDIV
import Formalism.SharpRestriction.Divisibility.LatticeTransfer
import Formalism.SharpRestriction.Divisibility.PrinLevClass
import Formalism.SharpRestriction.ParamsHeightRankConstant

noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.WeightThresholdDefs

open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.DegreeFormula

open Classical

def dE (D : D7) : ℕ := (NumberField.discr D.host.E).natAbs

abbrev HS (D : D7) : Type 1 := letI := D.host.cmStar; Formalism.BasicNotions.HSpace D.host.E

section Derived
variable {D : D7} (Y : ShimX D.what₂.Tau)

abbrev dimY : ℕ := dimFl D.what₂.Tau Y.N

def jS : ℕ := min Y.j (Y.N - Y.j)

def inSmall (i : Fin Y.N) : Prop := if Y.j ≤ Y.N - Y.j then (i : ℕ) < Y.j else Y.j ≤ (i : ℕ)

def Dominant (lam : D.what₂.Tau → Fin Y.N → ℝ) : Prop :=
  ∀ τ (a b : Fin Y.N), a ≤ b → lam τ b ≤ lam τ a

def gap (lam : D.what₂.Tau → Fin Y.N → ℝ) (τ : D.what₂.Tau) : ℝ :=
  lam τ ⟨Y.j - 1, by have := Y.j_lt; omega⟩ - lam τ ⟨Y.j, Y.j_lt⟩

def supAbs (lam : D.what₂.Tau → Fin Y.N → ℝ) : ℝ := ⨆ x : Rt D.what₂.Tau Y.N, |lam x.1 x.2|

def WeightHyp (u : D.what₂.Tau → Fin Y.N → ℝ) (g : ℝ) : Prop :=
  0 < g ∧ (∀ τ (a b : Fin Y.N), a < b → u τ b < u τ a) ∧ (∀ τ, g ≤ gap Y u τ) ∧
  (∀ τ (a b : Fin Y.N), inSmall Y a → a ≠ b → g ≤ |u τ a - u τ b|)

def bigB0 (u : D.what₂.Tau → Fin Y.N → ℝ) (g : ℝ) : ℝ :=
  4 * (D.R.f : ℝ) * (Y.N : ℝ) ^ 2 * (1 + supAbs Y u / g)

def geoDeg (lam : D.what₂.Tau → Fin Y.N → ℝ) : ℝ := Y.chern (linRoot lam ^ dimY Y)

def NefHT (p : ℕ) (lam : D.what₂.Tau → Fin Y.N → ℝ) : Prop :=
  ∀ c : Y.CurveHT p, 0 ≤ -∑ x : Rt D.what₂.Tau Y.N, lam x.1 x.2 * Y.degHT p c x

def NefDR (p : ℕ) (lam : D.what₂.Tau → Fin Y.N → ℝ) : Prop :=
  ∀ c : Y.CurveDR p, 0 ≤ -∑ x : Rt D.what₂.Tau Y.N, lam x.1 x.2 * Y.degDR p c x

end Derived

def cP (p : ℕ) : ℝ := 1 / ((p : ℝ) - 1)

variable {D : D7} (V : DivX D) (P : DIV.Align.PrinLev V)

def NefM {S : HS D} {κ : V.Lev} {p : ℕ} [Fact p.Prime] {la : V.PlP p} (z : V.Mp S κ p la)
    (lam : D.what₂.Tau → Fin (V.shv S κ).N → ℝ) : Prop :=
  ∀ c : V.CurveM S κ p la z, 0 ≤ -∑ x : Rt D.what₂.Tau (V.shv S κ).N, lam x.1 x.2 * V.degM S κ p la z c x

def FlagTriv {S : HS D} {κ : V.Lev} {p : ℕ} [Fact p.Prime] {la : V.PlP p} (z : V.Mp S κ p la) : Prop :=
  (∀ (τ : Emb D p) (k : ℕ), 1 ≤ k → ∀ (E : (V.md S κ p la z).Z.VDiv) (a : (V.md S κ p la z).Z.Ch),
    (V.md S κ p la z).Z.capDeg E
      (((∑ i, (V.md S κ p la z).Z.c1 (((V.md S κ p la z).lie τ).x' i) ^ k) +
        ∑ i, (V.md S κ p la z).Z.c1 (((V.md S κ p la z).om τ).x' i) ^ k) * a) = 0) ∧
  ∀ k : ℕ, 1 ≤ k → ∀ (E : (V.md S κ p la z).Z.VDiv) (a : (V.md S κ p la z).Z.Ch),
    (V.md S κ p la z).Z.capDeg E
      (((∑ i, (V.md S κ p la z).Z.c1 ((V.md S κ p la z).lieW.x' i) ^ k) +
        ∑ i, (V.md S κ p la z).Z.c1 ((V.md S κ p la z).omW.x' i) ^ k) * a) = 0

def r0 : ℝ := -((deriv riemannZeta (-1) / riemannZeta (-1)).re + 1 / 2)

def adm7 : Prop := ∀ t : V.Surf,
  (∃ q : ℚ, 2 * V.surfCh2 t - r0 * V.surfDegOm t = q * Real.log 2) ∧
  (∃ q : ℚ, 2 * V.surfCh2 t - r0 * V.surfDegOm t = q * Real.log 3)

def adm9 : Prop := LatticeTransfer.PointsLemma D V P

def adm10 : Prop := ∀ S κ, HidaSetting D V S κ →
  ∀ Q, (V.shv S κ).chern Q = (V.shv S κ).vol * degFl D.what₂.Tau (V.shv S κ).N Q

def admitted : Prop := adm7 V ∧ adm9 V P ∧ adm10 V

def Conclusion0 : Prop := ∀ S κ, HidaSetting D V S κ → DIV.Align.LevB P κ → ∀ p : ℕ, p.Prime →
  ∀ c : (V.shv S κ).FibComp p, ¬ (V.shv S κ).fibInBd p c

def Conclusion1 : Prop := ∀ S κ, HidaSetting D V S κ → DIV.Align.LevB P κ →
  (∀ (p : ℕ) [Fact p.Prime] (la : V.PlP p), ∃ n0 : ℕ, (p ∉ (V.shv S κ).lev → n0 = 0) ∧
    ∀ n : ℕ, n0 ≤ n → 1 + cP p < (n : ℝ) → ∃ z : V.Mp S κ p la, (V.md S κ p la z).lvl = n) ∧
  ∀ (p : ℕ) [Fact p.Prime] (la : V.PlP p) (z : V.Mp S κ p la),
    FlagTriv V z ∧ ∀ lam, Dominant (V.shv S κ) lam → NefM V z lam

def NefHodgeTateLattices : Prop := ∀ S κ, HidaSetting D V S κ → DIV.Align.LevB P κ → ∀ p : ℕ, p.Prime →
  ∀ lam, Dominant (V.shv S κ) lam → NefHT (V.shv S κ) p lam

def TrivialFlagIntersectionCond : Prop := ∀ S κ, HidaSetting D V S κ → DIV.Align.LevB P κ → ∀ (Sx : Finset ℕ) (R : ℝ) (p : ℕ), p.Prime →
  ∀ (τ : D.what₂.Tau) (k : ℕ), 1 ≤ k → ∀ Q : MvPolynomial (Rt D.what₂.Tau (V.shv S κ).N) ℝ,
    (V.shv S κ).arMix Sx R p (tagHT D.what₂.Tau _ (pk D _ τ k) *
      (tagDR D.what₂.Tau _ Q - tagHT D.what₂.Tau _ Q)) = 0

def LogarithmicExponentBound (C1 : ℝ) : Prop := ∀ S κ, HidaSetting D V S κ → DIV.Align.LevB P κ → ∀ p : ℕ, p.Prime → UnramE D p →
  ∀ (y : (V.shv S κ).Pt) (lam : D.what₂.Tau → Fin (V.shv S κ).N → ℝ),
    |∑ x : Rt D.what₂.Tau (V.shv S κ).N, lam x.1 x.2 * (V.shv S κ).phiDR p y x| ≤
      C1 * D.R.f * (V.shv S κ).N * supAbs (V.shv S κ) lam * Real.log p / ((p : ℝ) - 1)

def ExponentBlockSplitting : Prop := ∀ S κ, HidaSetting D V S κ → DIV.Align.LevB P κ → ∃ C : ℝ, ∀ p : ℕ, p.Prime → p ∣ dE D →
  ∀ (y : (V.shv S κ).Pt) (lam : D.what₂.Tau → Fin (V.shv S κ).N → ℝ),
    |∑ x : Rt D.what₂.Tau (V.shv S κ).N, lam x.1 x.2 * (V.shv S κ).phiMod p y x| ≤
      C * supAbs (V.shv S κ) lam

def proposition_eleven_one_at_scale : Prop := ∀ S κ, HidaSetting D V S κ → DIV.Align.LevB P κ → ∀ p : ℕ, p.Prime →
  ∀ (y : (V.shv S κ).Pt) (lam : D.what₂.Tau → Fin (V.shv S κ).N → ℝ),
    |∑ x : Rt D.what₂.Tau (V.shv S κ).N, lam x.1 x.2 * (V.shv S κ).phiFr p y x| ≤
      Real.log p * ∑ τ, (cP p * ∑ i, |lam τ i| +
        V.vdd p τ * |∑ i ∈ univ.filter (fun i : Fin (V.shv S κ).N => (i : ℕ) < (V.shv S κ).j),
          lam τ i|)

def Conclusion2 : Prop := ∀ S κ, HidaSetting D V S κ → DIV.Align.LevB P κ → ∀ p : ℕ, p.Prime → ¬ p ∣ 2 * dE D →
  p ∉ (V.shv S κ).lev → ∀ mu, Dominant (V.shv S κ) mu →
    4 * (D.R.f : ℝ) * supAbs (V.shv S κ) mu ≤ ((p : ℝ) - 2) * (⨅ τ, gap (V.shv S κ) mu τ) →
    NefDR (V.shv S κ) p mu

def Conclusion4a (r : ℝ) : Prop := ∀ S : V.Surf, V.surfCh2 S = r / 2 * V.surfDegOm S

def Conclusion4b : Prop := ∀ S : V.SurfFp, V.surfFpCh2 S = 0

def Conclusion4 (r : ℝ) : Prop := Conclusion4a V r ∧ Conclusion4b V

def Conclusion5 (C5 : ℝ) : Prop := ∀ S κ, HidaSetting D V S κ → DIV.Align.LevB P κ → ∀ u g, WeightHyp (V.shv S κ) u g →
  ∀ Qs : D.what₂.Tau → ℕ → MvPolynomial (Rt D.what₂.Tau (V.shv S κ).N) ℝ,
    (∀ τ k, 1 ≤ k → k ≤ (V.shv S κ).N → (Qs τ k).IsHomogeneous (dimY (V.shv S κ) + 1 - k)) →
    linRoot u ^ (dimY (V.shv S κ) + 1) =
      ∑ τ, ∑ k ∈ Finset.Icc 1 (V.shv S κ).N, pk D _ τ k * Qs τ k →
    ∀ B : ℕ, (∑ p ∈ (Finset.range (B + 1)).filter (fun p : ℕ => p.Prime ∧
        bigB0 (V.shv S κ) u g < (p : ℝ) ∧ ¬ p ∣ 2 * dE D ∧ p ∉ (V.shv S κ).lev),
      Real.log p * ∑ τ, ∑ k ∈ Finset.Icc 2 (V.shv S κ).N, ∑' n : ℕ,
        |(Nat.factorial k : ℝ) * ((p : ℝ) ^ k)⁻¹ ^ (n + 1) *
          (V.shv S κ).chern (chLie (V.shv S κ).j (k - 1) (frobEmb D p (n + 1) (Sum.inl τ)) *
            Qs τ k) / (((dimY (V.shv S κ) : ℝ) + 1) * geoDeg (V.shv S κ) u)|) ≤
    C5 * jS (V.shv S κ) * ∑ τ, ((⨆ i, u τ i) - ⨅ i, u τ i)

def WeakPrimewiseProportionality (C5 : ℝ) : Prop := ∀ S κ, HidaSetting D V S κ → DIV.Align.LevB P κ → ∀ u g, WeightHyp (V.shv S κ) u g →
  ∀ Qs : D.what₂.Tau → ℕ → MvPolynomial (Rt D.what₂.Tau (V.shv S κ).N) ℝ,
    (∀ τ k, 1 ≤ k → k ≤ (V.shv S κ).N → (Qs τ k).IsHomogeneous (dimY (V.shv S κ) + 1 - k)) →
    linRoot u ^ (dimY (V.shv S κ) + 1) =
      ∑ τ, ∑ k ∈ Finset.Icc 1 (V.shv S κ).N, pk D _ τ k * Qs τ k →
    ∀ B : ℕ, (∑ p ∈ (Finset.range (B + 1)).filter (fun p : ℕ => p.Prime ∧
        bigB0 (V.shv S κ) u g < (p : ℝ) ∧ ¬ p ∣ 2 * dE D ∧ p ∉ (V.shv S κ).lev),
      |Real.log p * (∑ τ, ∑ k ∈ Finset.Icc 2 (V.shv S κ).N, (Nat.factorial k : ℝ) *
        ∑' n : ℕ, ((p : ℝ) ^ k)⁻¹ ^ (n + 1) *
          (V.shv S κ).chern (chLie (V.shv S κ).j (k - 1) (frobEmb D p (n + 1) (Sum.inl τ)) *
            Qs τ k)) / (((dimY (V.shv S κ) : ℝ) + 1) * geoDeg (V.shv S κ) u)|) ≤
    C5 * jS (V.shv S κ) * ∑ τ, ((⨆ i, u τ i) - ⨅ i, u τ i)

structure Loc4 where

  dRho : V.Surf → ℕ
  dRho_pos : ∀ t, 0 < dRho t

  CHr : V.Surf → Type
  instCHr : ∀ t, AddCommGroup (CHr t)

  ch2 : ∀ t, CHr t

  ch2o : ∀ t, CHr t

  arithFirstChernHom : ∀ t, ℝ →+ CHr t

  degA : ∀ t, CHr t →+ ℝ

attribute [instance] Loc4.instCHr

def ArithmeticRiemannRochThetaCond (B : Loc4 V) (r : ℝ) : Prop :=
  ∀ t, B.ch2o t = B.arithFirstChernHom t (r - Real.log (2 * Real.pi))

def RescaledMetricChernCond (B : Loc4 V) : Prop :=
  ∀ t, B.ch2 t = B.ch2o t + B.arithFirstChernHom t (Real.log (2 * Real.pi))

def ArithmeticDegreePullbackCond (B : Loc4 V) : Prop :=
  ∀ t, B.degA t (B.ch2 t) = (B.dRho t : ℝ) * V.surfCh2 t ∧
    ∀ s : ℝ, B.degA t (B.arithFirstChernHom t s) = s / 2 * ((B.dRho t : ℝ) * V.surfDegOm t)

def Adm4 (B : Loc4 V) (r : ℝ) : Prop := ArithmeticRiemannRochThetaCond V B r ∧ RescaledMetricChernCond V B ∧ ArithmeticDegreePullbackCond V B

def ThetaChernBoundOfInputs (B : Loc4 V) (r : ℝ) : Prop := Adm4 V B r → Conclusion4a V r

def GeometricClausesWithBound (C1 : ℝ) : Prop :=
  Conclusion0 V P ∧ Conclusion1 V P ∧ NefHodgeTateLattices V P ∧ TrivialFlagIntersectionCond V P ∧ LogarithmicExponentBound V P C1 ∧ ExponentBlockSplitting V P ∧ proposition_eleven_one_at_scale V P ∧ Conclusion2 V P ∧ Conclusion4b V

def GeometricClausesDerivable : Prop :=
  Conclusion0 V P ∧ Conclusion1 V P ∧ TrivialFlagIntersectionCond V P ∧ ExponentBlockSplitting V P ∧ proposition_eleven_one_at_scale V P ∧ Conclusion2 V P ∧ Conclusion4b V

def ThetaChernBoundOfLastLine : Prop := adm7 V → Conclusion4a V r0

def GGFromIrreducibility (C5 : ℝ) : Prop := adm10 V → Conclusion5 V P C5

def LastRelationsAlgebra : Prop :=
  (Conclusion1 V P → NefHodgeTateLattices V P) ∧ (proposition_eleven_one_at_scale V P → LogarithmicExponentBound V P 1) ∧ ∀ C5, Conclusion5 V P C5 → WeakPrimewiseProportionality V P C5

def AllButProportionality (C1 : ℝ) : Prop :=
  adm7 V → Conclusion0 V P ∧ Conclusion1 V P ∧ NefHodgeTateLattices V P ∧ TrivialFlagIntersectionCond V P ∧ LogarithmicExponentBound V P C1 ∧ ExponentBlockSplitting V P ∧ proposition_eleven_one_at_scale V P ∧ Conclusion2 V P ∧ Conclusion4 V r0

def AllButProportionalityParam (C1 r : ℝ) (B : Loc4 V) : Prop :=
  Adm4 V B r → Conclusion0 V P ∧ Conclusion1 V P ∧ NefHodgeTateLattices V P ∧ TrivialFlagIntersectionCond V P ∧ LogarithmicExponentBound V P C1 ∧ ExponentBlockSplitting V P ∧ proposition_eleven_one_at_scale V P ∧ Conclusion2 V P ∧ Conclusion4 V r

def GeometricAllButProportionality (C1 r : ℝ) (B : Loc4 V) : Prop :=
  1 ≤ C1 → GeometricClausesDerivable V P → Adm4 V B r →
    Conclusion0 V P ∧ Conclusion1 V P ∧ NefHodgeTateLattices V P ∧ TrivialFlagIntersectionCond V P ∧ LogarithmicExponentBound V P C1 ∧ ExponentBlockSplitting V P ∧ proposition_eleven_one_at_scale V P ∧ Conclusion2 V P ∧ Conclusion4 V r

def PacketAbsoluteConstants (C1 r C5 : ℝ) (B : Loc4 V) : Prop :=
  Adm4 V B r ∧ adm9 V P ∧ adm10 V → Conclusion0 V P ∧ Conclusion1 V P ∧ NefHodgeTateLattices V P ∧ TrivialFlagIntersectionCond V P ∧ LogarithmicExponentBound V P C1 ∧ ExponentBlockSplitting V P ∧
    proposition_eleven_one_at_scale V P ∧ Conclusion2 V P ∧ Conclusion4 V r ∧ Conclusion5 V P C5

def Stmt (C1 C5 : ℝ) : Prop :=
  admitted V P → Conclusion0 V P ∧ Conclusion1 V P ∧ NefHodgeTateLattices V P ∧ TrivialFlagIntersectionCond V P ∧ LogarithmicExponentBound V P C1 ∧ ExponentBlockSplitting V P ∧ proposition_eleven_one_at_scale V P ∧ Conclusion2 V P ∧
    Conclusion4 V r0 ∧ Conclusion5 V P C5

section Fam
variable {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (PL : DIV.Align.PrinLevF Fm)

def adm7F : Prop := ∀ x, Fm.x1 < x → ∀ i : Fm.Ix x, adm7 (Fm.X x i)

def proportionalityInputFamily : Prop := ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), adm9 (Fm.X x i) (PL x hx i)

def compactDualInputFamily : Prop := ∀ x, Fm.x1 < x → ∀ i : Fm.Ix x, adm10 (Fm.X x i)

def AdmF : Prop := ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), admitted (Fm.X x i) (PL x hx i)

def familyAllButProportionality (C1 : ℝ) : Prop := ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x),
  Conclusion0 (Fm.X x i) (PL x hx i) ∧ Conclusion1 (Fm.X x i) (PL x hx i) ∧ NefHodgeTateLattices (Fm.X x i) (PL x hx i) ∧ TrivialFlagIntersectionCond (Fm.X x i) (PL x hx i) ∧
    LogarithmicExponentBound (Fm.X x i) (PL x hx i) C1 ∧ ExponentBlockSplitting (Fm.X x i) (PL x hx i) ∧ proposition_eleven_one_at_scale (Fm.X x i) (PL x hx i) ∧
    Conclusion2 (Fm.X x i) (PL x hx i) ∧ Conclusion4 (Fm.X x i) r0

def SlopeLossFamily (C5 : ℝ) : Prop := ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), Conclusion5 (Fm.X x i) (PL x hx i) C5

def OrbitValuationBound (C1 C5 : ℝ) : Prop := familyAllButProportionality Fm PL C1 ∧ SlopeLossFamily Fm PL C5

def FamilyAllButPropImpl (C1 : ℝ) : Prop := adm7F Fm → familyAllButProportionality Fm PL C1

def FamilyProportionality (C5 : ℝ) : Prop := compactDualInputFamily Fm → SlopeLossFamily Fm PL C5

def ProportionalityPointwise (C5 : ℝ) : Prop := ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), GGFromIrreducibility (Fm.X x i) (PL x hx i) C5

def KudlaFamilyStatement (C1 C5 : ℝ) : Prop := AdmF Fm PL → OrbitValuationBound Fm PL C1 C5

abbrev Loc4F : Type 1 := ∀ x (_ : Fm.x1 < x) (i : Fm.Ix x), Loc4 (Fm.X x i)

def Adm4F (BF : Loc4F Fm) (r : ℝ) : Prop := ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), Adm4 (Fm.X x i) (BF x hx i) r

def ThetaChernBoundFamily (BF : Loc4F Fm) (r : ℝ) : Prop :=
  Adm4F Fm BF r → ∀ x, Fm.x1 < x → ∀ i : Fm.Ix x, Conclusion4a (Fm.X x i) r

def familyAllButProportionalityParam (C1 r : ℝ) : Prop := ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x),
  Conclusion0 (Fm.X x i) (PL x hx i) ∧ Conclusion1 (Fm.X x i) (PL x hx i) ∧ NefHodgeTateLattices (Fm.X x i) (PL x hx i) ∧ TrivialFlagIntersectionCond (Fm.X x i) (PL x hx i) ∧
    LogarithmicExponentBound (Fm.X x i) (PL x hx i) C1 ∧ ExponentBlockSplitting (Fm.X x i) (PL x hx i) ∧ proposition_eleven_one_at_scale (Fm.X x i) (PL x hx i) ∧
    Conclusion2 (Fm.X x i) (PL x hx i) ∧ Conclusion4 (Fm.X x i) r

def familyAllClausesParam (C1 r C5 : ℝ) : Prop := familyAllButProportionalityParam Fm PL C1 r ∧ SlopeLossFamily Fm PL C5

def FamilyAllButPropParamImpl (C1 : ℝ) (BF : Loc4F Fm) (r : ℝ) : Prop := Adm4F Fm BF r → familyAllButProportionalityParam Fm PL C1 r

def GeoF : Prop := ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), GeometricClausesDerivable (Fm.X x i) (PL x hx i)

def FamilyGeometricAllButProp (C1 : ℝ) (BF : Loc4F Fm) (r : ℝ) : Prop :=
  1 ≤ C1 → GeoF Fm PL → Adm4F Fm BF r → familyAllButProportionalityParam Fm PL C1 r

def Adm4FT1 (r : ℝ) : Prop := ∀ x, Fm.x1 < x → ∀ i : Fm.Ix x, Conclusion4a (Fm.X x i) r

def FamilyAllClausesParam (C1 C5 : ℝ) (BF : Loc4F Fm) (r : ℝ) : Prop :=
  Adm4F Fm BF r ∧ proportionalityInputFamily Fm PL ∧ compactDualInputFamily Fm → familyAllClausesParam Fm PL C1 r C5

end Fam

def ClosedAllButProportionality (𝒞 : Formalism.MainNotions.FamClass) (𝒬 : DIV.Align.PrinLevClass) : Prop :=
  ∃ C1 : ℝ, Formalism.MainNotions.Closed 𝒞 (fun Fm _ => ∀ PL, 𝒬 Fm PL → FamilyAllButPropImpl Fm PL C1)

def ClosedProportionality (𝒞 : Formalism.MainNotions.FamClass) (𝒬 : DIV.Align.PrinLevClass) : Prop :=
  ∃ C5 : ℝ, Formalism.MainNotions.Closed 𝒞 (fun Fm _ => ∀ PL, 𝒬 Fm PL → FamilyProportionality Fm PL C5)

def ClosedAbsoluteShare (𝒞 : Formalism.MainNotions.FamClass) (𝒬 : DIV.Align.PrinLevClass) : Prop :=
  ∃ C1 C5 : ℝ, Formalism.MainNotions.Closed 𝒞 (fun Fm _ => ∀ PL, 𝒬 Fm PL → KudlaFamilyStatement Fm PL C1 C5)

def ClosedAllButPropParam (𝒞 : Formalism.MainNotions.FamClass) (𝒬 : DIV.Align.PrinLevClass)
    (BF : ∀ {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps), Loc4F Fm) : Prop :=
  ∃ C1 : ℝ, Formalism.MainNotions.Closed 𝒞 (fun Fm _ => ∀ PL, 𝒬 Fm PL → ∀ r : ℝ, FamilyAllButPropParamImpl Fm PL C1 (BF Fm) r)

def ClosedPacketAbsoluteConstants (𝒞 : Formalism.MainNotions.FamClass) (𝒬 : DIV.Align.PrinLevClass)
    (BF : ∀ {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps), Loc4F Fm) : Prop :=
  ∃ C1 C5 : ℝ, Formalism.MainNotions.Closed 𝒞 (fun Fm _ => ∀ PL, 𝒬 Fm PL → ∀ r : ℝ, FamilyAllClausesParam Fm PL C1 C5 (BF Fm) r)

def Adm4Closed (𝒞 : Formalism.MainNotions.FamClass) (BF : ∀ {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps), Loc4F Fm) : Prop :=
  ∃ r : ℝ, Formalism.MainNotions.Closed 𝒞 (fun Fm _ => Adm4F Fm (BF Fm) r)

end Formalism.MainNotions.WeightThresholdDefs

end
