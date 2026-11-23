import Mathlib
import Formalism.LocalRingCardinality.DataParams₂
import Formalism.SharpRestriction.Divisibility.WeightThresholdDefs
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLimDeg

open MvPolynomial Formalism.DegreeFormula Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions Formalism.MainNotions.WeightThresholdDefs Filter Topology Classical

noncomputable section

namespace GlobalTheory.Mean4

open GlobalTheory.FlagPoly GlobalTheory.FlagAr

def FlagHt (ι : Type) [Fintype ι] [DecidableEq ι] (N : ℕ) (hh : Pol ι N →ₗ[ℝ] ℝ) : Prop :=
  (∀ (j : ℕ) (τ : ι) (lam : ι → Fin N → ℝ), 1 ≤ j → j < N → Dom lam → GapZero j τ lam →
      hh (linRoot lam ^ (dimFl ι N + 1)) = 0) ∧
  (∀ lam : ι → Fin N → ℝ, Dom lam → 0 ≤ hh (linRoot lam ^ (dimFl ι N + 1))) ∧
  (∀ (τ : ι) (Q : Pol ι N), Q.IsHomogeneous (dimFl ι N) → hh (pSum τ 1 * Q) = 0) ∧
  ∀ (σ : Equiv.Perm ι) (F : Pol ι N), F.IsHomogeneous (dimFl ι N + 1) → hh (rename (Prod.map σ id) F) = hh F

variable {D : D7} (Y : ShimX D.what₂.Tau)

abbrev Wt : Type := D.what₂.Tau → Fin Y.N → ℝ

abbrev Fn : Type := Pol D.what₂.Tau Y.N →ₗ[ℝ] ℝ

structure SlopeTestRemainingChoices where

  dir : Wt Y

  w : Y.Comp → ℝ

  Ps : ℝ → Y.Comp → MvPolynomial (Option (D.what₂.Tau × Fin Y.N)) ℝ

  ht : Y.ALB → Y.Pt → ℝ

  dense : Y.Comp → Set Y.Pt → Prop

def IsRat (u : Wt Y) : Prop := ∀ τ i, ∃ q : ℚ, u τ i = (q : ℝ)

def CptGaps (c : ℝ) (u : Wt Y) : Prop :=
  ∀ τ (a b : Fin Y.N), (b : ℕ) = a + 1 → (b : ℕ) ≠ Y.j → c ≤ u τ a - u τ b

def NefCond (B : ℝ) (u : Wt Y) : Prop := ∀ τ, 4 * (D.R.f : ℝ) * supAbs Y u ≤ (B - 2) * gap Y u τ

def evS (P : MvPolynomial (Option (D.what₂.Tau × Fin Y.N)) ℝ) (u : Wt Y) (s : ℝ) : ℝ :=
  eval (fun o => o.elim s (fun x => u x.1 x.2)) P

def comb (Q : D.what₂.Tau → ℕ → Pol D.what₂.Tau Y.N) : Pol D.what₂.Tau Y.N :=
  ∑ τ, ∑ k ∈ Finset.Icc 1 Y.N, pSum τ k * Q τ k

def Cof (Q : D.what₂.Tau → ℕ → Pol D.what₂.Tau Y.N) : Prop :=
  ∀ τ k, 1 ≤ k → k ≤ Y.N → (Q τ k).IsHomogeneous (dimY Y + 1 - k)

def shAll (F : Pol D.what₂.Tau Y.N) : ℝ := ∑ τ, shF Y.j τ F

def totAll (F : Pol D.what₂.Tau Y.N) : ℝ := ∑ τ, totF τ F

def newPrimes (B₀ B : ℝ) : Finset ℕ := setB Y B \ setB Y B₀

def kap (p : ℕ) (τ : D.what₂.Tau) : ℝ :=
  ∑' n : ℕ, ((p : ℝ)⁻¹) ^ (n + 1) *
    (frobEmb D p (n + 1) (Sum.inl τ)).elim (fun _ => (Y.j : ℝ)) (fun _ => (Y.N : ℝ) - Y.j)

def restTerm (p : ℕ) (Q : D.what₂.Tau → ℕ → Pol D.what₂.Tau Y.N) : ℝ :=
  Real.log p * ∑ τ, ∑ k ∈ Finset.Icc 2 Y.N, (Nat.factorial k : ℝ) *
    ∑' n : ℕ, ((p : ℝ) ^ k)⁻¹ ^ (n + 1) * Y.chern (chLie Y.j (k - 1) (frobEmb D p (n + 1) (Sum.inl τ)) * Q τ k)

def testF : Pol D.what₂.Tau Y.N := ∑ τ, pSum τ 2 * curveCl D.what₂.Tau Y.N Y.j

def testI : ℝ := ∑ τ, degFl D.what₂.Tau Y.N (pLow Y.j τ 1 * curveCl D.what₂.Tau Y.N Y.j)

def offWall (τ₀ : D.what₂.Tau) (t : ℝ) (u : Wt Y) : Wt Y :=
  fun τ i => u τ i + if τ = τ₀ ∧ (i : ℕ) < Y.j then 2 * t else 0

def lg (D : D7) (B : ℝ) : ℝ := Real.log (B * D.host.rdE) + |dlogL D 1|

def Propor : Prop := ∀ Q, Y.chern Q = Y.vol * degFl D.what₂.Tau Y.N Q

def FewBad : Prop := Y.lev.card ≤ 15

variable {Y} (A : SlopeTestRemainingChoices Y) (Φ : ℝ → Fn Y) (hh : Fn Y)

def SlopeTestRemainingChoices.sh (u : Wt Y) (s : ℝ) : Wt Y := fun τ i => u τ i - s * A.dir τ i

def LimFam : Prop := ∀ B : ℝ, 2 ≤ B → IsLimDeg Y B (Φ B)

def PolySize : Prop := ∃ C : ℝ, ∀ B : ℝ, 2 ≤ B →
  (∀ c, (A.Ps B c).totalDegree ≤ dimY Y + 1 ∧ ∀ m, |(A.Ps B c).coeff m| ≤ C * Real.log B) ∧
  ∀ u : Wt Y, ∑ c, evS Y (A.Ps B c) u 0 = atWt Y (Φ B) u

def Agree : Prop := ∀ Λ : ℝ, ∃ s₀ : ℝ, 0 < s₀ ∧ ∃ C : ℝ, ∀ B : ℝ, 2 ≤ B → ∀ (u : Wt Y) (s : ℚ), IsRat Y u →
  supAbs Y u ≤ Λ → 0 < s → (s : ℝ) ≤ s₀ → Dominant Y (A.sh u s) →
  ∀ c, |Y.arSelfC (Y.Mbar B u s) c - evS Y (A.Ps B c) (A.sh u s) s| ≤ C * s

def Positive : Prop := ∀ Λ : ℝ, ∃ s₀ : ℝ, 0 < s₀ ∧ ∀ B : ℝ, 2 ≤ B → ∀ (u : Wt Y) (s : ℚ), IsRat Y u →
  supAbs Y u ≤ Λ → 0 < s → (s : ℝ) ≤ s₀ → Dominant Y (A.sh u s) → NefCond Y B (A.sh u s) →
  Y.semipos (Y.Mbar B u s) ∧ Y.nefFib (Y.Mbar B u s)

def Squeeze : Prop := ∀ L : Y.ALB, Y.semipos L → Y.nefFib L → ∀ (c : Y.Comp) (e : ℝ),
  ((∀ y, Y.compPt y = c → e ≤ A.ht L y) → ((dimY Y : ℝ) + 1) * e * Y.geoC L c ≤ Y.arSelfC L c) ∧
  ((∃ Z, A.dense c Z ∧ ∀ y ∈ Z, A.ht L y ≤ e) → Y.arSelfC L c ≤ ((dimY Y : ℝ) + 1) * e * Y.geoC L c)

def Heights : Prop := ∀ c₀ : ℝ, 0 < c₀ → ∃ t₀ : ℝ, 0 < t₀ ∧ ∃ C : ℝ, ∀ B : ℝ, 2 ≤ B → ∀ (u : Wt Y) (t : ℚ), IsRat Y u →
  supAbs Y u ≤ 1 → 0 < t → (t : ℝ) ≤ t₀ → (∀ τ, (t : ℝ) ≤ gap Y u τ) → CptGaps Y c₀ u →
  NefCond Y B (A.sh u ((t : ℝ) ^ 2)) →
  (∀ y, -(C * Real.log (B / (t : ℝ) ^ 2)) ≤ A.ht (Y.Mbar B u (t ^ 2)) y) ∧
  ∀ c, ∃ Z, A.dense c Z ∧ ∀ y ∈ Z, A.ht (Y.Mbar B u (t ^ 2)) y ≤ C * Real.log B

def Degrees : Prop := (∀ c, 0 < A.w c) ∧ Y.vol = ∑ c, A.w c ∧
  (∀ Λ : ℝ, ∃ s₀ : ℝ, 0 < s₀ ∧ ∀ B : ℝ, 2 ≤ B → ∀ (u : Wt Y) (s : ℚ), IsRat Y u → supAbs Y u ≤ Λ → 0 < s → (s : ℝ) ≤ s₀ →
    Dominant Y u → Dominant Y (A.sh u s) → ∀ c, 0 ≤ Y.geoC (Y.Mbar B u s) c ∧
      Y.geoC (Y.Mbar B u s) c ≤ A.w c * flagDeg D.what₂.Tau Y.N u) ∧
  ∀ B : ℝ, 2 ≤ B → ∀ u : Wt Y, IsRat Y u → ∀ c,
    Tendsto (fun s : ℚ => Y.geoC (Y.Mbar B u s) c) (𝓝[>] (0 : ℚ)) (𝓝 (A.w c * flagDeg D.what₂.Tau Y.N u))

def EqVol : Prop := ∀ c c', A.w c = A.w c'

def Antisym : Prop := ∀ B : ℝ, 2 ≤ B → ∀ (τ : D.what₂.Tau) (a b : Fin Y.N), (b : ℕ) = a + 1 → (b : ℕ) ≠ Y.j → ∀ u : Wt Y,
  atWt Y (Φ B) (fun σ i => u (swapAt τ a b (σ, i)).1 (swapAt τ a b (σ, i)).2) -
      Y.vol * atWt Y hh (fun σ i => u (swapAt τ a b (σ, i)).1 (swapAt τ a b (σ, i)).2) =
    -(atWt Y (Φ B) u - Y.vol * atWt Y hh u)

def Relabel : Prop := ∀ τ τ' : D.what₂.Tau, ∃ σ : Equiv.Perm D.what₂.Tau, σ τ = τ' ∧
  ∀ B : ℝ, 2 ≤ B → ∀ F : Pol D.what₂.Tau Y.N, Φ B (rename (Prod.map σ id) F) = Φ B F

def FlatVal : Prop := ∀ B : ℝ, 2 ≤ B → ∀ (τ : D.what₂.Tau) (Q : Pol D.what₂.Tau Y.N), Q.IsHomogeneous (dimY Y) →
  Φ B (pSum τ 1 * Q) = (∑ c, A.w c * Y.htDetT B c τ) * degFl D.what₂.Tau Y.N Q

variable (Y) in

def FlatBd (C : ℝ) : Prop := ∀ B : ℝ, 48 ≤ B → ∀ c τ, |Y.htDetT B c τ| ≤ C * Y.N * lg D B

def TestVal (r : ℝ) : Prop := ∀ B : ℝ, 2 ≤ B →
  Φ B (testF Y) = Y.vol * (hh (testF Y) - 2 * testI Y *
    (r - 1 / 2 - ∑ p ∈ setB Y B, (p : ℝ) * Real.log p / ((p : ℝ) ^ 2 - 1)))

def Inputs (r Cf : ℝ) : Prop :=
  LimFam Φ ∧ PolySize A Φ ∧ Agree A ∧ Positive A ∧ Squeeze A ∧ Heights A ∧ Degrees A ∧ EqVol A ∧ Antisym Φ hh ∧
  FlagHt D.what₂.Tau Y.N hh ∧ Relabel Φ ∧ FlatVal A Φ ∧ FlatBd Y Cf ∧ TestVal Φ hh r

def WallSmall : Prop := ∃ (C : ℝ) (B₁ : ℕ), ∀ B : ℕ, B₁ ≤ B → ∀ τ₀, ∀ u ∈ wallSet (N := Y.N) Y.j τ₀ (1 / (4 * (Y.N : ℝ))),
  IsRat Y u → ∀ t : ℚ, t = 5 * (D.R.f : ℚ) / B →
    Dominant Y (A.sh (offWall Y τ₀ t u) ((t : ℝ) ^ 2)) ∧
    |Y.arSelf (Y.Mbar B (offWall Y τ₀ t u) (t ^ 2))| ≤ C * Real.log B / B

def WallBd : Prop := ∃ (C : ℝ) (B₁ : ℕ), ∀ B : ℕ, B₁ ≤ B → ∀ τ₀, ∀ u ∈ wallSet (N := Y.N) Y.j τ₀ (1 / (4 * (Y.N : ℝ))),
  |atWt Y (Φ B) u| ≤ C * Real.log B / B

def ShapeT : Prop := ∃ (C : ℝ) (B₁ : ℕ), ∀ B : ℕ, B₁ ≤ B → ∃ (al be : D.what₂.Tau → ℝ) (E : Pol D.what₂.Tau Y.N),
  E.IsHomogeneous (dimY Y + 1) ∧ CoefLe E (C * Real.log B / B) ∧ ∀ u : Wt Y, atWt Y (Φ B) u =
    Y.vol * (atWt Y hh u + ((dimY Y : ℝ) + 1) * flagDeg D.what₂.Tau Y.N u * ev u (invForm Y.j al be)) + ev u E

def ShapeC : Prop := ∃ (C : ℝ) (B₁ : ℕ), ∀ B : ℕ, B₁ ≤ B → ∃ (al be : ℝ) (E : Pol D.what₂.Tau Y.N),
  E.IsHomogeneous (dimY Y + 1) ∧ CoefLe E (C * Real.log B / B) ∧ ∀ u : Wt Y, atWt Y (Φ B) u =
    Y.vol * (atWt Y hh u + ((dimY Y : ℝ) + 1) * flagDeg D.what₂.Tau Y.N u *
      ev u (invForm Y.j (fun _ => al) (fun _ => be))) + ev u E

def ShapeF : Prop := ∃ a b : ℕ → ℝ, ∀ F : Pol D.what₂.Tau Y.N, F.IsHomogeneous (dimY Y + 1) →
  Tendsto (fun B : ℕ => Φ B F - Y.vol * (hh F - a B * shAll Y F - b B * totAll Y F)) atTop (𝓝 0)

def Change : Prop := ∀ B₀ B : ℝ, 2 ≤ B₀ → B₀ ≤ B → ∀ Q, Cof Y Q →
  Φ B₀ (comb Y Q) = Φ B (comb Y Q) + ∑ p ∈ newPrimes Y B₀ B,
    (-(Real.log p / ((p : ℝ) - 1)) * Y.vol * shAll Y (comb Y Q) +
      Real.log p / Y.N * Y.vol * (∑ τ, kap Y p τ * totF τ (comb Y Q)) + restTerm Y p Q)

def ExactAt (B₀ a b : ℝ) : Prop := ∀ Q, Cof Y Q →
  Tendsto (fun B : ℕ => ∑ p ∈ newPrimes Y B₀ B, restTerm Y p Q) atTop
    (𝓝 (Φ B₀ (comb Y Q) - Y.vol * (hh (comb Y Q) - a * shAll Y (comb Y Q) - b * totAll Y (comb Y Q))))

def Lower (C : ℝ) : Prop := ∀ (u : Wt Y) (g : ℝ), WeightHyp Y u g →
  -(C * ((dimY Y : ℝ) + 1) * geoDeg Y u *
      (lg D (bigB0 Y u g) * (∑ τ, ∑ i, |u τ i|) + (jS Y : ℝ) * ∑ τ, ((⨆ i, u τ i) - ⨅ i, u τ i))) ≤
    atWt Y (Φ (bigB0 Y u g)) u

end GlobalTheory.Mean4
