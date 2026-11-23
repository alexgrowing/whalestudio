import Formalism.SharpRestriction.GlobalSchurBounds.ShortIntervalPrimes
import Formalism.SharpRestriction.GlobalSchurBounds.Chosen
import Formalism.LocalToGlobal.UnitaryNorms.MemFIffReal
import Formalism.SizeWindowBrackets.SmoothedRemainderRealIntegralFormula
import Formalism.GL3MeanSquares.SecondEstimateOfIntervalHypothesis

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.FiltrationCocycleLiftCriterion

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory Formalism.MainNotions.ShortIntervalPrimes NumberField

def QDGood (eps C x : ℝ) (q d : ℕ) : Prop :=
  ∃ (_ : Fact q.Prime) (_ : Fact d.Prime), Formalism.LFunctionChainParameters.LBr2.PrimePairBounds eps C x q d

def QDExists (eps C x : ℝ) : Prop := ∃ q : ℕ, ∃ d : ℕ, QDGood eps C x q d

open Classical in

def qSel (eps C x : ℝ) : ℕ :=
  if h : ∃ q : ℕ, ∃ d : ℕ, QDGood eps C x q d then Nat.find h else 0

open Classical in

def dSel (eps C x : ℝ) : ℕ :=
  if h : ∃ d : ℕ, QDGood eps C x (qSel eps C x) d then Nat.find h else 0

def QDTied (D : D7) (x eps C : ℝ) : Prop :=
  D.host.q = qSel eps C x ∧ D.host.d = dSel eps C x

def realTw (D : D7) : Set (ℕ → ℂ) :=
  {f | ∃ (N : ℕ) (χ : DirichletCharacter ℂ N), IsCharED D χ ∧ IsRealChar χ ∧ N ∣ D.host.QS ∧ f = fun a : ℕ => χ (a : ZMod N)}

def TwBox (B : ℕ) (Θ : Set (ℕ → ℂ)) (eps x : ℝ) (q d : ℕ) : Prop :=
  ∀ θ ∈ Θ, GoodAll (8 * (B : ℝ) * X1 x eps) (fun a => θ a * psDir q a) (8 * B * q * d) ∧
    GoodAll (8 * (B : ℝ) * X1 x eps * X2 x eps) (fun a => θ a * chDir d a) (8 * B * q * d) ∧
    GoodAll (8 * (B : ℝ) * X1 x eps * X2 x eps) (fun a => θ a * chDir d a * psDir q a) (8 * B * q * d)

def QDGoodH (B : ℕ) (Θ : Set (ℕ → ℂ)) (eps C x : ℝ) (q d : ℕ) : Prop :=
  QDGood eps C x q d ∧ TwBox B Θ eps x q d ∧ Nat.Coprime B (q * d) ∧
    ∀ l : ℕ, l.Prime → l ≠ 2 → l ∣ B → jacobiSym (-(d : ℤ)) l = 1

def QDExistsH (B : ℕ) (Θ : Set (ℕ → ℂ)) (eps C x : ℝ) : Prop := ∃ q : ℕ, ∃ d : ℕ, QDGoodH B Θ eps C x q d

open Classical in

def qSelH (B : ℕ) (Θ : Set (ℕ → ℂ)) (eps C x : ℝ) : ℕ :=
  if h : ∃ q : ℕ, ∃ d : ℕ, QDGoodH B Θ eps C x q d then Nat.find h else 0

open Classical in

def dSelH (B : ℕ) (Θ : Set (ℕ → ℂ)) (eps C x : ℝ) : ℕ :=
  if h : ∃ d : ℕ, QDGoodH B Θ eps C x (qSelH B Θ eps C x) d then Nat.find h else 0

def QDTiedH (D : D7) (x eps C : ℝ) : Prop :=
  D.host.q = qSelH (oddQS D) (realTw D) eps C x ∧ D.host.d = dSelH (oddQS D) (realTw D) eps C x

def Yg (D : D7) (x eps : ℝ) : ℝ := ((D.R.k : ℝ) * Real.exp (x ^ eps)) ^ 8

def GPair (D : D7) (x eps : ℝ) (g1 g2 : ℕ) : Prop :=
  g1.Prime ∧ g2.Prime ∧ g1 ≠ g2 ∧
    Formalism.HermitianLattices.ZeroFreeRegionGL2.IsNormOne D.host.d (NE D) g1 ∧ Formalism.HermitianLattices.ZeroFreeRegionGL2.IsNormOne D.host.d (NE D) g2 ∧
    Yg D x eps ≤ (g1 : ℝ) ∧ (g1 : ℝ) ≤ 2 * Yg D x eps ∧ Yg D x eps ≤ (g2 : ℝ) ∧ (g2 : ℝ) ≤ 2 * Yg D x eps ∧
    Disjoint (BB D.R.r g1) (BB D.R.r g2)

def GExists (D : D7) (x eps : ℝ) : Prop := ∃ g1 : ℕ, ∃ g2 : ℕ, GPair D x eps g1 g2

open Classical in

def chosenFirstPrime (D : D7) (x eps : ℝ) : ℕ :=
  if h : ∃ g1 : ℕ, ∃ g2 : ℕ, GPair D x eps g1 g2 then Nat.find h else 0

open Classical in

def chosenSecondPrime (D : D7) (x eps : ℝ) : ℕ :=
  if h : ∃ g2 : ℕ, GPair D x eps (chosenFirstPrime D x eps) g2 then Nat.find h else 0

def GTied (D : D7) (x eps : ℝ) : Prop :=
  D.host.g 0 = chosenFirstPrime D x eps ∧ D.host.g 1 = chosenSecondPrime D x eps

def TGood (D : D7) (u : D.what₂.Word) (T : ℕ) : Prop :=
  T.Prime ∧ Formalism.HermitianLattices.ZeroFreeRegionGL2.IsNormOne D.host.d (NE D * (D.host.g 0 * D.host.g 1) ^ 2) T ∧
    (D.mem u).A.Tstar ≤ (T : ℝ) ∧ (T : ℝ) ≤ (D.mem u).A.Tstar * (1 + 1 / ((D.R.f : ℝ) * D.R.k))

open Classical in

def TSel (D : D7) (u : D.what₂.Word) : ℕ := if h : ∃ T : ℕ, TGood D u T then Nat.find h else 0

def TTied (D : D7) : Prop := ∀ u, (D.mem u).A.T = TSel D u

def HostT (D : D7) : Prop := Nonempty (Formalism.L2.Host.HostTied D)

def CNF : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (d : ℕ), d.Prime → d % 4 = 3 → 3 < d → Module.finrank ℚ K = 2 →
    (∃ s : K, s ^ 2 = -(d : K)) →
    ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), Induces χ (chDir d) (2 * d) →
      ((classNumber K : ℕ) : ℂ) = ((Real.sqrt d : ℝ) : ℂ) * DirichletCharacter.LFunction χ 1 / (Real.pi : ℂ)

def CycSplit : Prop :=
  ∀ (N p : ℕ) (K : Type) [Field K] [NumberField K] [Algebra K (CyclotomicField N ℚ)], 0 < N → p.Prime →
    p % N = 1 % N →
    (Ideal.primesOver (Ideal.span {(p : ℤ)}) (𝓞 K)).ncard = Module.finrank ℚ K

def GL2LinkGoodPairPrimes : Prop :=
  ∀ eps C : ℝ, 0 < eps → eps < 1 / 52 → ∃ x0 : ℝ, ∀ x : ℝ, x0 ≤ x → ∀ D : D7,
    QDTied D x eps C → QDExists eps C x → (D.R.n : ℝ) ≤ x ^ (3 : ℝ) → BoxE D x eps → PrimesAsPropTwoFive D x eps C

def GL2LinkGoodPairTiedPrimes : Prop :=
  ∀ eps C : ℝ, 0 < eps → eps < 1 / 52 → ∃ x0 : ℝ, ∀ x : ℝ, x0 ≤ x → ∀ D : D7,
    QDTiedH D x eps C → QDExistsH (oddQS D) (realTw D) eps C x → (D.R.n : ℝ) ≤ x ^ (3 : ℝ) → PrimesAsPropTwoFive D x eps C

def GL2LinkGoodPair : Prop :=
  ∀ eps C : ℝ, 0 < eps → eps < 1 / 52 → ∃ x0 : ℝ, ∀ x : ℝ, x0 ≤ x → ∀ D : D7,
    QDExists eps C x → (D.R.n : ℝ) ≤ x ^ (3 : ℝ) → Conclusion5 D x eps C

def LinkExists5 : Prop :=
  ∀ eps : ℝ, 0 < eps → eps < 1 / 52 →
    ∀ c1 c5 C6 c6 C7 C11 C0 Cr cr cQ cT : ℝ, 0 < c1 → 0 < c5 → 0 < C6 → 0 < c6 → 0 < C7 → 0 < C11 → 0 < C0 →
      0 < Cr → 0 < cr → 0 < cQ → 0 < cT →
      ∃ C : ℝ, 0 < C ∧ ∃ x0 : ℝ, ∀ x : ℝ, x0 ≤ x → ∀ D : D7,
        adm1 D c1 → adm5 D c5 → adm6 D C6 c6 → adm7 D C7 → adm11 D C11 → adm8 D C0 Cr cr cQ cT →
        QDExists eps C x

def GL2LinkBoundedOddPart : Prop :=
  ∀ B : ℕ, ∃ c : ℝ, 0 < c ∧ ∀ eps : ℝ, 0 < eps → eps < 1 / 52 → ∃ x0 : ℝ, ∀ x : ℝ, x0 ≤ x → ∀ D : D7,
    oddQS D ≤ B → (D.R.n : ℝ) ≤ x ^ (3 : ℝ) → Conclusion6 D x eps c

def GL2LinkBoundedOddPartThinScales : Prop :=
  ∀ B : ℕ, ∃ c : ℝ, 0 < c ∧ ∀ eps : ℝ, 0 < eps → eps < 1 / 52 → ∃ x0 : ℝ, ∀ x : ℝ, x0 ≤ x → ∀ D : D7,
    oddQS D ≤ B → (D.R.n : ℝ) ≤ x ^ (3 : ℝ) → PropTwoSixThinScales D x eps c

def LinkQD : Prop :=
  ∀ eps C : ℝ, 0 < eps → eps < 1 / 52 → ∃ x0 : ℝ, ∀ x : ℝ, x0 ≤ x → ∀ D : D7,
    QDTied D x eps C → QDExists eps C x → (D.R.n : ℝ) ≤ x ^ (3 : ℝ) → ChQD_at D x eps C

def LinkThin : Prop :=
  ∀ B : ℕ, ∃ c : ℝ, 0 < c ∧ ∀ eps C : ℝ, 0 < eps → eps < 1 / 52 → ∃ x0 : ℝ, ∀ x : ℝ, x0 ≤ x → ∀ D : D7,
    oddQS D ≤ B → QDTied D x eps C → QDExists eps C x → (D.R.n : ℝ) ≤ x ^ (3 : ℝ) → BoxE D x eps →
      ChThin_at D x eps c

def LinkPointsLemma : Prop :=
  ∀ C0 Cr cr cQ cQ' : ℝ, 0 < C0 → 0 < Cr → 0 < cr → 0 < cQ → 0 < cQ' →
    ∃ C0' c1 c2 : ℝ, 0 < C0' ∧ 0 < c1 ∧ 0 < c2 ∧ ∀ (D : D7) (cT : ℝ),
      HostT D → adm8 D C0 Cr cr cQ cT → PointsLemma D cQ' C0' Cr cr c1 c2

def GL2LinkAdmissible : Prop :=
  ∀ eps : ℝ, 0 < eps → eps < 1 / 52 →
    ∀ c1 c5 C0 Cr cr cQ cT : ℝ, 0 < c1 → 0 < c5 → 0 < C0 → 0 < Cr → 0 < cr → 0 < cQ → 0 < cT →
      ∃ C : ℝ, 0 < C ∧ ∃ x0 : ℝ, ∀ x : ℝ, x0 ≤ x → ∀ D : D7,
        adm1 D c1 → adm5 D c5 → adm8 D C0 Cr cr cQ cT → Conclusion4 D x eps C

def LinkExists7 : Prop :=
  ∀ eps A : ℝ, 0 < eps → eps < 1 / 52 → 0 < A →
    ∀ C0 Cr cr cQ cT : ℝ, 0 < C0 → 0 < Cr → 0 < cr → 0 < cQ → 0 < cT →
      ∃ x0 : ℝ, ∀ x : ℝ, x0 ≤ x → ∀ D : D7, HostT D →
        1 ≤ D.R.k → (D.R.k : ℝ) ≤ x ^ A → 1 ≤ D.R.r → (D.R.r : ℝ) ≤ x ^ A → (D.R.n : ℝ) ≤ x ^ (3 : ℝ) →
        (D.host.d : ℝ) ≤ X2 x eps → Real.log (NE D) ≤ 2 * x ^ (eps / 5) * Real.log x ^ 2 →
        adm8 D C0 Cr cr cQ cT → GExists D x eps

def GL2LinkSizeRangesTiedPrimes : Prop :=
  ∀ eps : ℝ, 0 < eps → eps < 1 / 52 → ∃ x0 : ℝ, ∀ x : ℝ, x0 ≤ x → ∀ D : D7, HostT D →
    1 ≤ D.R.k → (D.R.k : ℝ) ≤ x ^ (5 : ℝ) → GTied D x eps → GExists D x eps → PrimesAsPropTwoSeven D x eps 9

def GL2LinkSizeRanges : Prop :=
  ∀ eps : ℝ, 0 < eps → eps < 1 / 52 →
    ∀ C0 Cr cr cQ cT : ℝ, 0 < C0 → 0 < Cr → 0 < cr → 0 < cQ → 0 < cT → ∀ C c : ℝ, 0 < C → 0 < c →
      ∃ x0 : ℝ, ∀ x : ℝ, x0 ≤ x → ∀ D : D7, HostT D →
        (D.R.n : ℝ) ≤ x ^ (3 : ℝ) → 1 ≤ D.R.k → (D.R.k : ℝ) ≤ x ^ (5 : ℝ) → (D.R.r : ℝ) ≤ x ^ (5 : ℝ) →
        x ^ ((1 : ℝ) / 3) ≤ D.R.m → D.R.f ≤ D.R.k →
        adm8 D C0 Cr cr cQ cT → CycSplit → division_rows_rational_lattice D x eps C c

def LinkTrec : Prop :=
  ∀ D : D7, HostT D → TTied D → (∀ u, ∃ T : ℕ, TGood D u T) → ∀ u,
    ((D.mem u).A.T).Prime ∧ NormOneMod D (NE D * (D.host.g 0 * D.host.g 1) ^ 2) (D.mem u).A.T ∧
      (D.mem u).A.T ≡ 1 [MOD NE D * (D.host.g 0 * D.host.g 1) ^ 2] ∧
      (D.mem u).A.Tstar ≤ ((D.mem u).A.T : ℝ) ∧
      ((D.mem u).A.T : ℝ) ≤ (D.mem u).A.Tstar * (1 + 1 / ((D.R.f : ℝ) * D.R.k))

def LinkExistsT : Prop :=
  ∀ eps : ℝ, 0 < eps → eps < 1 / 52 →
    ∀ C0 Cr cr cQ cT : ℝ, 0 < C0 → 0 < Cr → 0 < cr → 0 < cQ → 0 < cT → ∀ c : ℝ, 0 < c →
      ∃ x0 : ℝ, ∀ x : ℝ, x0 ≤ x → ∀ D : D7, HostT D →
        (D.R.n : ℝ) ≤ x ^ (3 : ℝ) → 1 ≤ D.R.k → (D.R.k : ℝ) ≤ x ^ (5 : ℝ) → x ^ ((1 : ℝ) / 3) ≤ D.R.m →
        D.R.f ≤ D.R.k → GTied D x eps → GExists D x eps → (∃ C5 : ℝ, PrimesAsPropTwoFive D x eps C5) →
        adm8 D C0 Cr cr cQ cT → TstarLogLowerBound D x eps c → ∀ u, ∃ T : ℕ, TGood D u T

def GL2LinkCycSplit : Prop :=
  ∀ eps : ℝ, 0 < eps → eps < 1 / 52 →
    ∀ C0 Cr cr cQ cT : ℝ, 0 < C0 → 0 < Cr → 0 < cr → 0 < cQ → 0 < cT → ∀ C : ℝ, 0 < C →
      ∃ C' : ℝ, 0 < C' ∧ ∃ x0 : ℝ, ∀ x : ℝ, x0 ≤ x → ∀ D : D7, HostT D →
        (D.R.n : ℝ) ≤ x ^ (3 : ℝ) → adm8 D C0 Cr cr cQ cT → CycSplit → Conclusion8 D x eps C C'

def LinkAdm4 : Prop := ∀ D : D7, HostT D → CNF → ArchimedeanSignatureMatching D

def LinkAdm1 : Prop := ∃ c : ℝ, 0 < c ∧ ∀ D : D7, adm1 D c

def LinkAdm5 : Prop := ∃ c : ℝ, 0 < c ∧ ∀ D : D7, adm5 D c

def LogGammaAdmissible : Prop := ∀ (eps : ℝ) (Fm : FamP eps), compactDualInputFamily Fm

end Formalism.L2.GlobalTheoryTheory.FiltrationCocycleLiftCriterion

end
