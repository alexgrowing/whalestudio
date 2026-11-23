import Formalism.SharpRestriction.GrowthBounds.WittFrameLocaliserOrders

noncomputable section

open MvPolynomial Finset Classical

namespace Formalism.MainNotions.G.symbolGeneratorData

open Formalism.MainNotions.G Formalism.MainNotions.SourceCleaning Formalism.MainNotions.G.WittFrameLocaliserOrders

structure Ctx (p n' r K : ℕ) [Fact p.Prime] [NeZero n'] [NeZero r] [NeZero K] (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [Algebra (WF p n') O] where
  S : UniformizedDVR p O
  hO : OHyp p n' O S
  hH : CommonHypotheses p n' r (r + K)
  Fr : Frames n' r
  L₁ : ℕ
  N₁ : ℕ
  G' : ℕ
  hV : Fr.Valid L₁ N₁
  hT : TwistBound p Fr (p ^ G')
  hG : ∀ j : ℤ, zF Fr j - Fr.fr (j - 1) 0 ≤ G'
  hK : N₁ + 2 * r ≤ K
  g : Matrix (Fin (r + K)) (Fin (r + K)) (WF p n')
  hg : IsGLW g

section Model

variable {n' r : ℕ} [NeZero n'] (F : Frames n' r) (j : ℤ)

abbrev Mj : ℕ := (F.letters j).card

def eL (i : Fin (Mj F j)) : ℤ := (F.letters j).orderEmbOfFin rfl i

def LLs : LiftLetters (Fin (Mj F j)) where
  vec := fun i => decide (Even (eL F j i))
  pos := eL F j

def nonW : Finset ℤ := (F.letters j).filter fun x => ¬ F.IsW j x

variable (O : Type) [CommRing O] (K : ℕ)

def plnm : MvPolynomial (Fin (Mj F j) × Fin (r + K)) O →ₐ[O] SegRing O r K :=
  rename fun v => (eL F j v.1, v.2)

variable {O} {K}

def CondM [NeZero r] [NeZero K] (m : ℤ) (A : MvPolynomial (Fin (Mj F j) × Fin r) O)
    (G : MvPolynomial (Fin (Mj F j) × Fin K) O) (Mx : Fin (Mj F j) → ℤ) : Prop :=
  ∀ i, ¬ F.IsW j (eL F j i) →
    (Even (eL F j i) → lam1S (LLs F j).toLetters {y | y ≤ i} G ≤ ((Mx i : ℤ) : WithBot ℤ) ∧
      ((Mx i + m : ℤ) : WithTop ℤ) ≤ valS (LLs F j).toLetters {y | y < i} A) ∧
    (¬ Even (eL F j i) → lam1S (LLs F j).toLetters {y | y < i} G ≤ ((Mx i : ℤ) : WithBot ℤ) ∧
      ((Mx i + m : ℤ) : WithTop ℤ) ≤ valS (LLs F j).toLetters {y | y ≤ i} A)

variable (O) (K)

def MGen [NeZero r] [NeZero K] (m : ℤ) (th : ℤ → ℝ) (dd : ℤ → ℕ) : Set (SegRing O r K) :=
  {P | ∃ (d' d'' : Fin (Mj F j) → ℕ) (A : MvPolynomial (Fin (Mj F j) × Fin r) O)
      (G : MvPolynomial (Fin (Mj F j) × Fin K) O) (Mx : Fin (Mj F j) → ℤ),
      A ∈ Pol O r d' ∧ G ∈ Pol O K d'' ∧ (∀ i, d' i + d'' i = dd (eL F j i)) ∧
      (∀ i, F.IsW j (eL F j i) → d'' i = 0) ∧ CondM F j m A G Mx ∧
      (∀ i, ¬ F.IsW j (eL F j i) → geR (valS (LLs F j).toLetters {y | y < i} A) (th (eL F j i))) ∧
      P = plnm F j O K (rename (plVar (K := K)) A * rename (tanVar (r := r)) G)}

def MGen0 [NeZero r] [NeZero K] : Set (SegRing O r K) :=
  {P | ∃ (d' d'' : Fin (Mj F j) → ℕ) (A : MvPolynomial (Fin (Mj F j) × Fin r) O)
      (G : MvPolynomial (Fin (Mj F j) × Fin K) O) (Mx : Fin (Mj F j) → ℤ),
      A ∈ Pol O r d' ∧ G ∈ Pol O K d'' ∧ (∀ i, F.IsW j (eL F j i) → d'' i = 0) ∧ CondM F j 0 A G Mx ∧
      P = plnm F j O K (rename (plVar (K := K)) A * rename (tanVar (r := r)) G)}

def PGen : Set (SegRing O r K) :=
  {P | ∃ (B : Fin (Mj F j) → ℕ) (Pth : PPath (r + K) (Mj F j) (LLs F j).toLetters B)
      (nu : Fin (Mj F j + 1) → Fin r → ℤ) (ka : Fin (Mj F j + 1) → Fin K → ℤ)
      (I' : ℤ → Finset (Fin r)) (I'' : ℤ → Finset (Fin K)),
      Pth.mu = joinPT nu ka ∧ IsSt nu I' ∧ IsSt ka I'' ∧ P = plnm F j O K (PsiPl O nu I' * PsiTan O ka I'')}

def Dseg (x : ℤ) : SegRing O r K :=
  (Matrix.of fun l b : Fin r => (X (Arow F x l.val, Fin.castAdd K b) : SegRing O r K)).det

def Wseg : SegRing O r K :=
  (Matrix.of fun l b : Fin r => (X (F.fr (j - 1) l.val, Fin.castAdd K b) : SegRing O r K)).det

def Dv (m1 m2 : ℕ) : SegRing O r K := (∏ x ∈ nonW F j, Dseg F O K x ^ m1) * Wseg F j O K ^ m2

end Model

section Sym

variable {p n' r k : ℕ} [Fact p.Prime] [NeZero n'] {O : Type} [CommRing O] [IsDomain O] [Algebra (WF p n') O]
  (w : O) (Fr : Frames n' r) (Q : ℕ) (g : Matrix (Fin k) (Fin k) (WF p n'))

def Sy (o : ℕ) (P : MvPolynomial (TV n' k) (KK O)) : Prop :=
  (∀ m ∈ P.support, normDeg r m = o) ∧
    C (algebraMap O (KK O) (w ^ o)) * P ∈ AddSubmonoid.closure (bc_agen w Fr Q g o 0)

def SyS : AddSubmonoid (MvPolynomial (TV n' k) (KK O)) := AddSubmonoid.closure {P | ∃ o, Sy w Fr Q g o P}

end Sym

section CtxDefs

variable {p n' r K : ℕ} [Fact p.Prime] [NeZero n'] [NeZero r] [NeZero K] {O : Type} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [Algebra (WF p n') O] (X : Ctx p n' r K O)

def Ctx.Q : ℕ := p ^ X.G'

def Ctx.m1 (c' : ℕ) : ℕ := (2 * X.Q + 3) * c' + (r + K) * X.Q + c'

def Ctx.m2 (c' : ℕ) : ℕ := c' * alphaMax p X.Fr (r + K) + 2 * c'

def Ctx.sb : MvPolynomial (TV n' (r + K)) (KK O) →ₐ[KK O] MvPolynomial (TV n' (r + K)) (KK O) :=
  subst p n' O X.S.w n' r X.g

def Ctx.fixedSymbolFactor (c' : ℕ) : MvPolynomial (TV n' (r + K)) (KK O) :=
  (X.sb (R0 p n' O X.Fr X.g)) ^ c' * (∏ j ∈ Finset.range X.Fr.J, (X.sb (Del p n' O X.Fr X.g j)) ^ c') *
    X.sb (DtopProd p n' O X.Fr X.hH.2.2.1 X.g ((2 * X.Q + 3) * c'))

def Ctx.DkQ : MvPolynomial (TV n' (r + K)) (KK O) :=
  X.sb (DtopProd p n' O X.Fr X.hH.2.2.1 X.g ((r + K) * X.Q))

def Ctx.SyS : AddSubmonoid (MvPolynomial (TV n' (r + K)) (KK O)) := symbolGeneratorData.SyS X.S.w X.Fr X.Q X.g

end CtxDefs

def RestModel : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] (n' r K : ℕ) [NeZero n'] [NeZero r] [NeZero K] (F : Frames n' r) (j : ℤ)
    (m : ℤ) (th o : ℤ → ℝ) (dd : ℤ → ℕ) (xi : SegRing O r K),
    xi ∈ XX' O r K F j (fun _ => m) th o →
    xi ∈ restrictSupport O {mm | ∀ x ∈ F.letters j, ∑ c : Fin (r + K), mm (x, c) = dd x} →
    xi ∈ Submodule.span O (MGen F j O K m th dd)

def RestGeom : Prop :=
  ∀ (p n' r : ℕ) [NeZero n'] (F : Frames n' r) (L₁ N₁ : ℕ), 13 ≤ p → 2 ≤ r → Even n' → F.Valid L₁ N₁ →
  ∀ (deg : Fin n' → ℕ) (a : ℕ), (∀ s ∈ F.TT, (a : ℝ) ≤ deg s ∧ (deg s : ℝ) ≤ 2 * a) →
  ∀ (j : ℤ) (dd : ℤ → ℕ),
    (∀ x ∈ F.letters j, (F.IsW j x ∨ x ∈ F.LLset j) →
      |(dd x : ℝ) - levDeg p F deg j x| ≤ levDeg p F deg j x / 100) →
  ∀ x ∈ nonW F j,
    ((∑ y ∈ (F.letters j).filter (fun y => Even y ∧ y < x ∧ ∀ l < r, y ≠ Arow F x l), dd y : ℕ) : ℝ) ≤
      Bo p F deg j x / 80

def RestDivM (CLa CD Csz : ℝ) : Prop :=
  ∀ (p n' r K : ℕ) [Fact p.Prime] [NeZero n'] [NeZero r] [NeZero K] (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [Algebra (WF p n') O] (X : Ctx p n' r K O)
    (deg : Fin n' → ℕ) (a : ℕ) (Y : ℝ) (c0 c'' cStar : ℕ) (Dd : ℝ),
    HypII CLa CD Csz p X.Fr (r + K) X.L₁ X.N₁ X.G' deg a Y c0 c'' cStar Dd →
  ∀ (j : ℤ) (dd : ℤ → ℕ),
    (∀ x ∈ X.Fr.letters j, (X.Fr.IsW j x ∨ x ∈ X.Fr.LLset j) →
      |(dd x : ℝ) - levDeg p X.Fr deg j x| ≤ levDeg p X.Fr deg j x / 100) →
  ∀ P ∈ MGen X.Fr j O K (mStar p X.Fr (r + K) X.N₁ (p ^ X.G') (cPrime n' r X.Fr.TT.card c0 c'' cStar) : ℤ)
      (fun x => Bo p X.Fr deg j x / 2 - sl p X.Fr deg Y (r + K) j x) dd,
    ∃ P' ∈ MGen0 X.Fr j O K,
      P = Dv X.Fr j O K (X.m1 (cPrime n' r X.Fr.TT.card c0 c'' cStar))
        (X.m2 (cPrime n' r X.Fr.TT.card c0 c'' cStar)) * P'

def GeneratorSpanInclusion : Prop :=
  ∀ (p n' r K : ℕ) [Fact p.Prime] [NeZero n'] [NeZero r] [NeZero K] (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [Algebra (WF p n') O] (X : Ctx p n' r K O) (j : ℤ),
    ∀ P ∈ MGen0 X.Fr j O K, P ∈ Submodule.span O (PGen X.Fr j O K)

def GeneratorImageIsSymbol : Prop :=
  ∀ (p n' r K : ℕ) [Fact p.Prime] [NeZero n'] [NeZero r] [NeZero K] (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [Algebra (WF p n') O] (X : Ctx p n' r K O) (j : ℤ),
    ∀ P ∈ PGen X.Fr j O K, ∃ o, Sy X.S.w X.Fr X.Q X.g o
      (MvPolynomial.map (algebraMap O (KK O)) (phSeg O K p X.Fr j P))

def RestMon : Prop :=
  ∀ (p n' r K : ℕ) [Fact p.Prime] [NeZero n'] [NeZero r] [NeZero K] (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [Algebra (WF p n') O] (X : Ctx p n' r K O)
    (mon : Fin n' × Fin (r + K) →₀ ℕ), IsLabel p X.Fr mon → (∀ v ∈ mon.support, v.1 ∈ X.Fr.TT) →
    ∃ o, Sy X.S.w X.Fr X.Q X.g o (monomial mon 1 * X.DkQ)

def RestPh : Prop :=
  ∀ (p n' r K : ℕ) [Fact p.Prime] [NeZero n'] [NeZero r] [NeZero K] (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [Algebra (WF p n') O] (X : Ctx p n' r K O) (c' : ℕ),
    ∃ H Y : MvPolynomial (TV n' (r + K)) (KK O), bc_IT X.Fr H ∧ InWj X.S.w Y 0 ∧
      MvPolynomial.map (algebraMap O (KK O))
          (∏ j ∈ Finset.range X.Fr.J, phSeg O K p X.Fr (j : ℤ) (Dv X.Fr (j : ℤ) O K (X.m1 c') (X.m2 c'))) =
        X.fixedSymbolFactor c' * X.DkQ * H + C (algebraMap O (KK O) ((p : O) ^ c')) * Y

end Formalism.MainNotions.G.symbolGeneratorData
