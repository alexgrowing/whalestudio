import Formalism.SharpRestriction.GrowthBounds.TwistedSubstitution.Proposition5Gram
import Formalism.SharpRestriction.GrowthBounds.TwistedSubstitution.MemLin

noncomputable section

open MvPolynomial Finset Classical

namespace Formalism.MainNotions.Proposition5Numerics

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.SourceCleaning Formalism.MainNotions.Pf14 Formalism.MainNotions.PlaneGramData Formalism.MainNotions.TestSideCounting Formalism.MainNotions.TestSideWords

def CoefGe (p : ℕ) {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {σ : Type}
    (F : MvPolynomial σ (KK O)) (t : ℝ) : Prop :=
  ∀ mo, geQ (vK p (F.coeff mo)) t

def twiceValuationFactorialProduct (p : ℕ) {n' : ℕ} (d : Fin n' → ℕ) : ℝ := (padicValNat p (∏ s, (d s).factorial) : ℝ)

section Asm

variable {n' r K m : ℕ} [NeZero n'] (Fr : Frames n' r) (p : ℕ) (O : Type) [CommRing O] [IsDomain O]
  (hk : m + 1 = r + K) {J : ℕ} [NeZero J] (nL : ZMod J → ℕ)

def labMon (rho : TL J nL r × Fin (r + K) → ℕ) : TV n' (m + 1) →₀ ℕ :=
  ∑ x : TL J nL r, ((∑ a : Fin r, Finsupp.single (plVar Fr hk nL x a) (rho (x, Fin.castAdd K a))) +
    ∑ b : Fin K, Finsupp.single (noVar Fr hk nL x b) (rho (x, Fin.natAdd r b)))

def upPl : MvPolynomial (TL J nL r × Fin r) (KK O) →ₐ[KK O] MvPolynomial (TV n' (m + 1)) (KK O) :=
  aeval fun v => X (plVar Fr hk nL v.1 v.2) ^ lowP Fr p v.1

def upNo : MvPolynomial (TL J nL r × Fin K) (KK O) →ₐ[KK O] MvPolynomial (TV n' (m + 1)) (KK O) :=
  aeval fun v => X (noVar Fr hk nL v.1 v.2) ^ lowP Fr p v.1

def asm (rho : TL J nL r × Fin (r + K) → ℕ) (A : MvPolynomial (TL J nL r × Fin r) (KK O))
    (N : MvPolynomial (TL J nL r × Fin K) (KK O)) : MvPolynomial (TV n' (m + 1)) (KK O) :=
  monomial (labMon Fr hk nL rho) 1 * upPl Fr p O hk nL A * upNo Fr p O hk nL N

def BlockOK (d : Fin n' → ℕ) (rho : TL J nL r × Fin (r + K) → ℕ) (dPl dNo : TL J nL r → ℕ) : Prop :=
  (∀ x c, rho (x, c) < lowP Fr p x) ∧
  ∀ x, ∑ c, rho (x, c) + lowP Fr p x * (dPl x + dNo x) = d (posOf n' (posTL Fr x))

end Asm

section Pick

variable (p : ℕ) {n' r K m : ℕ} [NeZero n'] [NeZero r] [NeZero K] (O : Type) [CommRing O] [IsDomain O]
  [IsDiscreteValuationRing O] (hk : m + 1 = r + K) (Fr : Frames n' r) (deg : Fin n' → ℕ) (Y : ℝ) (N₁ G' cP : ℕ)

def SignedChainDegreeCondition {J : ℕ} (Dt : SignedChainData p O r J) (dPl : TL J Dt.nL r → ℕ) (ka : ZMod J → ℕ → Fin K → ℤ) : Prop :=
  Tied Fr p deg Y (r + K) (mStar p Fr (r + K) N₁ (p ^ G') cP) K Dt dPl ka ∧ Dt.c = (cP : ℝ) ∧
  ∀ j (i : Fin (Dt.nch j)), Dt.sl j i = 3 / 8 * slU Fr p deg Y (r + K) Dt.nL j i.val

def NormTest {J : ℕ} [NeZero J] (Dt : SignedChainData p O r J) (dNo : TL J Dt.nL r → ℕ) (ka : ZMod J → ℕ → Fin K → ℤ)
    (N0 : MvPolynomial (TL J Dt.nL r × Fin K) (KK O)) : Prop :=
  CoefGe p N0 0 ∧ N0 ∈ Pol (KK O) K dNo ∧
  ∀ (j : ZMod J) (u : ℕ), u ≤ Dt.nL j + r →
    lam1S Dt.trueLet (NSet Dt.nL j u) N0 ≤ ((ka j u 0 + 4 * (cP : ℤ) : ℤ) : WithBot ℤ)

def PickAt (d : Fin n' → ℕ) (κ : ℕ) (Dn : ℝ) (G : MvPolynomial (TV n' (m + 1)) (KK O)) : Prop :=
  ∃ (J : ℕ) (_ : NeZero J) (Dt : SignedChainData p O r J) (dPl dNo : TL J Dt.nL r → ℕ) (ka : ZMod J → ℕ → Fin K → ℤ)
    (rho : TL J Dt.nL r × Fin (r + K) → ℕ) (F2 : MvPolynomial (TL J Dt.nL r × Fin r) (KK O))
    (N0 : MvPolynomial (TL J Dt.nL r × Fin K) (KK O)) (k0 : KK O),
    SignedChainDegreeCondition p O Fr deg Y N₁ G' cP Dt dPl ka ∧ BlockOK Fr p Dt.nL d rho dPl dNo ∧
    Dt.XX F2 ∧ vBB (O := O) p F2 = 0 ∧ NormTest p O cP Dt dNo ka N0 ∧
    leQ (vK p k0) (twiceValuationFactorialProduct p d - Dt.n0 + Dn) ∧
    ∀ A ∈ Pol (KK O) r dPl, CoefGe p A 0 →
      geQ (vK p (fock G (asm Fr p O hk Dt.nL rho A N0) - k0 * Dt.Bform F2 A)) ((cP : ℝ) + twiceValuationFactorialProduct p d - κ)

def MembAt (d : Fin n' → ℕ) : Prop :=
  ∀ (J : ℕ) [NeZero J] (Dt : SignedChainData p O r J) (dPl dNo : TL J Dt.nL r → ℕ) (ka : ZMod J → ℕ → Fin K → ℤ)
    (rho : TL J Dt.nL r × Fin (r + K) → ℕ) (N0 : MvPolynomial (TL J Dt.nL r × Fin K) (KK O)),
    SignedChainDegreeCondition p O Fr deg Y N₁ G' cP Dt dPl ka → BlockOK Fr p Dt.nL d rho dPl dNo → NormTest p O cP Dt dNo ka N0 →
    ∀ Gp : MvPolynomial (ML J Dt.nL r × Fin r) (KK O), CoefGe p Gp 0 → Dt.YY 24 60 Gp →
      (∀ mo ∈ Gp.support, Dt.ph (monomial mo 1) ∈ Pol (KK O) r Dt.d) →
      ∃ (nq : ℕ) (o : Fin nq → ℕ) (sig : Fin nq → MvPolynomial (TV n' (m + 1)) (KK O)),
        (∀ q, HasMultideg (sig q) d ∧ OneSidedLemma4Element p K O Fr N₁ G' cP deg Y hk (o q) (sig q)) ∧
        ∑ q, sig q = asm Fr p O hk Dt.nL rho (Dt.ph Gp) N0

def NumAt (d : Fin n' → ℕ) (CDm large₂ : ℝ) : Prop :=
  ∀ (J : ℕ) [NeZero J] (Dt : SignedChainData p O r J) (dPl dNo : TL J Dt.nL r → ℕ) (ka : ZMod J → ℕ → Fin K → ℤ)
    (rho : TL J Dt.nL r × Fin (r + K) → ℕ),
    SignedChainDegreeCondition p O Fr deg Y N₁ G' cP Dt dPl ka → BlockOK Fr p Dt.nL d rho dPl dNo →
    Dt.Hyp 26 ∧ 4 * (Dt.Dm + Dt.Dl + 3 * Dt.kp) < Dt.c ∧ 0 ≤ Dt.kp ∧ Dt.Dm + Dt.Dl + 3 * Dt.kp ≤ CDm * large₂

end Pick

def PickStep (C CDn CLa : ℝ) : Prop :=
  ∀ (p : ℕ) (W Qq O Kf : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq] [Algebra W Qq]
    [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
    (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (j : W →+* O) (w : O)
    (n' m r : ℕ) [Fact p.Prime] [NeZero n'] (TT : Finset (Fin n')) (L₁ L₂ : ℕ) (de h x : ℝ)
    (lam0 : Fin n' → Fin (m + 1) → ℤ) (aT bT : Fin n' → ℤ) (a Y : ℝ) (cpp c0 Dp cStar : ℕ)
    (K : ℕ) [NeZero r] [NeZero K] (hk : m + 1 = r + K) (F : Frames n' r) (nb : ℕ)
    (B : Fin nb → RRing O n' (r + K)),
    DataII C CLa p W Qq O Kf ι σ j w n' m r TT L₁ L₂ de h x lam0 aT bT a Y cpp c0 Dp cStar K F nb B →
    ∀ G : MvPolynomial (TV n' (m + 1)) (KK O),
      HasMultideg G (dT TT lam0) → InWj w G 0 → ¬ InWj w G 1 →
      MemAt p O hk F (flatDeg lam0) Y (orbitWindowCount r de h x) (goodG' r de h x) (cPrime n' r TT.card c0 cpp cStar) G →
      PickAt p O hk F (flatDeg lam0) Y (orbitWindowCount r de h x) (goodG' r de h x) (cPrime n' r TT.card c0 cpp cStar)
        (dT TT lam0) (kapFl p (m + 1) (dT TT lam0))
        (CDn * ((TT.card : ℝ) * ((m + 1 : ℕ) : ℝ) ^ 2 * Real.logb p a)) G

def MembStep (C CLa : ℝ) : Prop :=
  ∀ (p : ℕ) (W Qq O Kf : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq] [Algebra W Qq]
    [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
    (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (j : W →+* O) (w : O)
    (n' m r : ℕ) [Fact p.Prime] [NeZero n'] (TT : Finset (Fin n')) (L₁ L₂ : ℕ) (de h x : ℝ)
    (lam0 : Fin n' → Fin (m + 1) → ℤ) (aT bT : Fin n' → ℤ) (a Y : ℝ) (cpp c0 Dp cStar : ℕ)
    (K : ℕ) [NeZero r] [NeZero K] (hk : m + 1 = r + K) (F : Frames n' r) (nb : ℕ)
    (B : Fin nb → RRing O n' (r + K)),
    DataII C CLa p W Qq O Kf ι σ j w n' m r TT L₁ L₂ de h x lam0 aT bT a Y cpp c0 Dp cStar K F nb B →
    MembAt p O hk F (flatDeg lam0) Y (orbitWindowCount r de h x) (goodG' r de h x) (cPrime n' r TT.card c0 cpp cStar) (dT TT lam0)

def NumStep (C CDm CLa : ℝ) : Prop :=
  ∀ (p : ℕ) (W Qq O Kf : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq] [Algebra W Qq]
    [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
    (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (j : W →+* O) (w : O)
    (n' m r : ℕ) [Fact p.Prime] [NeZero n'] (TT : Finset (Fin n')) (L₁ L₂ : ℕ) (de h x : ℝ)
    (lam0 : Fin n' → Fin (m + 1) → ℤ) (aT bT : Fin n' → ℤ) (a Y : ℝ) (cpp c0 Dp cStar : ℕ)
    (K : ℕ) [NeZero r] [NeZero K] (_hk : m + 1 = r + K) (F : Frames n' r) (nb : ℕ)
    (B : Fin nb → RRing O n' (r + K)),
    DataII C CLa p W Qq O Kf ι σ j w n' m r TT L₁ L₂ de h x lam0 aT bT a Y cpp c0 Dp cStar K F nb B →
    1 ≤ (TT.card : ℝ) * ((m + 1 : ℕ) : ℝ) ^ 2 * Real.logb p a ∧
    (kapFl p (m + 1) (dT TT lam0) : ℝ) ≤ CDm * ((TT.card : ℝ) * ((m + 1 : ℕ) : ℝ) ^ 2 * Real.logb p a) ∧
    NumAt (K := K) p O F (flatDeg lam0) Y (orbitWindowCount r de h x) (goodG' r de h x) (cPrime n' r TT.card c0 cpp cStar)
      (dT TT lam0) CDm ((TT.card : ℝ) * ((m + 1 : ℕ) : ℝ) ^ 2 * Real.logb p a)

def RestPick (D : Formalism.BasicNotions.D7) (CLa Ck Crk Cdeg : ℝ) : Prop :=
  tableLineDegreeFive.admitted D CLa Ck Crk Cdeg → ∃ CDn C₁ : ℝ, 0 < CDn ∧ 0 < C₁ ∧ ∀ C : ℝ, C₁ ≤ C → PickStep C CDn CLa

def RestMemb (D : Formalism.BasicNotions.D7) (CLa Ck Crk Cdeg : ℝ) : Prop :=
  tableLineDegreeFive.admitted D CLa Ck Crk Cdeg → ∃ C₁ : ℝ, 0 < C₁ ∧ ∀ C : ℝ, C₁ ≤ C → MembStep C CLa

def RestNum (D : Formalism.BasicNotions.D7) (CLa Ck Crk Cdeg : ℝ) : Prop :=
  tableLineDegreeFive.admitted D CLa Ck Crk Cdeg → ∃ CDm C₁ : ℝ, 0 < CDm ∧ 0 < C₁ ∧ ∀ C : ℝ, C₁ ≤ C → NumStep C CDm CLa

end Formalism.MainNotions.Proposition5Numerics
