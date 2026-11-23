import Formalism.SharpRestriction.GrowthBounds.DiagonalSupport.DecompositionOfThreeParts

noncomputable section

open MvPolynomial Finset Classical

namespace Formalism.MainNotions.Proposition5Numerics

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.SourceCleaning Formalism.MainNotions.Pf14 Formalism.MainNotions.PlaneGramData Formalism.MainNotions.TestSideCounting Formalism.MainNotions.TestSideWords

def gamR (P rho be : ℕ) : ℚ :=
  ((rho + P * be).factorial : ℚ) / ((rho.factorial : ℚ) * (be.factorial : ℚ) * (P.factorial : ℚ) ^ be)

def diagK {Kf : Type} [Field Kf] {σ : Type} (g : (σ →₀ ℕ) → Kf) (F : MvPolynomial σ Kf) : MvPolynomial σ Kf :=
  ∑ mo ∈ F.support, monomial mo (g mo * F.coeff mo)

section Dig

variable {n' r K m : ℕ} [NeZero n'] (Fr : Frames n' r) (p : ℕ) (O : Type) [CommRing O] [IsDomain O]
  (hk : m + 1 = r + K) {J : ℕ} [NeZero J] (nL : ZMod J → ℕ)

def gamPl (rho : TL J nL r × Fin (r + K) → ℕ) (bp : TL J nL r × Fin r →₀ ℕ) : ℚ :=
  ∏ v : TL J nL r × Fin r, gamR (lowP Fr p v.1) (rho (v.1, Fin.castAdd K v.2)) (bp v)

def gamNo (rho : TL J nL r × Fin (r + K) → ℕ) (bn : TL J nL r × Fin K →₀ ℕ) : ℚ :=
  ∏ v : TL J nL r × Fin K, gamR (lowP Fr p v.1) (rho (v.1, Fin.natAdd r v.2)) (bn v)

def cstOf (rho : TL J nL r × Fin (r + K) → ℕ) (dPl dNo : TL J nL r → ℕ) : ℕ :=
  (∏ v : TL J nL r × Fin (r + K), (rho v).factorial) * ∏ x : TL J nL r, (lowP Fr p x).factorial ^ (dPl x + dNo x)

def classOf (mo : TV n' (m + 1) →₀ ℕ) : TL J nL r × Fin (r + K) → ℕ :=
  fun v => Fin.addCases (fun a => mo (plVar Fr hk nL v.1 a) % lowP Fr p v.1)
    (fun b => mo (noVar Fr hk nL v.1 b) % lowP Fr p v.1) v.2

def blkPl (mo : TV n' (m + 1) →₀ ℕ) : TL J nL r → ℕ := fun x => ∑ a : Fin r, mo (plVar Fr hk nL x a) / lowP Fr p x

def blkNo (mo : TV n' (m + 1) →₀ ℕ) : TL J nL r → ℕ := fun x => ∑ b : Fin K, mo (noVar Fr hk nL x b) / lowP Fr p x

def DigFacts (d : Fin n' → ℕ) : Prop :=
  ∀ G : MvPolynomial (TV n' (m + 1)) (KK O), HasMultideg G d →
    (∀ (rho : TL J nL r × Fin (r + K) → ℕ) (dPl dNo : TL J nL r → ℕ), (∀ x c, rho (x, c) < lowP Fr p x) →
      ∀ A ∈ Pol (KK O) r dPl, ∀ N ∈ Pol (KK O) K dNo,
        fock G (asm Fr p O hk nL rho A N) = ((cstOf Fr p nL rho dPl dNo : ℕ) : KK O) *
          ∑ bp ∈ A.support, ∑ bn ∈ N.support, ((levImg Fr p hk nL rho dPl dNo G).coeff bp).coeff bn *
            (((gamPl Fr p nL rho bp : ℚ) : KK O) * A.coeff bp * ((expFact bp : ℕ) : KK O)) *
            (((gamNo Fr p nL rho bn : ℚ) : KK O) * N.coeff bn * ((expFact bn : ℕ) : KK O))) ∧
    (∀ (rho : TL J nL r × Fin (r + K) → ℕ) (dPl dNo : TL J nL r → ℕ) (bp : TL J nL r × Fin r →₀ ℕ),
      (levImg Fr p hk nL rho dPl dNo G).coeff bp ∈ Pol (KK O) K dNo) ∧
    ∀ mo ∈ G.support,
      BlockOK Fr p nL d (classOf Fr p hk nL mo) (blkPl Fr p hk nL mo) (blkNo Fr p hk nL mo) ∧
      ((levImg Fr p hk nL (classOf Fr p hk nL mo) (blkPl Fr p hk nL mo) (blkNo Fr p hk nL mo) G).coeff
        (plMon Fr p hk nL mo)).coeff (noMon Fr p hk nL mo) = G.coeff mo ∧
      (∀ x, multideg (plMon Fr p hk nL mo) x = blkPl Fr p hk nL mo x) ∧
      (∀ x, multideg (noMon Fr p hk nL mo) x = blkNo Fr p hk nL mo x) ∧
      ((expFact mo : ℕ) : ℚ) = ((cstOf Fr p nL (classOf Fr p hk nL mo) (blkPl Fr p hk nL mo) (blkNo Fr p hk nL mo) : ℕ) : ℚ) *
        ((expFact (plMon Fr p hk nL mo) : ℕ) : ℚ) * ((expFact (noMon Fr p hk nL mo) : ℕ) : ℚ) *
        gamPl Fr p nL (classOf Fr p hk nL mo) (plMon Fr p hk nL mo) *
        gamNo Fr p nL (classOf Fr p hk nL mo) (noMon Fr p hk nL mo)

end Dig

section Parts

variable (p : ℕ) {n' r K : ℕ} [NeZero n'] [NeZero r] [NeZero K] (O : Type) [CommRing O] [IsDomain O]
  [IsDiscreteValuationRing O] (Fr : Frames n' r) {J : ℕ} [NeZero J]

def DnoOf (nL : ZMod J → ℕ) (dNo : TL J nL r → ℕ) : ℕ :=
  ∑ i : Σ j : ZMod J, Fin (nL j + r + 1), N0 K * Nat.log p (2 * degIn dNo (NSet nL i.1 i.2.val) + K - 1)

def JPOK (Dt : SignedChainData p O r J) (dNo : TL J Dt.nL r → ℕ) (ka : ZMod J → ℕ → Fin K → ℤ)
    (e : Module.End (KK O) (MvPolynomial (TL J Dt.nL r × Fin K) (KK O))) : Prop :=
  IsJProj (normE p K Dt) {fun i => ka i.1 i.2.val} e ∧
  (∀ F G, fock (e F) G = fock F (e G)) ∧
  (∀ F ∈ Pol (KK O) K dNo, e F ∈ Pol (KK O) K dNo ∧
    (InBB (O := O) p F → InBB (O := O) p (((p : KK O) ^ DnoOf (K := K) p Dt.nL dNo) • e F))) ∧
  ∀ F i, e F ∈ isoSub (normE p K Dt i) (ka i.1 i.2.val)

def JPAt (Dt : SignedChainData p O r J) : Prop :=
  ∀ (dNo : TL J Dt.nL r → ℕ), ∀ y ∈ Pol (KK O) K dNo,
    ∃ (ka : ZMod J → ℕ → Fin K → ℤ) (e : Module.End (KK O) (MvPolynomial (TL J Dt.nL r × Fin K) (KK O))),
      JPOK p O Dt dNo ka e ∧ vBB (O := O) p (e y) ≤ vBB (O := O) p y

def NoAt (cP : ℕ) (Dt : SignedChainData p O r J) : Prop :=
  ∀ (dNo : TL J Dt.nL r → ℕ) (ka : ZMod J → ℕ → Fin K → ℤ) (rho : TL J Dt.nL r × Fin (r + K) → ℕ)
    (e : Module.End (KK O) (MvPolynomial (TL J Dt.nL r × Fin K) (KK O))) (nu : TL J Dt.nL r × Fin K →₀ ℕ),
    (∀ x c, rho (x, c) < lowP Fr p x) → JPOK p O Dt dNo ka e → (∀ x, multideg nu x = dNo x) →
    ∃ (N0 : MvPolynomial (TL J Dt.nL r × Fin K) (KK O)) (cY : KK O),
      NormTest p O cP Dt dNo ka N0 ∧
      leQ (vK p cY) ((padicValNat p (∏ x, (dNo x).factorial) : ℝ) / 2 + DnoOf (K := K) p Dt.nL dNo -
        (padicValNat p (expFact nu) : ℝ) / 2) ∧
      CoefGe p (N0 - diagK (fun bn => ((gamNo Fr p Dt.nL rho bn : ℚ) : KK O)⁻¹) (cY • e (monomial nu 1))) cP

def GaAt (nL : ZMod J → ℕ) : Prop :=
  ∀ rho : TL J nL r × Fin (r + K) → ℕ, (∀ x c, rho (x, c) < lowP Fr p x) →
    (∀ bn : TL J nL r × Fin K →₀ ℕ, gamNo Fr p nL rho bn ≠ 0 ∧ padicValRat p (gamNo Fr p nL rho bn) = 0) ∧
    (∀ bp : TL J nL r × Fin r →₀ ℕ, gamPl Fr p nL rho bp ≠ 0 ∧ padicValRat p (gamPl Fr p nL rho bp) = 0) ∧
    ∃ ga : (TL J nL r × Fin r →₀ ℕ) → O, (∀ al, IsUnit (ga al)) ∧
      (∀ al, algebraMap O (KK O) (ga al) = ((gamPl Fr p nL rho al : ℚ) : KK O)) ∧
      ∀ k : ℕ, 1 ≤ k → ∀ ε : Bool, ∃ lam : (TL J nL r × Fin r →₀ ℕ) →₀ O,
        (∀ m ∈ lam.support, (m.sum fun _ e => e) ≤ 6 * k) ∧
        ∀ al : TL J nL r × Fin r →₀ ℕ,
          geQ (vK p ((if ε then algebraMap O (KK O) (ga al) else (algebraMap O (KK O) (ga al))⁻¹) -
            binomCombF (K := KK O) lam al)) (k : ℝ)

def SizeAt (nL : ZMod J → ℕ) (d : Fin n' → ℕ) (Dn : ℝ) : Prop :=
  ∀ (rho : TL J nL r × Fin (r + K) → ℕ) (dPl dNo : TL J nL r → ℕ), BlockOK Fr p nL d rho dPl dNo →
    ∀ (bp : TL J nL r × Fin r →₀ ℕ) (bn : TL J nL r × Fin K →₀ ℕ),
      (∀ x, multideg bp x = dPl x) → (∀ x, multideg bn x = dNo x) →
      (DnoOf (K := K) p nL dNo : ℝ) +
        ((padicValNat p (∏ x, (dPl x).factorial) : ℝ) - (padicValNat p (expFact bp) : ℝ)) / 2 +
        ((padicValNat p (∏ x, (dNo x).factorial) : ℝ) - (padicValNat p (expFact bn) : ℝ)) / 2 ≤ Dn

end Parts

end Formalism.MainNotions.Proposition5Numerics
