import Formalism.SharpRestriction.GrowthBounds.AevalValuation.RestSpec
import Formalism.SharpRestriction.GrowthBounds.DiagonalSupport.MembDefs
import Formalism.SharpRestriction.GrowthBounds.TwistedSubstitution.TwistedMonomialFiltration.TwistSubXMemSupported

noncomputable section

open MvPolynomial Finset Classical

namespace Formalism.MainNotions.PairMembershipBlocks

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.SourceCleaning Formalism.MainNotions.Pf14 Formalism.MainNotions.PlaneGramData Formalism.MainNotions.TestSideCounting Formalism.MainNotions.TestSideWords Formalism.MainNotions.Proposition5Numerics Formalism.MainNotions.TraceSpectra
open Formalism.MainNotions.TestSideWords.TwistedFiltration.G3

def PhiJ {n' r : ℕ} [NeZero n'] [NeZero r] (Fr : Frames n' r) {p : ℕ} {O : Type} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] {J : ℕ} (Dt : SignedChainData p O r J) (j : ZMod J) :
    MvPolynomial (ℤ × Fin r) (KK O) →ₐ[KK O] MvPolynomial (TL J Dt.nL r × Fin r) (KK O) :=
  Dt.ph.comp (chi Fr Dt.nL (KK O) j)

def wSet {n' r : ℕ} (Fr : Frames n' r) (jz : ℤ) : Set ℤ := {y | ∃ m : Fin r, y = Fr.fr (jz - 1) (r - 1 - m.val)}

def ValNN : Prop :=
  ∀ (R : Type) [CommRing R] [IsDomain R] (ι : Type) (n : ℕ) [NeZero n] (LL : Letters ι) (S : Set ι)
    (F : MvPolynomial (ι × Fin n) R), (∀ v ∈ F.vars, v.1 ∈ S → LL.vec v.1 = true) → 0 ≤ valS LL S F

def HomDec : Prop :=
  ∀ (R : Type) [CommRing R] (ι : Type) (n : ℕ) (F : MvPolynomial (ι × Fin n) R),
    ∃ Dl : Finset (ι → ℕ), F = ∑ δ ∈ Dl, homComp δ F

def LinkL : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (n' r : ℕ) [NeZero n'] [NeZero r] (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] (Fr : Frames n' r) (L₁ N₁ : ℕ), Fr.Valid L₁ N₁ → Even n' →
    ∀ (J : ℕ) [NeZero J] (Dt : SignedChainData p O r J), TieS Fr Dt → 2 ≤ J →
    ∀ (j : ZMod J) (mm : Fin r), mm.val + 2 ≤ r →
    ∀ (F : MvPolynomial (ℤ × Fin r) (KK O)), F ∈ supported (KK O) {v : ℤ × Fin r | v.1 ∈ Fr.letters (segZ j)} →
    ∀ (dw : ℕ), (∀ μ ∈ F.support, wDeg (wSet Fr (segZ j)) μ ≤ dw) →
    ∀ (th : ℤ), (th : WithTop ℤ) ≤ valS LZ {y | y < posU Fr (Dt.nL j) (segZ j) (Dt.nL j + (r - 1 - mm.val))} F →
      ((th - dw : ℤ) : WithTop ℤ) ≤ valS Dt.trueLet (Dt.TSet j mm) (PhiJ Fr Dt j F)

def LkDeg : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (n' r : ℕ) [NeZero n'] [NeZero r] (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] (Fr : Frames n' r) (L₁ N₁ : ℕ), Fr.Valid L₁ N₁ →
    ∀ (J : ℕ) [NeZero J] (Dt : SignedChainData p O r J), TieS Fr Dt → 2 ≤ J →
    ∀ (j : ZMod J) (F : MvPolynomial (ℤ × Fin r) (KK O)),
      F ∈ supported (KK O) {v : ℤ × Fin r | v.1 ∈ Fr.letters (segZ j)} →
    ∀ (δ : ℤ → ℕ), (∀ μ ∈ F.support, ∀ y, multideg μ y = δ y) →
    ∀ ν ∈ (PhiJ Fr Dt j F).support, ∀ m' : Fin r,
      multideg ν ⟨j - 1, Sum.inr m'⟩ = Dt.P (j - 1) m' * δ (Fr.fr (segZ j - 1) (r - 1 - m'.val))

def LkVars : Prop :=
  ∀ (p : ℕ) (n' r : ℕ) [NeZero n'] [NeZero r] (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] (Fr : Frames n' r) (J : ℕ) [NeZero J] (Dt : SignedChainData p O r J)
    (j : ZMod J) (F : MvPolynomial (ℤ × Fin r) (KK O)),
    ∀ v ∈ (PhiJ Fr Dt j F).vars, (∃ l, v.1 = ⟨j, Sum.inl l⟩) ∨ ∃ (j' : ZMod J) (m' : Fin r), v.1 = ⟨j', Sum.inr m'⟩

def RestLink : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (n' r K m : ℕ) [NeZero n'] [NeZero r] [NeZero K] (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [CharZero (KK O)]
    (hk : m + 1 = r + K) (Fr : Frames n' r) (L₁ N₁ : ℕ), Fr.Valid L₁ N₁ → Even n' →
    ∀ (J : ℕ) [NeZero J] (Dt : SignedChainData p O r J), TieS Fr Dt → 2 ≤ J →
    ∀ (A : ℤ → MvPolynomial (ℤ × Fin r) O),
      (∀ i : ℕ, i < Fr.J → A i ∈ supported O {v : ℤ × Fin r | v.1 ∈ Fr.letters i}) →
    ∀ (l : Fin n' × Fin (r + K) →₀ ℕ), IsLabel p Fr l →
    ∀ (ga : TV n' (m + 1) →₀ ℕ), PlaneEven r ga →
    ∀ (t : ZMod J → ℕ → ℝ),
      (∀ (j : ZMod J) (u : ℕ), u < Dt.nL j + r →
        geZ (valS LZ {y | y < posU Fr (Dt.nL j) (segZ j) u} (A (segZ j))) (t j u)) →
    ∀ (dPl : TL J Dt.nL r → ℕ),
      ∀ (j : ZMod J) (mm : Fin r), mm.val + 2 ≤ r →
        geZ (valS Dt.trueLet (Dt.TSet j mm) (compD dPl (levP Fr p hk Dt.nL (zPl p O hk Fr A l ga))))
          (t j (Dt.nL j + (r - 1 - mm.val)) - dwB Fr hk Dt dPl (l.mapDomain (castV hk) + ga) j)

def RestChain : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (n' r K m : ℕ) [NeZero n'] [NeZero r] [NeZero K] (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [CharZero (KK O)]
    (hk : m + 1 = r + K) (Fr : Frames n' r) (L₁ N₁ : ℕ), Fr.Valid L₁ N₁ → Even n' →
    ∀ (J : ℕ) [NeZero J] (Dt : SignedChainData p O r J), TieS Fr Dt → 2 ≤ J →
    ∀ (A : ℤ → MvPolynomial (ℤ × Fin r) O),
      (∀ i : ℕ, i < Fr.J → A i ∈ supported O {v : ℤ × Fin r | v.1 ∈ Fr.letters i}) →
    ∀ (l : Fin n' × Fin (r + K) →₀ ℕ), IsLabel p Fr l →
    ∀ (ga : TV n' (m + 1) →₀ ℕ), PlaneEven r ga →
    ∀ (t : ZMod J → ℕ → ℝ),
      (∀ (j : ZMod J) (u : ℕ), u < Dt.nL j + r →
        geZ (valS LZ {y | y < posU Fr (Dt.nL j) (segZ j) u} (A (segZ j))) (t j u)) →
    ∀ (dPl : TL J Dt.nL r → ℕ),
      (∀ (rho' : (ZMod J × Fin r) × Fin r → ℕ) (j : ZMod J) (i : Fin (Dt.nch j)),
        geZ (valS Dt.modelLet (Dt.chainML j i)
          (Dt.Fdig rho' (compD dPl (levP Fr p hk Dt.nL (zPl p O hk Fr A l ga))))) (t j i.val))

end Formalism.MainNotions.PairMembershipBlocks
