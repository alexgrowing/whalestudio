import Formalism.SharpRestriction.GrowthBounds.PlaneCoefficients.PlaneCoeffOneTTens

noncomputable section

open MvPolynomial Finset Classical

namespace Formalism.MainNotions.TraceSpectra

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.SourceCleaning Formalism.MainNotions.Pf14 Formalism.MainNotions.PlaneGramData Formalism.MainNotions.TestSideCounting Formalism.MainNotions.TestSideWords Formalism.MainNotions.PairMembershipBlocks

section Defs

variable {n' r : ℕ} [NeZero n'] [NeZero r] (Fr : Frames n' r) {J : ℕ} (nL : ZMod J → ℕ)

def mlOf (j : ZMod J) (y : ℤ) : ML J nL r :=
  if h : ∃ l : Fin (nL j), y = llPos Fr (segZ j) l.val then ML.ll j h.choose
  else if h : ∃ m : Fin r, y = Fr.fr (segZ j) (r - 1 - m.val) then ML.lab j h.choose
  else if h : ∃ m : Fin r, y = Fr.fr (segZ j - 1) (r - 1 - m.val) then ML.wc (j - 1) h.choose
  else ML.lab j 0

def chi (Kf : Type) [CommRing Kf] (j : ZMod J) :
    MvPolynomial (ℤ × Fin r) Kf →ₐ[Kf] MvPolynomial (ML J nL r × Fin r) Kf :=
  aeval fun v => if v.1 ∈ Fr.letters (segZ j) then X (mlOf Fr nL j v.1, v.2) else 0

def MlSpec (j : ZMod J) (y : ℤ) : Prop :=
  (∃ l : Fin (nL j), y = llPos Fr (segZ j) l.val ∧ mlOf Fr nL j y = ML.ll j l) ∨
  (∃ m : Fin r, y = Fr.fr (segZ j) (r - 1 - m.val) ∧ mlOf Fr nL j y = ML.lab j m) ∨
  (∃ m : Fin r, y = Fr.fr (segZ j - 1) (r - 1 - m.val) ∧ mlOf Fr nL j y = ML.wc (j - 1) m)

end Defs

def RestSpec : Prop :=
  ∀ (n' r : ℕ) [NeZero n'] [NeZero r] (Fr : Frames n' r) (L₁ N₁ : ℕ), Fr.Valid L₁ N₁ →
    ∀ (J : ℕ) [NeZero J] (nL : ZMod J → ℕ), (∀ j, nL j = (Fr.LLset (segZ j)).card) →
    ∀ (j : ZMod J), ∀ y ∈ Fr.letters (segZ j), MlSpec Fr nL j y

def RestTr : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (n' r K m : ℕ) [NeZero n'] [NeZero r] [NeZero K] (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O]
    (hk : m + 1 = r + K) (Fr : Frames n' r) (L₁ N₁ : ℕ), Fr.Valid L₁ N₁ → Even n' →
    ∀ (J : ℕ) [NeZero J] (Dt : SignedChainData p O r J), TieS Fr Dt →
    ∀ (A : ℤ → MvPolynomial (ℤ × Fin r) O),
      (∀ i : ℕ, i < Fr.J → A i ∈ supported O {v : ℤ × Fin r | v.1 ∈ Fr.letters i}) →
    ∀ (l : Fin n' × Fin (r + K) →₀ ℕ), IsLabel p Fr l →
    ∀ (ga : TV n' (m + 1) →₀ ℕ), PlaneEven r ga →
      levP Fr p hk Dt.nL (zPl p O hk Fr A l ga) =
        monomial (plMon Fr p hk Dt.nL (l.mapDomain (castV hk) + ga)) 1 *
          ∏ j : ZMod J, Dt.ph (chi Fr Dt.nL (KK O) j (MvPolynomial.map (algebraMap O (KK O)) (A (segZ j)))) ∧
      ∀ (j : ZMod J) (ll : Fin (Dt.nL j)) (a : Fin r), Dt.sgn j ll = false →
        plMon Fr p hk Dt.nL (l.mapDomain (castV hk) + ga) (⟨j, Sum.inl ll⟩, a) = 0

end Formalism.MainNotions.TraceSpectra
