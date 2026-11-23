import Formalism.SharpRestriction.GrowthBounds.DiagonalSupport.MembTop
import Formalism.SharpRestriction.GrowthBounds.DiagonalSupport.LowestWeightCNonpos

noncomputable section

open MvPolynomial Finset Classical

namespace Formalism.MainNotions.Proposition5Numerics

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.SourceCleaning Formalism.MainNotions.Pf14 Formalism.MainNotions.PlaneGramData Formalism.MainNotions.TestSideCounting Formalism.MainNotions.TestSideWords

def SLt {J : ℕ} (j : ZMod J) (x : ℤ) : Set (ZMod J × ℤ) := {i | i.1 = j ∧ i.2 < x}

def SLe {J : ℕ} (j : ZMod J) (x : ℤ) : Set (ZMod J × ℤ) := {i | i.1 = j ∧ i.2 ≤ x}

section At

variable (p : ℕ) {n' r K : ℕ} [NeZero n'] [NeZero r] [NeZero K] (O : Type) [CommRing O] [IsDomain O]
  [IsDiscreteValuationRing O] (Fr : Frames n' r) (deg : Fin n' → ℕ) (Y : ℝ) (N₁ G' cP : ℕ)
  {J : ℕ} [NeZero J] (Dt : SignedChainData p O r J) (dNo : TL J Dt.nL r → ℕ)
  (ka : ZMod J → ℕ → Fin K → ℤ)
  (No : MvPolynomial (TL J Dt.nL r × Fin K) O) (Go : MvPolynomial (ML J Dt.nL r × Fin r) O)

def pU (j : ZMod J) (u : ℕ) : ℤ := posU Fr (Dt.nL j) (segZ j) u

def tauU (j : ZMod J) (u : ℕ) : ℝ :=
  thStar Fr p deg Y (r + K) (mStar p Fr (r + K) N₁ (p ^ G') cP) Dt.nL K ka j u -
    slU Fr p deg Y (r + K) Dt.nL j u / 2 - 60 * (cP : ℝ)

def ValBd : Prop :=
  (∀ j u, u < Dt.nL j + r →
    geZ (valS (LSeg J) (SLt j (pU p O Fr Dt j u)) (xiPl Fr O Dt.nL Go)) (tauU p O Fr deg Y N₁ G' cP Dt ka j u)) ∧
  (∀ j u, u < Dt.nL j →
    geZ (valS (LSeg J) (SLe j (pU p O Fr Dt j u)) (xiPl Fr O Dt.nL Go)) (tauU p O Fr deg Y N₁ G' cP Dt ka j (u + 1))) ∧
  ∀ j u, u < Dt.nL j + r →
    lam1S (LSeg J) (SLt j (pU p O Fr Dt j u)) (xiNo Fr O K Dt.nL No) ≤ ((ka j u 0 + 4 * (cP : ℤ) : ℤ) : WithBot ℤ) ∧
    lam1S (LSeg J) (SLe j (pU p O Fr Dt j u)) (xiNo Fr O K Dt.nL No) ≤ ((ka j (u + 1) 0 + 4 * (cP : ℤ) : ℤ) : WithBot ℤ)

def dNoOf (i : ZMod J × ℤ) : ℕ := ∑ x : TL J Dt.nL r, if tlPos Fr Dt.nL x = i then dNo x else 0

def SuppOK : Prop :=
  (∀ mo ∈ (xiPl Fr O Dt.nL Go).support, ∀ v ∈ mo.support, v.1.2 ∈ Fr.letters (segZ v.1.1)) ∧
  ∀ mo ∈ (xiNo Fr O K Dt.nL No).support,
    (∀ v ∈ mo.support, v.1.2 ∈ Fr.letters (segZ v.1.1) ∧ ¬ Fr.IsW (segZ v.1.1) v.1.2) ∧
    ∀ i, multideg mo i = dNoOf p O Fr Dt dNo i

def PlOK (δ : ZMod J × ℤ → ℕ) (j : ZMod J) (A : MvPolynomial (ℤ × Fin r) O) : Prop :=
  A ∈ supported O {v : ℤ × Fin r | v.1 ∈ Fr.letters (segZ j)} ∧
  (∀ mo ∈ A.support, ∀ x, multideg mo x = δ (j, x)) ∧
  (∀ u, u < Dt.nL j + r →
    ((⌈tauU p O Fr deg Y N₁ G' cP Dt ka j u⌉ : ℤ) : WithTop ℤ) ≤ valS LZ {y | y < pU p O Fr Dt j u} A) ∧
  ∀ u, u < Dt.nL j →
    ((⌈tauU p O Fr deg Y N₁ G' cP Dt ka j (u + 1)⌉ : ℤ) : WithTop ℤ) ≤ valS LZ {y | y ≤ pU p O Fr Dt j u} A

def NoOK (j : ZMod J) (B : MvPolynomial (ℤ × Fin K) O) : Prop :=
  B ∈ supported O {v : ℤ × Fin K | v.1 ∈ Fr.letters (segZ j) ∧ ¬ Fr.IsW (segZ j) v.1} ∧
  (∀ mo ∈ B.support, ∀ x, multideg mo x = dNoOf p O Fr Dt dNo (j, x)) ∧
  ∀ u, u < Dt.nL j + r →
    lam1S LZ {y | y < pU p O Fr Dt j u} B ≤ ((ka j u 0 + 4 * (cP : ℤ) : ℤ) : WithBot ℤ) ∧
    lam1S LZ {y | y ≤ pU p O Fr Dt j u} B ≤ ((ka j (u + 1) 0 + 4 * (cP : ℤ) : ℤ) : WithBot ℤ)

def XXAt : Prop :=
  ∀ (δ : ZMod J × ℤ → ℕ) (j : ZMod J) (A : MvPolynomial (ℤ × Fin r) O) (B : MvPolynomial (ℤ × Fin K) O),
    PlOK p O Fr deg Y N₁ G' cP Dt ka δ j A → NoOK p O Fr cP Dt dNo ka j B →
    plEmb O r K A * nmEmb O r K B ∈ XX' O r K Fr (segZ j) (fun _ => (mStar p Fr (r + K) N₁ (p ^ G') cP : ℤ))
      (fun x => Bo p Fr deg (segZ j) x / 2 - sl p Fr deg Y (r + K) (segZ j) x)
      (fun x => ((δ (j, x) + dNoOf p O Fr Dt dNo (j, x) : ℕ) : ℝ)) ∧
    plEmb O r K A * nmEmb O r K B ∈ restrictSupport O {mm | ∀ x ∈ Fr.letters (segZ j),
      ∑ c : Fin (r + K), mm (x, c) = δ (j, x) + dNoOf p O Fr Dt dNo (j, x)}

def DdAt : Prop :=
  ∀ δ : ZMod J × ℤ → ℕ, Occ p O Fr Dt Go δ → ∀ (j : ZMod J), ∀ x ∈ Fr.letters (segZ j),
    (Fr.IsW (segZ j) x ∨ x ∈ Fr.LLset (segZ j)) →
    ((δ (j, x) + dNoOf p O Fr Dt dNo (j, x) : ℕ) : ℝ) ≤
      levDeg p Fr deg (segZ j) x + levDeg p Fr deg (segZ j) x / 100

end At

def RestValBdG : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] {n' r K : ℕ} [NeZero n'] [NeZero r] [NeZero K] (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] (_S : UniformizedDVR p O) (Fr : Frames n' r) (TT : Finset (Fin n'))
    (L₁ L₂ N₁ G' : ℕ) (deg d : Fin n' → ℕ) (Y : ℝ) (cP : ℕ), MFH p Fr TT L₁ L₂ N₁ G' deg d Y (r + K) cP →
    ∀ (J : ℕ) [NeZero J] (Dt : SignedChainData p O r J) (dPl dNo : TL J Dt.nL r → ℕ) (ka : ZMod J → ℕ → Fin K → ℤ)
      (rho : TL J Dt.nL r × Fin (r + K) → ℕ) (No : MvPolynomial (TL J Dt.nL r × Fin K) O)
      (Go : MvPolynomial (ML J Dt.nL r × Fin r) O),
      MH p O Fr deg Y N₁ G' cP d Dt dPl dNo ka rho No Go →
      ValBd p O Fr deg Y N₁ G' cP Dt ka No Go ∧ SuppOK p O Fr Dt dNo No Go

def RestXXG : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] {n' r K : ℕ} [NeZero n'] [NeZero r] [NeZero K] (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] (_S : UniformizedDVR p O) (Fr : Frames n' r) (TT : Finset (Fin n'))
    (L₁ L₂ N₁ G' : ℕ) (deg d : Fin n' → ℕ) (Y : ℝ) (cP : ℕ), MFH p Fr TT L₁ L₂ N₁ G' deg d Y (r + K) cP →
    ∀ (J : ℕ) [NeZero J] (Dt : SignedChainData p O r J) (dPl dNo : TL J Dt.nL r → ℕ) (ka : ZMod J → ℕ → Fin K → ℤ),
      SignedChainDegreeCondition p O Fr deg Y N₁ G' cP Dt dPl ka → XXAt p O Fr deg Y N₁ G' cP Dt dNo ka

def RestDdG : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] {n' r K : ℕ} [NeZero n'] [NeZero r] [NeZero K] (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] (_S : UniformizedDVR p O) (Fr : Frames n' r) (TT : Finset (Fin n'))
    (L₁ L₂ N₁ G' : ℕ) (deg d : Fin n' → ℕ) (Y : ℝ) (cP : ℕ), MFH p Fr TT L₁ L₂ N₁ G' deg d Y (r + K) cP →
    ∀ (J : ℕ) [NeZero J] (Dt : SignedChainData p O r J) (dPl dNo : TL J Dt.nL r → ℕ) (ka : ZMod J → ℕ → Fin K → ℤ)
      (rho : TL J Dt.nL r × Fin (r + K) → ℕ) (No : MvPolynomial (TL J Dt.nL r × Fin K) O)
      (Go : MvPolynomial (ML J Dt.nL r × Fin r) O),
      MH p O Fr deg Y N₁ G' cP d Dt dPl dNo ka rho No Go → DdAt p O Fr deg Dt dNo Go

end Formalism.MainNotions.Proposition5Numerics
