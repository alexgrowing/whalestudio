import Formalism.SharpRestriction.GrowthBounds.AevalValuation.RestSpec
import Formalism.SharpRestriction.GrowthBounds.DiagonalSupport.MemSupportSumMonomial
import Formalism.SharpRestriction.GrowthBounds.PlaneCoefficients.DigOKAddInl
import Formalism.SharpRestriction.GrowthBounds.PlaneCoefficients.TensZeroRight

noncomputable section

open MvPolynomial Finset Classical

namespace Formalism.MainNotions.TraceSpectra

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.SourceCleaning Formalism.MainNotions.Pf14 Formalism.MainNotions.PlaneGramData Formalism.MainNotions.TestSideCounting Formalism.MainNotions.TestSideWords Formalism.MainNotions.PairMembershipBlocks

def filtQ {Kf : Type} [Field Kf] {ι : Type} {n : ℕ} (Q : (ι → ℕ) → Prop) (F : MvPolynomial (ι × Fin n) Kf) :
    MvPolynomial (ι × Fin n) Kf :=
  ∑ mo ∈ F.support.filter (fun mo => Q (fun i => multideg mo i)), monomial mo (F.coeff mo)

def VecOnly : Prop :=
  ∀ (Kf : Type) [Field Kf] (ι : Type) (n : ℕ) [NeZero n] (LL : Letters ι) (S : Set ι)
    (F : MvPolynomial (ι × Fin n) Kf), F ∈ supported Kf {v : ι × Fin n | v.1 ∈ S → LL.vec v.1 = true} →
    (0 : WithTop ℤ) ≤ valS LL S F

def ValFilt : Prop :=
  ∀ (Kf : Type) [Field Kf] (ι : Type) (n : ℕ) [NeZero n] (LL : Letters ι) (S : Set ι)
    (Q : (ι → ℕ) → Prop) (F : MvPolynomial (ι × Fin n) Kf), valS LL S F ≤ valS LL S (filtQ Q F)

def ValAeval : Prop :=
  ∀ (Kf : Type) [Field Kf] (ι κ : Type) (n : ℕ) [NeZero n] (LL : Letters ι) (LL' : Letters κ)
    (S L : Set ι) (S' : Set κ) (f : ι → κ) (g : ι × Fin n → MvPolynomial (κ × Fin n) Kf)
    (F : MvPolynomial (ι × Fin n) Kf), F ∈ supported Kf {v : ι × Fin n | v.1 ∈ L} →
    (∀ v : ι × Fin n, v.1 ∈ L → v.1 ∈ S → g v = X (f v.1, v.2) ∧ f v.1 ∈ S' ∧ LL'.vec (f v.1) = LL.vec v.1) →
    (∀ v : ι × Fin n, v.1 ∈ L → v.1 ∉ S → g v ∈ supported Kf {u : κ × Fin n | u.1 ∉ S'}) →
    valS LL S F ≤ valS LL' S' (aeval g F)

section Alg

variable {p : ℕ} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {r J : ℕ}

def phL {nL : ZMod J → ℕ} : ML J nL r → TL J nL r
  | ML.ll j l => ⟨j, Sum.inl l⟩
  | ML.lab j m => ⟨j, Sum.inr m⟩
  | ML.wc j m => ⟨j, Sum.inr m⟩
  | ML.tp j m _ => ⟨j, Sum.inr m⟩

def IsLW {nL : ZMod J → ℕ} : ML J nL r → Prop
  | ML.ll _ _ => True
  | ML.wc _ _ => True
  | _ => False

variable [NeZero J]

def phDeg (Dt : SignedChainData p O r J) (δ : ML J Dt.nL r → ℕ) : TL J Dt.nL r → ℕ
  | ⟨j, Sum.inl l⟩ => δ (ML.ll j l)
  | ⟨j, Sum.inr m⟩ => δ (ML.lab j m) + Dt.P j m * δ (ML.wc j m) + (if h : 1 ≤ m.val then δ (ML.tp j m h) else 0)

def phExp (Dt : SignedChainData p O r J) (M : ML J Dt.nL r × Fin r →₀ ℕ) : TL J Dt.nL r × Fin r →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun u => match u with
    | (⟨j, Sum.inl l⟩, a) => M (ML.ll j l, a)
    | (⟨j, Sum.inr m⟩, a) => M (ML.lab j m, a) + Dt.P j m * M (ML.wc j m, a) +
        (if h : 1 ≤ m.val then M (ML.tp j m h, a) else 0)

end Alg

def PhMon : Prop :=
  ∀ (p : ℕ) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (r J : ℕ) [NeZero J]
    (Dt : SignedChainData p O r J) (M : ML J Dt.nL r × Fin r →₀ ℕ) (c : KK O),
    Dt.ph (monomial M c) = monomial (phExp Dt M) c

def CompPh : Prop :=
  ∀ (p : ℕ) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (r J : ℕ) [NeZero J]
    (Dt : SignedChainData p O r J) (d : TL J Dt.nL r → ℕ) (β : TL J Dt.nL r × Fin r →₀ ℕ) (c : KK O)
    (F : MvPolynomial (ML J Dt.nL r × Fin r) (KK O)),
    compD d (monomial β c * Dt.ph F) =
      monomial β c * Dt.ph (filtQ (fun δ => ∀ x, multideg β x + phDeg Dt δ x = d x) F)

def FdigPh : Prop :=
  ∀ (p : ℕ) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (r J : ℕ) [NeZero J]
    (Dt : SignedChainData p O r J), (∀ j m, 0 < Dt.P j m) →
    ∀ (rho : (ZMod J × Fin r) × Fin r → ℕ) (β : TL J Dt.nL r × Fin r →₀ ℕ) (c : KK O)
      (F : MvPolynomial (ML J Dt.nL r × Fin r) (KK O)), F ∈ supported (KK O) {v | IsLW v.1} →
      Dt.Fdig rho (monomial β c * Dt.ph F) = if Dt.digOK rho β then monomial (liftMon Dt β) c * F else 0

def FdigSum : Prop :=
  ∀ (p : ℕ) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (r J : ℕ)
    (Dt : SignedChainData p O r J) (rho : (ZMod J × Fin r) × Fin r → ℕ) (α : Type) (s : Finset α)
    (f : α → MvPolynomial (TL J Dt.nL r × Fin r) (KK O)),
    Dt.Fdig rho (∑ i ∈ s, f i) = ∑ i ∈ s, Dt.Fdig rho (f i)

end Formalism.MainNotions.TraceSpectra
