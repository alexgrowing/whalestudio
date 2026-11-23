import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LatticeFactsAt
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TranslateMomentsAll
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TranslateJets

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.L2.Th1.H GlobalTheory.MomT
open GlobalTheory.IndefiniteRowSideFullHecke.BadPrimesPeriodBound (recFields recPrimes recSeam HostTie AnTie badS)
open GlobalTheory.IndefiniteRowSideFullHecke.CharacterValuation (StdOver)

noncomputable section

namespace GlobalTheory.DatumJets

def SplitSet {X : Fields} (A : Amb X) (a b : ℕ) (S : Finset (HeightOneSpectrum (𝓞 X.E))) (ϖ : 𝓞 X.E) (p : ℕ) : Prop :=
  X.Ok ∧ A.LaHyp a b S ∧ A.AA ≠ ⊥ ∧ A.ESmooth a b ∧ p.Prime ∧ ϖ * X.conjO ϖ = (p : 𝓞 X.E) ∧ IsCoprime ϖ (X.conjO ϖ) ∧
    ∀ P : HeightOneSpectrum (𝓞 X.E), ϖ ∈ P.asIdeal → P ∈ S

def TranslateInt {X : Fields} (A : Amb X) {a b : ℕ} (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b))
    {p : ℕ} [Fact p.Prime] (lam : TaylorLogMetric.Qbar →+* ℂ_[p]) (π : X.E) (κ : ℂ) (e : DVar X.Tau a b →₀ ℕ) : Prop :=
  ∀ (s : HomE X.E a b) (n : ℕ), Nat.Coprime n p → ((n : X.E) * π) • s ∈ per A N N' →
    GlobalTheory.IndefiniteRowSideFullHecke.IntegralityWeylConditions.IntAt lam (κ * jetC A.cD (Wx A s (A.e a b N N')) e)

def HalfInclusions : Prop :=
  ∀ (X : Fields) (A : Amb X) (a b : ℕ) (S SG : Finset (HeightOneSpectrum (𝓞 X.E))) (ϖ : 𝓞 X.E) (p cA c : ℕ)
    (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)),
    SplitSet A a b S ϖ p → (∀ P ∈ SG, P ∈ S ∧ ϖ ∉ P.asIdeal) → IsSdLat N → IsSdLat N' → 0 < cA → 0 < c → p ∣ c →
    ∃ (n₀ k : ℕ) (r : 𝓞 X.E), Nat.Coprime n₀ p ∧ r ≠ 0 ∧
      (∀ y ∈ per A N N', ((n₀ : X.E) * (ϖ : X.E) ^ (k + 1)) • y ∈ halfBO S (per A N N') c) ∧
      (∀ y ∈ halfBO S (per A N N') c, (c : X.E) • y ∈ per A N N' ∧
        (star (r : X.E) • y ∈ per A N N' → ((n₀ : X.E) * star (ϖ : X.E)) • y ∈ per A N N')) ∧
      (∀ x ∈ homAt (divs ϖ) N N', ∀ t ∈ halfAO S (per A N N') (cA * c), t - x ∈ mulLat c (homAt S N N') →
        (n₀ : X.E) • t ∈ per A N N') ∧
      (∀ y ∈ per A N N', y ∈ homAt S N N' ∧ (r : X.E) • y ∈ halfAO S (per A N N') (cA * c) ∧
        (r : X.E) • y ∈ mulLat p (homAt (divs ϖ) N N') ∧ (r : X.E) • y ∈ mulLat c (homAt SG N N') ∧
        ((r : X.E) • y ∈ mulLat c (homAt S N N') ↔ y ∈ smulLat ((ϖ : X.E) ^ k) (per A N N')) ∧
        (y ∈ mulLat c (homAt S N N') → y ∈ halfBO S (per A N N') c)) ∧
      (∀ y ∈ mulLat c (homAt S N N'), y ∈ mulLat p (homAt (divs ϖ) N N') ∧ y ∈ mulLat c (homAt SG N N') ∧
        y ∈ divLat cA (homAt S N N'))

def MultipleIndex : Prop :=
  ∀ (X : Fields) (A : Amb X) (a b : ℕ) (ϖ : 𝓞 X.E) (p : ℕ) (N : Submodule (𝓞 X.E) (Sp X.E a))
    (N' : Submodule (𝓞 X.E) (Sp X.E b)), X.Ok → A.AA.FG → A.AA ≠ ⊥ → IsSdLat N → IsSdLat N' → p ≠ 0 →
    ϖ * X.conjO ϖ = (p : 𝓞 X.E) →
    (smulLat (ϖ : X.E) (per A N N')).toAddSubgroup.relIndex (per A N N').toAddSubgroup = p ^ (X.f * a * b)

def PlaceAbove : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (σ : K →+* ℂ) (p : ℕ) [Fact p.Prime] (w : HeightOneSpectrum (𝓞 K)),
    (p : 𝓞 K) ∈ w.asIdeal →
    ∃ lam : TaylorLogMetric.Qbar →+* ℂ_[p], ∀ k : K, GlobalTheory.IndefiniteRowSideFullHecke.IntegralityWeylConditions.IntAt lam (σ k) ↔ w.valuation K k ≤ 1

def TranslatesAt {X : Fields} (Pr : Primes X) (A : Amb X) : Prop :=
  ∀ (i : Fin 2) (p : ℕ) [Fact p.Prime] (lam : TaylorLogMetric.Qbar →+* ℂ_[p]), p = Pr.g i →
    ∀ (a b : ℕ) (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)), Even a → Even b →
      IsSdLat N → IsSdLat N' → StdOver p N → StdOver p N' →
      ∀ e : DVar X.Tau a b →₀ ℕ, e.degree + 1 < p →
        TranslateInt A N N' lam ((Pr.piG i : 𝓞 X.E) : X.E)
          (A.σ₀ (e.prod fun k n => X.emb k.1 (star ((Pr.piG i : 𝓞 X.E) : X.E)) ^ n)) e

def RecordTranslates : Prop :=
  ∀ (D : D7) (EX : ErrX D) (δ : ℂ) (B : Base D D.host.ccK δ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ),
    HostTie EX → AnTie D δ χ cD → B.VecP χ → B.IntP χ → GlobalTheory.ColPeriod.LatticeFactsAt (ambOf (recSeam D) B χ cD) →
    TranslatesAt (recPrimes EX) (ambOf (recSeam D) B χ cD)

def TypePrimeBadPrimesLevelsHypotheses : Prop :=
  ∀ (D : D7) (EX : ErrX D) (sel : HeightOneSpectrum (𝓞 D.host.F) → HeightOneSpectrum (𝓞 D.host.E)) (δ : ℂ)
    (B : Base D D.host.ccK δ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ), HostTie EX → IsSel (recFields D) sel →
    ∀ (i : Fin 2) (u : (recPrimes EX).Word) (mu : Tup (recFields D).F (recFields D).E (recFields D).K (badS D))
      (cst : LocCst (recFields D) (rowSG (recPrimes EX) sel mu)), cst.Ok →
    ∀ a b : ℕ, (ambOf (recSeam D) B χ cD).LaHyp a b ∅ → (ambOf (recSeam D) B χ cD).ESmooth a b →
      SplitSet (ambOf (recSeam D) B χ cD) a b (Sall sel mu u) ((recFields D).conjO ((recPrimes EX).piG i))
        ((recPrimes EX).g i) ∧
      0 < cAof sel mu cst ∧ 0 < cBof sel mu cst u ∧ (recPrimes EX).g i ∣ cBof sel mu cst u

end GlobalTheory.DatumJets
