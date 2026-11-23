import Formalism.LocalToGlobal.Columns.HeckeSp
import Formalism.LocalToGlobal.Columns.StdLatUnimodular
import Formalism.LocalToGlobal.Columns.Adelic
import Formalism.LocalToGlobal.Columns.ScaledRamifiedLattice
import Formalism.LogVandermondeBounds.LogRatioLowerBound
import Formalism.GradedWeylDivisibility.StatementD
import Formalism.HermitianLattices.StatementMass
import Formalism.FlagUnipotentLattices.MemOfOrthogonalAnisotropic
import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms

noncomputable section

namespace Formalism.L2.Col

open Module Module.End Polynomial

section Link

variable {L Pl Pt : Type} [Field L]

def ZSubHasBlocks (n : ℕ) (q : Pl → ℕ) (t : ℕ) (bl : List (Pl → L)) (sys : Pt → Pl × ℕ → L) (Z : Set Pt) : Prop :=
  ∀ x ∈ Z, HasBlocks n q t bl (sys x)

theorem ZSubHasBlocks.mono {n : ℕ} {q : Pl → ℕ} {t : ℕ} {bl : List (Pl → L)} {sys : Pt → Pl × ℕ → L} {Z Z' : Set Pt}
    (h : ZSubHasBlocks n q t bl sys Z) (hZ : Z' ⊆ Z) : ZSubHasBlocks n q t bl sys Z' :=
  fun x hx => h x (hZ hx)

def heckeRenorm (n : ℕ) (q : Pl → ℕ) (a : Pl × ℕ → L) : Pl × ℕ → L :=
  fun y => (q y.1 : L) ^ (y.2 * (n - 1)) * a y

end Link

section Conc

open NumberField IsDedekindDomain Formalism.HermitianLatticesTheory

variable {K : Type} [Field K] [NumberField K] [StarRing K]
variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}
  {ST SG : Finset (HeightOneSpectrum (𝓞 E))} {S : GSD K}

def ZSubHasBlocksC (c : DecoPts S E n ST SG) (S0 : Set (HeightOneSpectrum (𝓞 E))) (t : ℕ)
    (bl : List (LevOff ST SG S0 → K)) (Z : Set (hAlg K (heckeFam c S0) →ₐ[K] K)) : Prop :=
  ZSubHasBlocks n SplitOff.q t bl (fun ψ => sysOf ψ) Z

end Conc

section Genus

open NumberField Formalism.HermitianLatticesTheory Formalism.BasicNotions

def UnimodGenusLoc (E : Type) [Field E] [NumberField E] [StarRing E] (n : ℕ) : Prop :=
  IsCMUnram E → ∀ N : Submodule (𝓞 E) (Sp E n), Submodule.IsLattice E N → IsUnimodular (hStd E n) N →
    SameGenus (hStd E n) (stdLat E n) N

def UnimodGenusLocAll : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (n : ℕ), UnimodGenusLoc E n

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
variable (hc : Formalism.BasicNotions.CMData F E) (n : ℕ) [NeZero n]

def UnimodGenus : Prop :=
  ∀ N : Submodule (𝓞 E) (Sp E n), Submodule.IsLattice E N → Formalism.HermitianLatticesTheory.IsUnimodular (hStd E n) N →
    ∃ x ∈ UAd hc n, Formalism.UG.CS.globLat x (stdLat E n) = N

end Genus

section Counting

open NumberField Formalism.HermitianLatticesTheory Formalism.BasicNotions

abbrev MassRatioStd : Prop := Formalism.HermitianLatticesTheory.SiegelMassRatio

def wSeq {n : ℕ} (lam : DomWeight n) : ℕ → ℝ := fun i => if h : i < n then ((lam.w ⟨i, h⟩ : ℤ) : ℝ) - i else 0

def WeylDim {n : ℕ} (lam : DomWeight n) : Prop :=
  (Nat.card (Formalism.GradedWeylDivisibility.ssIdx n n lam.natW) : ℝ) = Formalism.LogVandermondeBounds.StandardLattice.dimVN (wSeq lam) n

end Counting

section Alcove

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.DIV

abbrev NablaMemDeltaLocallyAtLargePrime : Prop := Formalism.BasicNotions.NablaMemDeltaLocallyAtLargePrime

def DeltaEqNablaLatticeLargePrime : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (ι : Type) [Fintype ι] (n : ℕ) (lam : ι → DomWeight n)
    (w : HeightOneSpectrum (𝓞 K)), (∀ τ, (lam τ).spread < (prW w : ℤ)) →
    ∀ M : ι → Submodule (𝓞 K) (Fin n → K), (∀ τ, Submodule.IsLattice K (M τ)) →
      atW w (delK lam M) = atW w (nabK lam M)

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)

def DeltaEqNablaAtWordPrime : Prop :=
  ∀ (u : Pr.Word) (j : ℕ), j ≤ R.m → ∀ w : HeightOneSpectrum (𝓞 X.K), prW w = Pr.T u →
    SwC W Ch u j w = SwNabC W Ch u j w ∧ ∀ P : {P // P ∈ Pr.vT u}, BvWC W Ch u j w P = BvNabWC W Ch u j w P

end Alcove

abbrev MinkowskiBound : Prop := Formalism.HermitianLatticeCounting.S6.MinkowskiBound

section FormalDegree

open MeasureTheory

def HCFormalDegreeCD : Prop :=
  ∀ (C : Formalism.BasicNotions.CDHaar) (n P Q : ℕ) (ε : Fin n → Bool) (e : Fin P ⊕ Fin Q ≃ Fin n),
    (∀ i, ε (e (Sum.inl i)) = true) → (∀ j, ε (e (Sum.inr j)) = false) →
    ∀ μ : Measure (Formalism.REAL.UJ ε),
      (∀ A : Set (Formalism.REAL.UJ ε), MeasurableSet A →
        μ A = C.cd P Q {g | ∃ a ∈ A, Formalism.MainNotions.S.umat a = Matrix.reindex e e (Formalism.BasicNotions.UpqT.mat g)}) →
    ∀ lam : Fin n → ℝ, Formalism.QuantumDeterminants.IsHCParam lam →
    ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (w : H),
      Formalism.MainNotions.S.IsDS ε lam σ → w ≠ 0 → Formalism.MainNotions.S.fdegOf μ σ w = Formalism.QuantumDeterminants.fdegHC lam

end FormalDegree

end Formalism.L2.Col
