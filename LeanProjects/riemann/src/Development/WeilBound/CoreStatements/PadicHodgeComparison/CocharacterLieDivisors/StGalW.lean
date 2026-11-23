import Development.WeilBound.CoreStatements.PadicHodgeComparison.CocharacterLieDivisors.HTDistinctMult
import Development.WeilBound.CoreStatements.PadicHodgeComparison.CocharacterLieDivisors.DivWCoreLacUseType

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp Polynomial
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.AutomorphicGaloisHodgeTate.Div

def FrobKills {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] {l : ℕ} [Fact l.Prime] {N : ℕ}
    (V : G E Ω →* GL (Fin N) (Qbar l)) (w : HeightOneSpectrum (𝓞 E)) (f : (Qbar l)[X]) : Prop :=
  ∀ A : ValuationSubring Ω, IsPlaceOver A w → (∀ s ∈ Ine (F := E) A, V s = 1) ∧
    ∀ σ : G E Ω, IsFrob A (normV w) σ → aeval (V σ⁻¹ : Matrix (Fin N) (Fin N) (Qbar l)) f = 0

def HTLac {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {l : ℕ}
    [Fact l.Prime] {N : ℕ} (V : G E Ω →* GL (Fin N) (Qbar l)) (n : ℕ) : Prop :=
  ∃ (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) ∧
    ∃ (w : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω), ((l : ℕ) : 𝓞 E) ∈ w.asIdeal ∧ IsPlaceOver A w ∧
    ∃ (O : Type) (_ : CommRing O) (_ : Algebra ℤ_[l] O) (_ : TopologicalSpace O)
      (Bw : LocBridge l E Ω (Dec (F := E) A) O), GlobalTheory.Pst.Induces Bw ∧
    ∃ (τ : E →+* Qbar l) (J : Multiset ℤ), IsJumpsAt P Bw (V.comp (Dec (F := E) A).subtype) τ J ∧
      ∃ ks : Fin n → ℤ, Function.Injective ks ∧ (∀ i, ks i ∈ J) ∧ IsLac (fun i => ((ks i : ℤ) : ℚ))

def SenWLac : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (l : ℕ) [Fact l.Prime] (N n : ℕ) (V : G E Ω →* GL (Fin N) (Qbar l)), Continuous V → HTLac V n →
    ∃ (K' : Type) (_ : Field K') (_ : IsAlgClosed K') (_ : Algebra (Qbar l) K')
      (X : Matrix (Fin N) (Fin N) K'), InLieZar V X ∧
        ∃ e : Fin n → K', Function.Injective e ∧ IsLac e ∧ ∀ i, X.charpoly.IsRoot (e i)

def DivWGal : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (l : ℕ) [Fact l.Prime] (N n : ℕ),
    ∀ V : G E Ω →* GL (Fin N) (Qbar l), Continuous V → IsSSRep V →
    ∀ (S : Set (HeightOneSpectrum (𝓞 E))), NumberField.Set.HasDirichletDensity S 1 →
    ∀ (P : HeightOneSpectrum (𝓞 E) → (Qbar l)[X]), (∀ w ∈ S, (P w).Monic ∧ (P w).natDegree = n) →
      (∀ w ∈ S, FrobKills V w (P w)) →
      HTLac V n →
    ∀ (ψ : G E Ω →* (Qbar l)ˣ), Continuous (fun g : G E Ω => ((ψ g : (Qbar l)ˣ) : Qbar l)) →
      (∀ w ∈ S, ∀ A : ValuationSubring Ω, IsPlaceOver A w → ∀ σ : G E Ω, IsFrob A (normV w) σ →
        ((ψ σ⁻¹ : (Qbar l)ˣ) : Qbar l) = (-1) ^ n * (P w).coeff 0) →
    ∃ r : G E Ω →* GL (Fin n) (Qbar l), Continuous r ∧ IsSSRep r ∧
      (∃ A : Matrix (Fin N) (Fin n) (Qbar l), A.rank = n ∧
        ∀ g : G E Ω, (V g : Matrix (Fin N) (Fin N) (Qbar l)) * A = A * (r g : Matrix (Fin n) (Fin n) (Qbar l))) ∧
      (∀ g : G E Ω, (r g : Matrix (Fin n) (Fin n) (Qbar l)).det = ((ψ g : (Qbar l)ˣ) : Qbar l)) ∧
      (∃ S' ⊆ S, Dense {σ : G E Ω | ∃ w ∈ S', ∃ A : ValuationSubring Ω, IsPlaceOver A w ∧ IsFrob A (normV w) σ} ∧
        ∀ w ∈ S', FrobCP r w (P w)) ∧
      (∀ w ∈ S, ProdGen n (P w) → FrobCP r w (P w))

def DivWGalUse : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (l : ℕ) [Fact l.Prime] (N N₀ n : ℕ),
    ∀ V : G E Ω →* GL (Fin N) (Qbar l), Continuous V → IsSSRep V →
    ∀ V₀ : G E Ω →* GL (Fin N₀) (Qbar l), Continuous V₀ →
      (∃ A₀ : Matrix (Fin N) (Fin N₀) (Qbar l), A₀.rank = N₀ ∧
        ∀ g : G E Ω, (V g : Matrix (Fin N) (Fin N) (Qbar l)) * A₀ = A₀ * (V₀ g : Matrix (Fin N₀) (Fin N₀) (Qbar l))) →
    ∀ (S : Set (HeightOneSpectrum (𝓞 E))), NumberField.Set.HasDirichletDensity S 1 →
    ∀ (P : HeightOneSpectrum (𝓞 E) → (Qbar l)[X]), (∀ w ∈ S, (P w).Monic ∧ (P w).natDegree = n) →
      (∀ w ∈ S, FrobKills V w (P w)) →
      HTLac V₀ n →
    ∀ (ψ : G E Ω →* (Qbar l)ˣ), Continuous (fun g : G E Ω => ((ψ g : (Qbar l)ˣ) : Qbar l)) →
      (∀ w ∈ S, ∀ A : ValuationSubring Ω, IsPlaceOver A w → ∀ σ : G E Ω, IsFrob A (normV w) σ →
        ((ψ σ⁻¹ : (Qbar l)ˣ) : Qbar l) = (-1) ^ n * (P w).coeff 0) →
    ∃ r : G E Ω →* GL (Fin n) (Qbar l), Continuous r ∧ IsSSRep r ∧
      (∃ A : Matrix (Fin N₀) (Fin n) (Qbar l), A.rank = n ∧
        ∀ g : G E Ω, (V₀ g : Matrix (Fin N₀) (Fin N₀) (Qbar l)) * A = A * (r g : Matrix (Fin n) (Fin n) (Qbar l))) ∧
      (∃ (k : ℕ) (B : Matrix (Fin n × Fin k) (Fin N) (Qbar l)), B.rank = N ∧
        ∀ g : G E Ω, Matrix.kronecker (r g : Matrix (Fin n) (Fin n) (Qbar l)) (1 : Matrix (Fin k) (Fin k) (Qbar l)) * B =
          B * (V g : Matrix (Fin N) (Fin N) (Qbar l))) ∧
      (∀ g : G E Ω, (r g : Matrix (Fin n) (Fin n) (Qbar l)).det = ((ψ g : (Qbar l)ˣ) : Qbar l)) ∧
      (∃ S' ⊆ S, Dense {σ : G E Ω | ∃ w ∈ S', ∃ A : ValuationSubring Ω, IsPlaceOver A w ∧ IsFrob A (normV w) σ} ∧
        ∀ w ∈ S', FrobCP r w (P w)) ∧
      (∀ w ∈ S, ProdGen n (P w) → FrobCP r w (P w))

def HTDistinct {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {l : ℕ}
    [Fact l.Prime] {N : ℕ} (V : G E Ω →* GL (Fin N) (Qbar l)) (n : ℕ) : Prop :=
  ∃ (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) ∧
    ∃ (w : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω), ((l : ℕ) : 𝓞 E) ∈ w.asIdeal ∧ IsPlaceOver A w ∧
    ∃ (O : Type) (_ : CommRing O) (_ : Algebra ℤ_[l] O) (_ : TopologicalSpace O)
      (Bw : LocBridge l E Ω (Dec (F := E) A) O), GlobalTheory.Pst.Induces Bw ∧
    ∃ (τ : E →+* Qbar l) (J : Multiset ℤ), IsJumpsAt P Bw (V.comp (Dec (F := E) A).subtype) τ J ∧
      ∃ ks : Fin n → ℤ, Function.Injective ks ∧ ∀ i, ks i ∈ J

def SenWDistinct : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (l : ℕ) [Fact l.Prime] (N n : ℕ) (V : G E Ω →* GL (Fin N) (Qbar l)), Continuous V → HTDistinct V n →
    ∃ (K' : Type) (_ : Field K') (_ : IsAlgClosed K') (_ : Algebra (Qbar l) K')
      (X : Matrix (Fin N) (Fin N) K'), InLieZar V X ∧
        ∃ e : Fin n → K', Function.Injective e ∧ ∀ i, X.charpoly.IsRoot (e i)

def GenCosets {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] {l : ℕ} [Fact l.Prime] {N : ℕ}
    (V : G E Ω →* GL (Fin N) (Qbar l)) (S : Set (HeightOneSpectrum (𝓞 E)))
    (P : HeightOneSpectrum (𝓞 E) → (Qbar l)[X]) (n : ℕ) : Prop :=
  ∀ H : Subgroup (G E Ω), H.Normal → IsOpen (H : Set (G E Ω)) → V.ker ≤ H →
    Nat.card (G E Ω ⧸ H) ≤ n.factorial → ∀ g : G E Ω,
      ∃ w ∈ S, ∃ A : ValuationSubring Ω, IsPlaceOver A w ∧ ∃ σ : G E Ω, IsFrob A (normV w) σ ∧
        g⁻¹ * σ⁻¹ ∈ H ∧ WGen n (P w)

def DivWGalAny : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (l : ℕ) [Fact l.Prime] (N n : ℕ),
    ∀ V : G E Ω →* GL (Fin N) (Qbar l), Continuous V → IsSSRep V →
    ∀ (S : Set (HeightOneSpectrum (𝓞 E))), NumberField.Set.HasDirichletDensity S 1 →
    ∀ (P : HeightOneSpectrum (𝓞 E) → (Qbar l)[X]), (∀ w ∈ S, (P w).Monic ∧ (P w).natDegree = n) →
      (∀ w ∈ S, FrobKills V w (P w)) →
      (HTLac V n ∨ (HTDistinct V n ∧ GenCosets V S P n)) →
    ∀ (ψ : G E Ω →* (Qbar l)ˣ), Continuous (fun g : G E Ω => ((ψ g : (Qbar l)ˣ) : Qbar l)) →
      (∀ w ∈ S, ∀ A : ValuationSubring Ω, IsPlaceOver A w → ∀ σ : G E Ω, IsFrob A (normV w) σ →
        ((ψ σ⁻¹ : (Qbar l)ˣ) : Qbar l) = (-1) ^ n * (P w).coeff 0) →
    ∃ r : G E Ω →* GL (Fin n) (Qbar l), Continuous r ∧ IsSSRep r ∧
      (∃ A : Matrix (Fin N) (Fin n) (Qbar l), A.rank = n ∧
        ∀ g : G E Ω, (V g : Matrix (Fin N) (Fin N) (Qbar l)) * A = A * (r g : Matrix (Fin n) (Fin n) (Qbar l))) ∧
      (∃ (k : ℕ) (B : Matrix (Fin n × Fin k) (Fin N) (Qbar l)), B.rank = N ∧
        ∀ g : G E Ω, Matrix.kronecker (r g : Matrix (Fin n) (Fin n) (Qbar l)) (1 : Matrix (Fin k) (Fin k) (Qbar l)) * B =
          B * (V g : Matrix (Fin N) (Fin N) (Qbar l))) ∧
      (∀ g : G E Ω, (r g : Matrix (Fin n) (Fin n) (Qbar l)).det = ((ψ g : (Qbar l)ˣ) : Qbar l)) ∧
      (∃ S' ⊆ S, Dense {σ : G E Ω | ∃ w ∈ S', ∃ A : ValuationSubring Ω, IsPlaceOver A w ∧ IsFrob A (normV w) σ} ∧
        ∀ w ∈ S', FrobCP r w (P w)) ∧
      (∀ w ∈ S, ProdGen n (P w) → FrobCP r w (P w))

end PositivityTheory.AutomorphicGaloisHodgeTate.Div
