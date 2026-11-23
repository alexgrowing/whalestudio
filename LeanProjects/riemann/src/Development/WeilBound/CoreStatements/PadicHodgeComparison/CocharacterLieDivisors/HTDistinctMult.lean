import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsWeight
import Development.WeilBound.CoreStatements.PadicHodgeComparison.CocharacterLieDivisors.MeetsOpenCosets

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp Polynomial
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.AutomorphicGaloisHodgeTate.Div

def FrobCP {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] {l : ℕ} [Fact l.Prime] {N : ℕ}
    (V : G E Ω →* GL (Fin N) (Qbar l)) (w : HeightOneSpectrum (𝓞 E)) (f : (Qbar l)[X]) : Prop :=
  ∀ A : ValuationSubring Ω, IsPlaceOver A w → (∀ s ∈ Ine (F := E) A, V s = 1) ∧
    ∀ σ : G E Ω, IsFrob A (normV w) σ → (V σ⁻¹ : Matrix (Fin N) (Fin N) (Qbar l)).charpoly = f

def HTDistinctMult {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {l : ℕ}
    [Fact l.Prime] {N : ℕ} (V : G E Ω →* GL (Fin N) (Qbar l)) (n m : ℕ) : Prop :=
  ∃ (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) ∧
    ∃ (w : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω), ((l : ℕ) : 𝓞 E) ∈ w.asIdeal ∧ IsPlaceOver A w ∧
    ∃ (O : Type) (_ : CommRing O) (_ : Algebra ℤ_[l] O) (_ : TopologicalSpace O)
      (Bw : LocBridge l E Ω (Dec (F := E) A) O), GlobalTheory.Pst.Induces Bw ∧
    ∃ (τ : E →+* Qbar l) (ks : Finset ℤ), ks.card = n ∧
      IsJumpsAt P Bw (V.comp (Dec (F := E) A).subtype) τ (m • ks.val)

def DRAllAbove {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {l : ℕ}
    [Fact l.Prime] {N : ℕ} (V : G E Ω →* GL (Fin N) (Qbar l)) : Prop :=
  ∀ (w : HeightOneSpectrum (𝓞 E)), ((l : ℕ) : 𝓞 E) ∈ w.asIdeal →
    ∀ (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) → ∀ (A : ValuationSubring Ω), IsPlaceOver A w →
    ∀ (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω (Dec (F := E) A) O),
      GlobalTheory.Pst.Induces Bw → IsdRAt P Bw (V.comp (Dec (F := E) A).subtype)

def DivGal : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (l : ℕ) [Fact l.Prime] (n m : ℕ), 0 < m →
    ∀ V : G E Ω →* GL (Fin (n * m)) (Qbar l), Continuous V → IsSSRep V → DRAllAbove V →
    ∀ (S : Set (HeightOneSpectrum (𝓞 E))), NumberField.Set.HasDirichletDensity S 1 →
    ∀ (P : HeightOneSpectrum (𝓞 E) → (Qbar l)[X]), (∀ w ∈ S, (P w).Monic) →
      (∀ w ∈ S, FrobCP V w (P w ^ m)) →
      HTDistinctMult V n m →
    ∃ r : G E Ω →* GL (Fin n) (Qbar l), Continuous r ∧ IsSSRep r ∧ (∀ w ∈ S, FrobCP r w (P w)) ∧
      ∃ g : GL (Fin (n * m)) (Qbar l), ∀ s : G E Ω,
        (V s : Matrix (Fin (n * m)) (Fin (n * m)) (Qbar l)) =
          (g : Matrix _ _ (Qbar l)) *
            Matrix.reindex finProdFinEquiv finProdFinEquiv
              (Matrix.kronecker (r s : Matrix (Fin n) (Fin n) (Qbar l)) (1 : Matrix (Fin m) (Fin m) (Qbar l))) *
            ((g⁻¹ : GL (Fin (n * m)) (Qbar l)) : Matrix _ _ (Qbar l))

def SenLie : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (l : ℕ) [Fact l.Prime] (n m : ℕ), 0 < m →
    ∀ V : G E Ω →* GL (Fin (n * m)) (Qbar l), Continuous V → HTDistinctMult V n m →
    ∃ (K' : Type) (_ : Field K') (_ : IsAlgClosed K') (_ : Algebra (Qbar l) K')
      (X : Matrix (Fin (n * m)) (Fin (n * m)) K') (Q : K'[X]),
      InLieZar V X ∧ X.charpoly = Q ^ m ∧ Q.Separable

def ChebMeets : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (S : Set (HeightOneSpectrum (𝓞 E))), NumberField.Set.HasDirichletDensity S 1 →
    Dense {σ : G E Ω | ∃ w ∈ S, ∃ A : ValuationSubring Ω, IsPlaceOver A w ∧ IsFrob A (normV w) σ}

end PositivityTheory.AutomorphicGaloisHodgeTate.Div
