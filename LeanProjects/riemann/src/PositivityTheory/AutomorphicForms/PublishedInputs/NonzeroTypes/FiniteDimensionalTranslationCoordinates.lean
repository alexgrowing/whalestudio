import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.KIface
import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.CIface
import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.ScalarOnInertiaProp
import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.TensorProductVectors

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.UnitaryBC UpperTheory.V.Af
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel Matrix UpperTheory.TNZ

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.NonzeroTypeTheory

def Need_CMain : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (G : Grp k n)
    (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin n) k) V), IsSmooth ρ → ρ.IsIrreducible →
    (∃ x : V, x ≠ 0 ∧ ∀ g ∈ G.JSet, ρ g x = G.lam g • x) → IsTwSphProd ρ G.d G.hd G.μ

def Need_CProps : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (G : Grp k n),
    G.JSet ⊆ KO k (Fin n) ∧ (1 : GL (Fin n) k) ∈ G.JSet ∧
    (∀ g ∈ G.JSet, ∀ g' ∈ G.JSet, g * g' ∈ G.JSet ∧ G.lam (g * g') = G.lam g * G.lam g') ∧
    (∀ g ∈ G.JSet, g⁻¹ ∈ G.JSet) ∧ (∀ g ∈ G.JSet, G.lam g ≠ 0) ∧
    IsOpen (KC k n G.lev) ∧ (1 : GL (Fin n) k) ∈ KC k n G.lev ∧ KC k n G.lev ⊆ G.JSet ∧ (∀ g ∈ KC k n G.lev, G.lam g = 1) ∧
    (∀ φ ∈ G.V0sp, ∀ k' : ↥(KO k (Fin n)), rightReg ℂ ↥(KO k (Fin n)) ℂ k' φ ∈ G.V0sp) ∧ FiniteDimensional ℂ G.V0sp ∧
    G.v0 ∈ G.V0sp ∧ G.v0 ≠ 0 ∧
    ∀ j : ↥(KO k (Fin n)), (j : GL (Fin n) k) ∈ G.JSet → rightReg ℂ ↥(KO k (Fin n)) ℂ j G.v0 = G.lam j • G.v0

def Need_Grp : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ)
    (μ : Fin n → kˣ →* ℂˣ), (∀ i, IsSmoothChar (μ i)) →
    ∃ (G : Grp k n) (σ : Fin n ≃ Fin n), ∀ i, res (G.chi i) = res (μ (σ i))

def ArtinTransferDecompositionCharacter : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω)
    (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (a : Weil h →* (w.adicCompletion E)ˣ), IsLocalArtin h a →
    ∀ (n : ℕ) (χ : Fin n → Dec (F := E) A →* ℂˣ), (∀ i, IsOpen ((χ i).ker : Set (Dec (F := E) A))) →
      ∃ μ : Fin n → (w.adicCompletion E)ˣ →* ℂˣ, (∀ i, IsSmoothChar (μ i)) ∧
        ∀ i (σ : Weil h), χ i (Subgroup.inclusion (Weil_le_Dec h) σ) = μ i (a σ)

def LocalArtinCharacterProduct : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω)
    (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (a : Weil h →* (w.adicCompletion E)ˣ), IsLocalArtin h a →
    ∀ (n : ℕ) (χ : Fin n → Dec (F := E) A →* ℂˣ) (ho : ∀ i, IsOpen ((χ i).ker : Set (Dec (F := E) A)))
      (μ : Fin n → (w.adicCompletion E)ˣ →* ℂˣ), (∀ i (σ : Weil h), χ i (Subgroup.inclusion (Weil_le_Dec h) σ) = μ i (a σ)) →
      ∀ (G : Grp (w.adicCompletion E) n) (σ : Fin n ≃ Fin n), (∀ i, res (G.chi i) = res (μ (σ i))) →
        ∀ s : ↥(Ine (F := E) A), (xOf h χ ho).charPol (ineIncl h s) =
          ∏ b, (X - C (((G.μ b (a (ineIncl h s))) : ℂˣ) : ℂ)) ^ G.d b

def FiniteDimensionalTranslationCoordinates : Prop :=
  ∀ (K : Type) [Group K] [TopologicalSpace K] (W : Submodule ℂ (K → ℂ)), FiniteDimensional ℂ W →
    (∀ φ ∈ W, ∀ k : K, rightReg ℂ K ℂ k φ ∈ W) → (∀ φ ∈ W, IsOpen {k : K | rightReg ℂ K ℂ k φ = φ}) →
    ∃ (m : ℕ) (V0 : Representation ℂ K (Fin m → ℂ)) (e : (Fin m → ℂ) →ₗ[ℂ] (K → ℂ)),
      Function.Injective e ∧ LinearMap.range e = W ∧ (∀ k v, e (V0 k v) = rightReg ℂ K ℂ k (e v)) ∧ IsSmooth V0

def TwistedSphericalRepresentative : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ)
    (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin n) k) V) (h1 : IsSmooth ρ) (h2 : ρ.IsIrreducible)
    (s : ℕ) (d : Fin s → ℕ) (hd : ∑ a, d a = n) (η : Fin s → kˣ →* ℂˣ),
    IsTwSphProd (IrrGL.of ρ h1 h2).rep d hd η ↔ IsTwSphProd ρ d hd η

def DistinctOnUnitsDistinctOnInertia : Prop :=
  ArtinInertiaProp →
  ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω)
    (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (a : Weil h →* (w.adicCompletion E)ˣ), IsLocalArtin h a →
    ∀ (n : ℕ) (G : Grp (w.adicCompletion E) n) (b c : Fin G.s), b ≠ c →
      ∃ t : ↥(Ine (F := E) A), G.μ b (a (ineIncl h t)) ≠ G.μ c (a (ineIncl h t))

def SmoothVectorsFixedByCongruence : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (G : Grp k n),
    IsOpen (KC k n G.lev) → (1 : GL (Fin n) k) ∈ KC k n G.lev →
    ∀ φ ∈ G.V0sp, IsOpen {k' : ↥(KO k (Fin n)) | rightReg ℂ ↥(KO k (Fin n)) ℂ k' φ = φ}

end UpperTheory.NonzeroTypeTheory
