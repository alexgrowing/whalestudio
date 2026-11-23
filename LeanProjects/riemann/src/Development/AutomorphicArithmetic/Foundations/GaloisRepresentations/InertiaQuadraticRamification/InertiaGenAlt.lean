import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.InertiaQuadraticRamification.NumberField

noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.HeckeGal GlobalTheory.CuspRep UpperTheory.V.Published

namespace UpperTheory.Gal.UnramifiedFromSplittingCriterion

def GroupStep : Prop :=
  ∀ (Γ : Type) [Group Γ] (Gd P : Subgroup Γ → Prop) (D : Set Γ) (Pl : Type) (Dc I : Pl → Set Γ), (∀ u, I u ⊆ Dc u) →
    (∀ H H', Gd H → Gd H' → Gd (H ⊓ H')) → (∀ H H', H ≤ H' → Gd H → Gd H') →
    (∀ U, Gd U → ∀ n : ℕ, 0 < n → ∃ ψ : Γ →* ℂˣ, Gd ψ.ker ∧ ψ ^ n = 1 ∧ (∀ g ∈ D, ψ g = 1) ∧
      ∃ u, Dc u ⊆ U ∧ ∃ τ ∈ I u, orderOf (ψ τ) = n) →
    (∀ H H' u, Gd H → Gd H' → P H → H' ≤ H → (H'.relIndex H).Prime → Dc u ⊆ H → (∃ τ ∈ I u, τ ∉ H') → P H') →
    ∀ (H₀ : Subgroup Γ) (r : Γ →* ℂˣ), Gd H₀ → P H₀ → Gd r.ker → ∀ n : ℕ, 0 < n → r ^ n = 1 →
      ∃ r' : Γ →* ℂˣ, Gd r'.ker ∧ (∀ g ∈ D, r' g = r g) ∧ P (H₀ ⊓ r'.ker)

def CharsOf : Prop :=
  ∀ (Γ : Type) [Group Γ] (H : Subgroup Γ), H.FiniteIndex → commutator Γ ≤ H →
    ∃ L : List (Γ →* ℂˣ), (∀ r ∈ L, H ≤ r.ker ∧ r ^ H.index = 1) ∧ ∀ g, (∀ r ∈ L, r g = 1) → g ∈ H

def PowChar : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (n : ℕ), 0 < n → 2 * n ∣ p - 1 →
    ∃ lam : (ZMod p)ˣ →* ℂˣ, lam ^ n = 1 ∧ lam (-1) = 1 ∧ ∀ a, orderOf a = p - 1 → orderOf (lam a) = n

def InertiaGen : Prop :=
  ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (A : ValuationSubring Ω) (u : HeightOneSpectrum (𝓞 F)), IsPlaceOver A u →
    ∀ (p : ℕ) [Fact p.Prime], ((p : ℕ) : 𝓞 F) ∈ u.asIdeal → ((p : ℕ) : 𝓞 F) ∉ u.asIdeal ^ 2 →
    ∀ ζ : Ω, IsPrimitiveRoot ζ p →
    ∃ τ ∈ Ine (F := F) A, ∃ a : (ZMod p)ˣ, orderOf a = p - 1 ∧ τ ζ = ζ ^ (a : ZMod p).val

def DecPow : Prop :=
  ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (A : ValuationSubring Ω) (t : HeightOneSpectrum (𝓞 F)), IsPlaceOver A t →
    ∀ p : ℕ, p.Prime → ((p : ℕ) : 𝓞 F) ∉ t.asIdeal → ∀ ζ : Ω, IsPrimitiveRoot ζ p →
    (∀ g ∈ Dec (F := F) A, ∃ k : ℕ, g ζ = ζ ^ (normV t ^ k)) ∧ ∀ τ ∈ Ine (F := F) A, τ ζ = ζ

def SplitPlace : Prop :=
  ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (U : Subgroup (G F Ω)), IsOpen (U : Set (G F Ω)) →
    ∀ T : Set (HeightOneSpectrum (𝓞 F)), T.Finite →
    ∃ u ∉ T, (normV u).Prime ∧ ((normV u : ℕ) : 𝓞 F) ∈ u.asIdeal ∧ ((normV u : ℕ) : 𝓞 F) ∉ u.asIdeal ^ 2 ∧
      ∀ A : ValuationSubring Ω, IsPlaceOver A u → Dec (F := F) A ≤ U

def RootMod : Prop :=
  ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (A : ValuationSubring Ω) (u : HeightOneSpectrum (𝓞 F)), IsPlaceOver A u →
    ∀ p : ℕ, p.Prime → normV u = p → ∀ (y : Ω) (n : ℕ), 0 < n → (∀ g ∈ Dec (F := F) A, g y = y) →
    (∀ m : ℕ, y ^ n = (m : Ω) → ∃ b : ZMod p, b ^ n = (m : ZMod p)) ∧ (IsPrimitiveRoot y n → ¬ p ∣ n → n ∣ p - 1)

def FreshPrime : Prop :=
  ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (U : Subgroup (G F Ω)), IsOpen (U : Set (G F Ω)) →
    ∀ T : Set (HeightOneSpectrum (𝓞 F)), T.Finite → ∀ n : ℕ, 0 < n →
    ∃ u ∉ T, (normV u).Prime ∧ ((normV u : ℕ) : 𝓞 F) ∈ u.asIdeal ∧ ((normV u : ℕ) : 𝓞 F) ∉ u.asIdeal ^ 2 ∧
      (∀ A : ValuationSubring Ω, IsPlaceOver A u → Dec (F := F) A ≤ U) ∧ 2 * n ∣ normV u - 1 ∧
      ∀ t ∈ T, ((normV u : ℕ) : 𝓞 F) ∉ t.asIdeal ∧ ∃ b : ZMod (normV u), b ^ n = (normV t : ZMod (normV u))

def ExFld : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (H : Subgroup (G (maximalRealSubfield E) Ω)), Good H → ∃ X : Fld E Ω, Cuts X H

def RealPart : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (H : Subgroup (G (maximalRealSubfield E) Ω)), Good H → ∀ X : Fld E Ω, Cuts X H →
    fixGrp (maximalRealSubfield E) Ω (maximalRealSubfield X.K) = H

def InclOf : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (X Y : Fld E Ω), fixGrp E Ω Y.K ≤ fixGrp E Ω X.K →
    ∃ (_ : Algebra X.K Y.K) (_ : IsScalarTower E X.K Y.K) (_ : IsScalarTower X.K Y.K Ω), IsGalois X.K Y.K ∧
      Module.finrank X.K Y.K = (fixGrp E Ω Y.K).relIndex (fixGrp E Ω X.K)

def IndexComap : Prop :=
  ∀ (Γ Γ' : Type) [Group Γ] [Group Γ'] (f : Γ' →* Γ) (H H' : Subgroup Γ), commutator Γ ≤ H' → H' ≤ H → (H'.relIndex H).Prime →
    (∃ τ, f τ ∈ H ∧ f τ ∉ H') → (H'.comap f).relIndex (H.comap f) = H'.relIndex H

def LayerOf : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (S : Set (HeightOneSpectrum (𝓞 E))) (H H' : Subgroup (G (maximalRealSubfield E) Ω)), Good H' → H' ≤ H →
    (H'.relIndex H).Prime → ∀ X Y : Fld E Ω, Cuts X H → Cuts Y H' →
    ∀ u : HeightOneSpectrum (𝓞 (maximalRealSubfield E)), (∀ s ∈ S, s.under (𝓞 (maximalRealSubfield E)) ≠ u) →
    (∀ A : ValuationSubring Ω, IsPlaceOver A u → ∀ g ∈ Dec (F := maximalRealSubfield E) A, Fixes E g ∧ g ∈ H) →
    (∃ A : ValuationSubring Ω, IsPlaceOver A u ∧ ∃ τ ∈ Ine (F := maximalRealSubfield E) A, τ ∉ H') →
    Layer S X Y ∧ ∀ (_ : Algebra X.K Y.K) (_ : IsScalarTower X.K Y.K Ω), Module.finrank X.K Y.K = H'.relIndex H

def Disj : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (S : Set (HeightOneSpectrum (𝓞 E))) (N : Subgroup (G E Ω)),
    (∀ u ∉ S, ∀ A : ValuationSubring Ω, IsPlaceOver A u → Ine (F := E) A ≤ N) →
    ∀ X : Fld E Ω, Tower S X → GlobalTheory.AboveL.SolvDisj X.K N

def GoodLocal : Prop :=
  ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] [IsTotallyReal F] (ι : Type) [Finite ι]
    (v : ι → HeightOneSpectrum (𝓞 F)) (A : ι → ValuationSubring Ω), Function.Injective v →
    (∀ i, IsPlaceOver (A i) (v i)) → ∀ V : ∀ i, Subgroup (Dec (F := F) (A i)),
    (∀ i, IsOpen (V i : Set (Dec (F := F) (A i)))) → (∀ i, commutator (Dec (F := F) (A i)) ≤ V i) →
    ∀ T : Set (HeightOneSpectrum (𝓞 F)), T.Finite → (∀ i, v i ∉ T) →
    ∃ H : Subgroup (G F Ω), Good H ∧ (∀ i (g : Dec (F := F) (A i)), (g : G F Ω) ∈ H ↔ g ∈ V i) ∧
      ∀ t ∈ T, ∀ B : ValuationSubring Ω, IsPlaceOver B t → Dec (F := F) B ≤ H

def GoodUnr : Prop :=
  ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] [IsTotallyReal F] (W : Set (HeightOneSpectrum (𝓞 F))), W.Finite →
    ∀ d : HeightOneSpectrum (𝓞 F) → ℕ, (∀ t, 0 < d t) → ∀ T : Set (HeightOneSpectrum (𝓞 F)), T.Finite → Disjoint W T →
    ∃ H : Subgroup (G F Ω), Good H ∧
      (∀ v ∈ W, ∀ A : ValuationSubring Ω, IsPlaceOver A v → Ine (F := F) A ≤ H ∧
        ∀ φ : G F Ω, IsFrob A (normV v) φ → ∀ k : ℕ, φ ^ k ∈ H ↔ d v ∣ k) ∧
      ∀ t ∈ T, ∀ B : ValuationSubring Ω, IsPlaceOver B t → Dec (F := F) B ≤ H

def DegOf : Prop :=
  ∀ (K M Ω : Type) [Field K] [NumberField K] [Field M] [NumberField M] [Field Ω] [Algebra K M] [Algebra K Ω] [Algebra M Ω]
    [IsScalarTower K M Ω] [IsAlgClosure K Ω] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 K))
    (w : HeightOneSpectrum (𝓞 M)), IsPlaceOver A v → IsPlaceOver A w → (∀ τ ∈ Ine (F := K) A, Fixes M τ) →
    ∀ (φ : G K Ω) (d : ℕ), 0 < d → IsFrob A (normV v) φ → (∀ k : ℕ, Fixes M (φ ^ k) ↔ d ∣ k) → normV w = normV v ^ d

end UpperTheory.Gal.UnramifiedFromSplittingCriterion
