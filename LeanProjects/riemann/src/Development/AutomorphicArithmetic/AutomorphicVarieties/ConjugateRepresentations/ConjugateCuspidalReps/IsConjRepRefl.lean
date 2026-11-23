import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.HasCohomology
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.DerivativeRightTranslateL2

noncomputable section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af

namespace UpperTheory.V.Cj.R

def IsRegInt (a : ℕ) (m : Multiset ℂ) : Prop :=
  Multiset.card m = a ∧ m.Nodup ∧ ∀ z ∈ m, ∃ n : ℤ, z = (n : ℂ) + ((a : ℂ) - 1) / 2

theorem isRegInt_zero : IsRegInt 0 0 := ⟨rfl, Multiset.nodup_zero, fun _ h => absurd h (Multiset.notMem_zero _)⟩

def IsConjRep {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ} (σ : ℂ ≃+* ℂ) (Ξ Ξ' : AlgRep E a) : Prop :=
  ∃ h : Ξ.d = Ξ'.d, ∀ γ i j, ratC Ξ' γ (Fin.cast h i) (Fin.cast h j) = σ (ratC Ξ γ i j)

theorem isConjRep_refl {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ} (Ξ : AlgRep E a) :
    IsConjRep (RingEquiv.refl ℂ) Ξ Ξ := ⟨rfl, fun _ _ _ => rfl⟩

def ExAlgRep : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (m : (E →+* ℂ) → Multiset ℂ),
    (∀ τ, IsRegInt a (m τ)) → ∃ Ξ : AlgRep E a, ∀ τ, AlgInfChar Ξ τ ((m τ).map Neg.neg)

def ExAlgRepCusp : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (π : CuspSub E a), (CG.mk π).IsRegAlg →
    ∃ Ξ : AlgRep E a, ∀ τ, ∃ m, π.HasInfChar τ m ∧ AlgInfChar Ξ τ (m.map Neg.neg)

def ConjAlgMat : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (Ξ : AlgRep E a) (σ : ℂ ≃+* ℂ),
    ∃ (M : GL (Fin a) (Cinf E) →* Matrix (Fin Ξ.d) (Fin Ξ.d) ℂ) (hr : ∀ i j, (fun y => M y i j) ∈ regFun E a)
      (hi : ∀ W : Submodule ℂ (Fin Ξ.d → ℂ), (∀ y, ∀ v ∈ W, M y *ᵥ v ∈ W) → W = ⊥ ∨ W = ⊤),
      (∀ γ, ratC ⟨Ξ.d, M, hr, Ξ.pos, hi⟩ γ = (ratC Ξ γ).map σ) ∧
        ∀ τ m, AlgInfChar Ξ τ m → AlgInfChar ⟨Ξ.d, M, hr, Ξ.pos, hi⟩ (σ.toRingHom.comp τ) m

def ConjAlgRep : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (Ξ : AlgRep E a) (σ : ℂ ≃+* ℂ),
    ∃ Ξ' : AlgRep E a, IsConjRep σ Ξ Ξ' ∧ ∀ τ m, AlgInfChar Ξ τ m → AlgInfChar Ξ' (σ.toRingHom.comp τ) m

theorem conjAlgRep_of (h : ConjAlgMat) : ConjAlgRep := by
  intro E _ _ _ a Ξ σ
  obtain ⟨M, hr, hi, h1, h2⟩ := h E a Ξ σ
  exact ⟨⟨Ξ.d, M, hr, Ξ.pos, hi⟩, ⟨rfl, fun γ i j => congrFun (congrFun (h1 γ) i) j⟩, h2⟩

end UpperTheory.V.Cj.R
