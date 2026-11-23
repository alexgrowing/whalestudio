import Development.AbelianVarietyTheory.Definitions.Foundations.IsSelfDualE
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LeafBounds.MeanMaxLeaf.LeafMMFree

open NumberField
open Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open scoped Matrix ComplexOrder

noncomputable section

namespace GlobalTheory.TestLat

def SlopeK : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] (v₀ : InfinitePlace K), Formalism.DivisionValues.IsConjAt v₀ →
  ∀ (ι : Type) [Fintype ι] (n : ℕ) (lam : ι → DomWeight n) (R : ℝ), 1 ≤ R → SpreadLe lam R →
  ∀ (G : ι → Matrix (Fin n) (Fin n) K), (∀ τ, IsDefGram (G τ)) →
  ∀ (C : Type) [Nonempty C] (M : C → ι → Submodule (𝓞 K) (Fin n → K)), (∀ c τ, IsSelfDualK (G τ) (M c τ)) →
  ∀ (N : ℕ) (e : Fin N ≃ C × VVIdx lam) (X : InfinitePlace K → Matrix (Fin N) (Fin N) ℂ),
    (IsMetric (sumGram lam e G) X →
      TestLatticeCondition N X (sumLat lam e fun c => nabK lam (M c)) (bound (Fintype.card ι) n R) ∧
      TestLatticeCondition N X (sumLat lam e fun c => delK lam (M c)) (bound (Fintype.card ι) n R)) ∧
    (IsMetric ((sumGram lam e G)⁻¹)ᵀ X →
      TestLatticeCondition N X (dualFr (sumLat lam e fun c => delK lam (M c))) (bound (Fintype.card ι) n R))

def SlopeE : Prop :=
  ∀ (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K]
    (v₀ : InfinitePlace K), Formalism.DivisionValues.IsConjAt v₀ →
  ∀ (cE : E →+* E), (∀ (φ : E →+* ℂ) (x : E), φ (cE x) = starRingEnd ℂ (φ x)) →
  ∀ (ι : Type) [Fintype ι] (emb : ι → E →+* K), (∀ τ x, star (emb τ x) = emb τ (cE x)) →
  ∀ (n : ℕ) (lam : ι → DomWeight n) (R : ℝ), 1 ≤ R → SpreadLe lam R →
  ∀ (J : Matrix (Fin n) (Fin n) E), (∀ φ : E →+* ℂ, (J.map φ).PosDef) →
  ∀ (C : Type) [Nonempty C] (L : C → Submodule (𝓞 E) (Fin n → E)), (∀ c, IsSelfDualE cE J (L c)) →
  ∀ (N : ℕ) (e : Fin N ≃ C × VVIdx lam) (X : InfinitePlace K → Matrix (Fin N) (Fin N) ℂ),
    (IsMetric ((sumGram lam e (gramK emb J))⁻¹)ᵀ X →
      TestLatticeCondition N X (dualFr (sumLat lam e fun c => delAt emb lam (L c))) (bound (Fintype.card ι) n R)) ∧
    (IsMetric (sumGram lam e (gramK emb J)) X →
      TestLatticeCondition N X (sumLat lam e fun c => nabAt emb lam (L c)) (bound (Fintype.card ι) n R)) ∧
    (IsMetric ((sumGram lam e (gramKd emb J))⁻¹)ᵀ X →
      TestLatticeCondition N X (dualFr (sumLat lam e fun c => delAtr emb lam (L c))) (bound (Fintype.card ι) n R)) ∧
    (IsMetric (sumGram lam e (gramKd emb J)) X →
      TestLatticeCondition N X (sumLat lam e fun c => nabAtr emb lam (L c)) (bound (Fintype.card ι) n R))

end GlobalTheory.TestLat
