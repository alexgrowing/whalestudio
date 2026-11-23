import Mathlib
import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.SlopeE
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.SpreadComposition
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SumPairingGramMatrixValuesAndDefinite
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.OrthogonalSumCoefficientLatticeIsLatticeAndDual
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DualLatticeIsLatticeAndHermitianDual
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NablaDeltaOperatorLatticePreserved
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LatticeExtensionAlongFieldEmbeddingDuals
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TransportedWeylLatticeHermitianDuality
import Formalism.LocalToGlobal.Columns.CoefModB

open NumberField
open Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open scoped Matrix ComplexOrder

noncomputable section

namespace GlobalTheory.TestLat.Compare

def conjHom (E : Type) [Field E] [NumberField E] [IsCMField E] : E →+* E :=
  (IsCMField.complexConj E : E →+* E)

section Space

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

end Space

section Sum

variable {E K : Type} [Field E] [NumberField E] [Field K] [NumberField K] {ι C : Type} [Fintype ι] {n N : ℕ}

end Sum

section DualSpace

variable {E K : Type} [Field E] [NumberField E] [Field K] [NumberField K] {ι : Type} {n : ℕ}

end DualSpace

section Nabla

variable {K : Type} [Field K] [NumberField K] {ι C : Type} [Fintype ι] {n N : ℕ}

open Classical in

def blk {F I : Type} [Zero F] (e : Fin N ≃ C × I) (M : Matrix I I F) : Matrix (Fin N) (Fin N) F :=
  Matrix.of fun a b => if (e a).1 = (e b).1 then M (e a).2 (e b).2 else 0

omit [NumberField K] in
theorem pairK_basis [StarRing K] (lam : ι → DomWeight n) (g : ι → GL (Fin n) K) (i j : VVIdx lam) :
    pairK lam (fun τ => (g τ : Matrix (Fin n) (Fin n) K)) (bVV K lam i) (bVV K lam j) =
      pairBK lam (bVV K lam i) (rhoK lam g (bVV K lam j)) := by
  rw [pairK_apply, pairP_eq_pairB, pairBK_apply, rhoK_coe]
  congr 2
  rw [bVV_coe]
  obtain ⟨Q, hQ⟩ := bVVfun_int K lam i
  rw [hQ, MvPolynomial.map_map]
  congr 2
  exact RingHom.ext_int _ _

def gramB (K : Type) [Field K] (lam : ι → DomWeight n) : Matrix (VVIdx lam) (VVIdx lam) K :=
  Matrix.of fun i j => pairBK lam (bVV K lam i) (bVV K lam j)

omit [NumberField K] in
theorem gramB_transpose (lam : ι → DomWeight n) : (gramB K lam)ᵀ = gramB K lam := by
  ext i j
  simp only [gramB, Matrix.transpose_apply, Matrix.of_apply, pairBK_apply]
  exact pairingBSymm_holds K ι n lam _ _

theorem hdualFr_triv {m : ℕ} (P : Matrix (Fin m) (Fin m) K) (M : Submodule (𝓞 K) (Fin m → K)) (x : Fin m → K) :
    x ∈ @hdualFr K _ m starRingOfComm P M ↔ P *ᵥ x ∈ dualFr M := by
  change (∀ y ∈ M, y ⬝ᵥ (P *ᵥ x) ∈ (1 : Submodule (𝓞 K) K)) ↔ ∀ y ∈ M, (P *ᵥ x) ⬝ᵥ y ∈ (1 : Submodule (𝓞 K) K)
  simp only [dotProduct_comm]

end Nabla

section Clauses

variable {E K : Type} [Field E] [NumberField E] [Field K] [NumberField K] [StarRing K] {ι C : Type} [Fintype ι] {n N : ℕ}
  (emb : ι → E →+* K) (lam : ι → DomWeight n) (R : ℝ) (J : Matrix (Fin n) (Fin n) E)
  (L : C → Submodule (𝓞 E) (Fin n → E)) (e : Fin N ≃ C × VVIdx lam) (X : InfinitePlace K → Matrix (Fin N) (Fin N) ℂ)

def WeylClause : Prop :=
  IsMetric ((sumGram lam e (gramK emb J))⁻¹)ᵀ X →
    TestLatticeCondition N X (dualFr (sumLat lam e fun c => delAt emb lam (L c))) (bound (Fintype.card ι) n R)

def WeylClauseDual : Prop :=
  IsMetric ((sumGram lam e (gramKd emb J))⁻¹)ᵀ X →
    TestLatticeCondition N X (dualFr (sumLat lam e fun c => delAtr emb lam (L c))) (bound (Fintype.card ι) n R)

def NablaClause : Prop :=
  IsMetric (sumGram lam e (gramK emb J)) X →
    TestLatticeCondition N X (sumLat lam e fun c => nabAt emb lam (L c)) (bound (Fintype.card ι) n R)

def NablaClauseDual : Prop :=
  IsMetric (sumGram lam e (gramKd emb J)) X →
    TestLatticeCondition N X (sumLat lam e fun c => nabAtr emb lam (L c)) (bound (Fintype.card ι) n R)

end Clauses

def Under (P : ∀ (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] [StarRing K] (_ : E →+* E)
    (ι : Type) [Fintype ι] (_ : ι → E →+* K) (n : ℕ) (lam : ι → DomWeight n) (_ : ℝ) (_ : Matrix (Fin n) (Fin n) E)
    (C : Type) (_ : C → Submodule (𝓞 E) (Fin n → E)) (N : ℕ) (_ : Fin N ≃ C × VVIdx lam)
    (_ : InfinitePlace K → Matrix (Fin N) (Fin N) ℂ), Prop) : Prop :=
  ∀ (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K]
    (v₀ : InfinitePlace K), Formalism.DivisionValues.IsConjAt v₀ →
  ∀ (cE : E →+* E), (∀ (φ : E →+* ℂ) (x : E), φ (cE x) = starRingEnd ℂ (φ x)) →
  ∀ (ι : Type) [Fintype ι] (emb : ι → E →+* K), (∀ τ x, star (emb τ x) = emb τ (cE x)) →
  ∀ (n : ℕ) (lam : ι → DomWeight n) (R : ℝ), 1 ≤ R → SpreadLe lam R →
  ∀ (J : Matrix (Fin n) (Fin n) E), (∀ φ : E →+* ℂ, (J.map φ).PosDef) →
  ∀ (C : Type) [Nonempty C] (L : C → Submodule (𝓞 E) (Fin n → E)), (∀ c, IsSelfDualE cE J (L c)) →
  ∀ (N : ℕ) (e : Fin N ≃ C × VVIdx lam) (X : InfinitePlace K → Matrix (Fin N) (Fin N) ℂ),
    P E K cE ι emb n lam R J C L N e X

theorem slopeE_eq : SlopeE = Under fun _ _ _ _ _ _ _ _ _ _ emb _ lam R J _ L _ e X =>
    WeylClause emb lam R J L e X ∧ NablaClause emb lam R J L e X ∧
      WeylClauseDual emb lam R J L e X ∧ NablaClauseDual emb lam R J L e X := rfl

def FirstCM : Prop := Under fun E _ _ _ _ _ _ cE _ _ emb n lam R J _ L _ e X =>
  cE ≠ RingHom.id E → 1 ≤ n → WeylClause emb lam R J L e X

def First : Prop := Under fun _ _ _ _ _ _ _ _ _ _ emb _ lam R J _ L _ e X => WeylClause emb lam R J L e X

def FirstDegenerate : Prop := Under fun E _ _ _ _ _ _ cE _ _ emb n lam R J _ L _ e X =>
  cE = RingHom.id E ∨ n = 0 → WeylClause emb lam R J L e X

def SlopeCM : Prop := Under fun E _ _ _ _ _ _ cE _ _ emb n lam R J _ L _ e X =>
  cE ≠ RingHom.id E → 1 ≤ n → WeylClause emb lam R J L e X ∧ NablaClause emb lam R J L e X ∧
      WeylClauseDual emb lam R J L e X ∧ NablaClauseDual emb lam R J L e X

end GlobalTheory.TestLat.Compare
