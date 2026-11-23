import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.TaylorCoefficientForms
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.TensorCoordinateForms
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSumTaylorCoordinateSpaceEntire

open Finset
open scoped ComplexConjugate Real

noncomputable section

namespace GlobalTheory.JetFrameCompare

open GlobalTheory.IndefiniteRowSideFullHecke Formalism.DimensionVariation

section Calculus

variable {E κ W : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  [NormedAddCommGroup W] [NormedSpace ℂ W]

theorem wordDeriv_eq_lineDerivList (v : κ → E) {F : E → ℂ} (hF : Differentiable ℂ F) (w : List κ) :
    TensorCoordinateForms.wordDeriv v w F = lineDerivList ℂ (w.map v) F := by
  induction w with
  | nil => rfl
  | cons x w ih =>
    funext z
    have h := (analyticAt_lineDerivList
      (SCV.analyticOnNhd_of_differentiable hF Set.univ z (Set.mem_univ z)) (w.map v)).differentiableAt
    rw [List.map_cons, lineDerivList_cons]
    change TensorCoordinateForms.dirDeriv (v x) (TensorCoordinateForms.wordDeriv v w F) z = _
    rw [ih]
    exact h.lineDeriv_eq_fderiv.symm

theorem wordDeriv_perm (v : κ → E) {F : E → ℂ} (hF : Differentiable ℂ F) {w w' : List κ}
    (h : w.Perm w') : TensorCoordinateForms.wordDeriv v w F = TensorCoordinateForms.wordDeriv v w' F := by
  funext z
  rw [wordDeriv_eq_lineDerivList v hF, wordDeriv_eq_lineDerivList v hF]
  exact lineDerivList_perm (SCV.analyticOnNhd_of_differentiable hF Set.univ z (Set.mem_univ z)) (h.map v)

def stdWord [Fintype κ] (e : κ → ℕ) : List κ :=
  (univ : Finset κ).toList.flatMap fun x => List.replicate (e x) x

omit [FiniteDimensional ℂ E] in

theorem monoDeriv_eq_wordDeriv [Fintype κ] (v : κ → E) (e : κ → ℕ) (F : E → ℂ) :
    TaylorCoefficientForms.monoDeriv v e F = TensorCoordinateForms.wordDeriv v (stdWord e) F := by
  unfold TaylorCoefficientForms.monoDeriv TensorCoordinateForms.wordDeriv stdWord
  induction (univ : Finset κ).toList with
  | nil => rfl
  | cons x l ih =>
    rw [List.foldr_cons, List.flatMap_cons, List.foldr_append, ← ih]
    generalize List.foldr (fun x G => (TaylorCoefficientForms.dirDeriv (v x))^[e x] G) F l = G
    induction e x with
    | zero => rfl
    | succ n ihn => rw [Function.iterate_succ_apply', List.replicate_succ, List.foldr_cons, ← ihn]; rfl

theorem isSpelling_stdWord [Fintype κ] [DecidableEq κ] : TensorCoordinateForms.IsSpelling (stdWord (κ := κ)) := by
  intro e x
  rw [stdWord, List.count_flatMap, Finset.sum_map_toList]
  simp [List.count_replicate]

theorem wordDeriv_eq_monoDeriv [Fintype κ] [DecidableEq κ] {w : (κ → ℕ) → List κ}
    (hw : TensorCoordinateForms.IsSpelling w) (v : κ → E) {F : E → ℂ} (hF : Differentiable ℂ F) (e : κ → ℕ) :
    TensorCoordinateForms.wordDeriv v (w e) F = TaylorCoefficientForms.monoDeriv v e F := by
  rw [monoDeriv_eq_wordDeriv]
  exact wordDeriv_perm v hF (List.perm_iff_count.2 fun x => (hw e x).trans (isSpelling_stdWord e x).symm)

theorem coordVec_eq [DecidableEq κ] : (TensorCoordinateForms.coordVec : κ → κ → ℂ) = TaylorCoefficientForms.coordVec := by
  funext p
  unfold TensorCoordinateForms.coordVec TaylorCoefficientForms.coordVec
  congr
  exact Subsingleton.elim _ _

theorem hasSum_taylorCoeff [Fintype κ] {F : (κ → ℂ) → ℂ} (hF : Differentiable ℂ F) (u : κ → ℂ) :
    HasSum (fun e => TaylorCoefficientForms.taylorCoeff F e * mono u e) (F u) := by
  classical
  have han := SCV.analyticOnNhd_of_differentiable hF Set.univ 0 (Set.mem_univ _)
  have hw : TensorCoordinateForms.IsSpelling fun e : κ → ℕ =>
      (Finsupp.toMultiset (Finsupp.equivFunOnFinite.symm e)).toList := fun e x => by
    rw [← Multiset.coe_count, Multiset.coe_toList, Finsupp.count_toMultiset]
    rfl
  have key : ∀ α : κ →₀ ℕ, TaylorCoefficientForms.monoDeriv TaylorCoefficientForms.coordVec α F =
      lineDerivList ℂ ((Finsupp.toMultiset α).toList.map fun k => Pi.single k (1 : ℂ)) F := fun α => by
    rw [← wordDeriv_eq_monoDeriv hw _ hF, wordDeriv_eq_lineDerivList _ hF, ← coordVec_eq]
    simp only [Finsupp.equivFunOnFinite_symm_coe]
    rfl
  have hne : ∀ α : κ →₀ ℕ, ((∏ i, (α i).factorial : ℕ) : ℂ) ≠ 0 := cast_prod_factorial_ne_zero
  have hc : ∀ α : κ →₀ ℕ,
      (∏ j, ((α j).factorial : ℂ)) * TaylorCoefficientForms.taylorCoeff F α = pderivIter α F 0 := fun α => by
    rw [TaylorCoefficientForms.taylorCoeff, key, mfact,
      ← Nat.cast_prod, mul_div_cancel₀ _ (hne α)]
    rfl
  have hc' : ∀ α : κ →₀ ℕ,
      TaylorCoefficientForms.taylorCoeff F α = MvPowerSeries.coeff α (GlobalTheory.taylor F) := fun α => by
    rw [GlobalTheory.taylor, coeff_taylorDir_eq_lineDerivList _ han (Multiset.coe_toList _), TaylorCoefficientForms.taylorCoeff, key,
      mfact, div_eq_inv_mul]
  have h1 := EntireTaylor.summable_of_entire hF (fun α => TaylorCoefficientForms.taylorCoeff F α) hc u
  have h2 := ProdThetaConj.tsum_of_entire hF (fun α => TaylorCoefficientForms.taylorCoeff F α) hc hc' u
  rw [← h2, ← (Finsupp.equivFunOnFinite (α := κ) (M := ℕ)).hasSum_iff]
  exact h1.hasSum

end Calculus

section Objects

variable {Pl : Type} [Fintype Pl] [DecidableEq Pl] {X₀ X₁ : Pl → Type}
  [∀ τ, NormedAddCommGroup (X₀ τ)] [∀ τ, InnerProductSpace ℂ (X₀ τ)] [∀ τ, FiniteDimensional ℂ (X₀ τ)]
  [∀ τ, NormedAddCommGroup (X₁ τ)] [∀ τ, InnerProductSpace ℂ (X₁ τ)] [∀ τ, FiniteDimensional ℂ (X₁ τ)]
  {n₀ n₁ : ℕ} (ξ D : Pl → ℂ) (b₀ : ∀ τ, OrthonormalBasis (Fin n₀) ℂ (X₀ τ))
  (b₁ : ∀ τ, OrthonormalBasis (Fin n₁) ℂ (X₁ τ))

end Objects

section Clauses

variable {Pl : Type} [Fintype Pl] {X₀ X₁ : Pl → Type}
  [∀ τ, NormedAddCommGroup (X₀ τ)] [∀ τ, InnerProductSpace ℂ (X₀ τ)] [∀ τ, FiniteDimensional ℂ (X₀ τ)]
  [∀ τ, NormedAddCommGroup (X₁ τ)] [∀ τ, InnerProductSpace ℂ (X₁ τ)] [∀ τ, FiniteDimensional ℂ (X₁ τ)]
  {n₀ n₁ : ℕ}

def ClausesFixedOrder (ξ D lam : Pl → ℂ) (b₀ : ∀ τ, OrthonormalBasis (Fin n₀) ℂ (X₀ τ))
    (b₁ : ∀ τ, OrthonormalBasis (Fin n₁) ℂ (X₁ τ)) : Prop :=
  (∀ z, TaylorCoefficientForms.ofUnitCoord ξ b₀ b₁ (TaylorCoefficientForms.unitCoord ξ b₀ b₁ z) = z) ∧
  (∀ u, TaylorCoefficientForms.unitCoord ξ b₀ b₁ (TaylorCoefficientForms.ofUnitCoord ξ b₀ b₁ u) = u) ∧
  (∀ z, (nsq (TaylorCoefficientForms.unitCoord ξ b₀ b₁ z) : ℂ) = π * TaylorCoefficientForms.bigForm ξ z z) ∧
  (∀ (τ : Pl) (d d' : ℂ) (x x' : X₀ τ →L[ℂ] X₁ τ),
    TaylorCoefficientForms.bigForm ξ (TaylorCoefficientForms.letterTensor τ d x) (TaylorCoefficientForms.letterTensor τ d' x') =
      TaylorCoefficientForms.lineForm (ξ τ) d d' * TaylorCoefficientForms.homForm x x') ∧
  ∀ Θ : (∀ τ, X₀ τ →L[ℂ] X₁ τ) → ℂ, Differentiable ℂ Θ →
    (∀ (x : Pl × (Fin n₁ × Fin n₀)) (z : ∀ τ, X₀ τ →L[ℂ] X₁ τ),
      TaylorCoefficientForms.dirDeriv (TaylorCoefficientForms.letterUnit D b₀ b₁ x) Θ z =
        lam x.1 * TaylorCoefficientForms.dirDeriv (TaylorCoefficientForms.coordVec x) (Θ ∘ TaylorCoefficientForms.ofUnitCoord ξ b₀ b₁)
          (TaylorCoefficientForms.unitCoord ξ b₀ b₁ z)) ∧
    (∀ u, HasSum (fun e => TaylorCoefficientForms.taylorCoeff (Θ ∘ TaylorCoefficientForms.ofUnitCoord ξ b₀ b₁) e * mono u e)
      (Θ (TaylorCoefficientForms.ofUnitCoord ξ b₀ b₁ u))) ∧
    ∀ (W : Type) [NormedAddCommGroup W] [NormedSpace ℂ W] (n : Pl → ℕ)
      (Rc : (Pl × (Fin n₁ × Fin n₀) → ℕ) →₀ W),
      (∀ e ∈ Rc.support, ∀ τ, ∑ p, e (τ, p) = n τ) →
      TaylorCoefficientForms.polyJet (TaylorCoefficientForms.letterUnit D b₀ b₁) Rc Θ =
          (∏ τ, lam τ ^ n τ) • TaylorCoefficientForms.polyJet TaylorCoefficientForms.coordVec Rc (Θ ∘ TaylorCoefficientForms.ofUnitCoord ξ b₀ b₁) ∧
        TaylorCoefficientForms.polyJet (TaylorCoefficientForms.letterUnit D b₀ b₁) Rc Θ =
          liftBlock (TaylorCoefficientForms.taylorCoeff (Θ ∘ TaylorCoefficientForms.ofUnitCoord ξ b₀ b₁)) Rc lam ∧
        ∀ c : (Pl × (Fin n₁ × Fin n₀) → ℕ) → ℂ,
          (∀ u, HasSum (fun e => c e * mono u e) (Θ (TaylorCoefficientForms.ofUnitCoord ξ b₀ b₁ u))) →
          TaylorCoefficientForms.polyJet (TaylorCoefficientForms.letterUnit D b₀ b₁) Rc Θ = liftBlock c Rc lam

def ClausesAllOrders [DecidableEq Pl] (a : Pl → ℝ) (D lam : Pl → ℂ)
    (b : ∀ τ, OrthonormalBasis (Fin n₀) ℂ (X₀ τ)) (b' : ∀ τ, OrthonormalBasis (Fin n₁) ℂ (X₁ τ)) : Prop :=
  (∀ u, TensorCoordinateForms.unitCoord a b b' (TensorCoordinateForms.ofUnitCoord a b b' u) = u) ∧
  (∀ z, TensorCoordinateForms.ofUnitCoord a b b' (TensorCoordinateForms.unitCoord a b b' z) = z) ∧
  (∀ z, ((nsq (TensorCoordinateForms.unitCoord a b b' z) : ℝ) : ℂ) = (π : ℂ) * TensorCoordinateForms.totalForm a z z) ∧
  (∀ (τ : Pl) (d d' : ℂ) (x x' : X₀ τ →L[ℂ] X₁ τ),
    TensorCoordinateForms.totalForm a (TensorCoordinateForms.tensorVec τ d x) (TensorCoordinateForms.tensorVec τ d' x') =
      TensorCoordinateForms.lineForm (a τ) d d' * TensorCoordinateForms.traceForm x x') ∧
  ∀ Th : (∀ τ, X₀ τ →L[ℂ] X₁ τ) → ℂ, Differentiable ℂ Th →
    (∀ (p : Pl × (Fin n₁ × Fin n₀)) (z : ∀ τ, X₀ τ →L[ℂ] X₁ τ),
      TensorCoordinateForms.dirDeriv (TensorCoordinateForms.frameVec D b b' p) Th z =
        lam p.1 * TensorCoordinateForms.dirDeriv (TensorCoordinateForms.coordVec p) (Th ∘ TensorCoordinateForms.ofUnitCoord a b b')
          (TensorCoordinateForms.unitCoord a b b' z)) ∧
    ∀ (W : Type) [NormedAddCommGroup W] [NormedSpace ℂ W]
      (Rc : (Pl × (Fin n₁ × Fin n₀) → ℕ) →₀ W) (n : Pl → ℕ)
      (w : (Pl × (Fin n₁ × Fin n₀) → ℕ) → List (Pl × (Fin n₁ × Fin n₀))),
      TensorCoordinateForms.IsSpelling w → (∀ e ∈ Rc.support, ∀ τ, ∑ q, e (τ, q) = n τ) →
      TensorCoordinateForms.substJet w (TensorCoordinateForms.frameVec D b b') Rc Th =
          (∏ τ, lam τ ^ n τ) • TensorCoordinateForms.substJet w TensorCoordinateForms.coordVec Rc (Th ∘ TensorCoordinateForms.ofUnitCoord a b b') ∧
      ∀ c : (Pl × (Fin n₁ × Fin n₀) → ℕ) → ℂ,
        (∀ u, HasSum (fun e => c e * mono u e) (Th (TensorCoordinateForms.ofUnitCoord a b b' u))) →
        TensorCoordinateForms.substJet w (TensorCoordinateForms.frameVec D b b') Rc Th = liftBlock c Rc lam

end Clauses

def ConclusionFixedOrder (Pl : Type) [Fintype Pl] (ξ D : Pl → ℂ) : Prop :=
  (∀ τ, 0 < TaylorCoefficientForms.period (ξ τ) (D τ)) ∧
  ∃ lam : Pl → ℂ, (∀ τ, ‖lam τ‖ ^ 2 = (TaylorCoefficientForms.period (ξ τ) (D τ))⁻¹) ∧
    ∀ (X₀ X₁ : Pl → Type)
      [∀ τ, NormedAddCommGroup (X₀ τ)] [∀ τ, InnerProductSpace ℂ (X₀ τ)] [∀ τ, FiniteDimensional ℂ (X₀ τ)]
      [∀ τ, NormedAddCommGroup (X₁ τ)] [∀ τ, InnerProductSpace ℂ (X₁ τ)] [∀ τ, FiniteDimensional ℂ (X₁ τ)]
      (n₀ n₁ : ℕ) (b₀ : ∀ τ, OrthonormalBasis (Fin n₀) ℂ (X₀ τ))
      (b₁ : ∀ τ, OrthonormalBasis (Fin n₁) ℂ (X₁ τ)), ClausesFixedOrder ξ D lam b₀ b₁

def ConclusionAllOrders (Pl : Type) [Fintype Pl] [DecidableEq Pl] (a : Pl → ℝ) (D : Pl → ℂ) : Prop :=
  ∃ ζ : Pl → ℂ,
    (∀ τ, ‖ζ τ‖ = 1) ∧ (∀ τ, 0 < TensorCoordinateForms.omega (a τ) (D τ)) ∧
    (∀ τ, ‖TensorCoordinateForms.letter (TensorCoordinateForms.omega (a τ) (D τ)) (ζ τ)‖ ^ 2 = (TensorCoordinateForms.omega (a τ) (D τ))⁻¹) ∧
    ∀ (X₀ X₁ : Pl → Type)
      [∀ τ, NormedAddCommGroup (X₀ τ)] [∀ τ, InnerProductSpace ℂ (X₀ τ)] [∀ τ, FiniteDimensional ℂ (X₀ τ)]
      [∀ τ, NormedAddCommGroup (X₁ τ)] [∀ τ, InnerProductSpace ℂ (X₁ τ)] [∀ τ, FiniteDimensional ℂ (X₁ τ)]
      (n₀ n₁ : ℕ) (b₀ : ∀ τ, OrthonormalBasis (Fin n₀) ℂ (X₀ τ))
      (b₁ : ∀ τ, OrthonormalBasis (Fin n₁) ℂ (X₁ τ)),
      ClausesAllOrders a D (fun τ => TensorCoordinateForms.letter (TensorCoordinateForms.omega (a τ) (D τ)) (ζ τ)) b₀ b₁

end GlobalTheory.JetFrameCompare
