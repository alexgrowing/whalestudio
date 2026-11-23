import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousComplEquivSymm

open MeasureTheory ValuativeRel Matrix
open scoped Pointwise
open GlobalTheory.SplitFlip GlobalTheory.FlipMatch GlobalTheory.FlipMatch.FieldTransport GlobalTheory.PureMatch.Transport

noncomputable section
namespace GlobalTheory.PureMatch.Transport
namespace PrimFrameTr

section Fields
variable {k k' : Type} [Field k] [Field k']

theorem rank_map_le {A D : Type} [Fintype A] [Fintype D] [DecidableEq D] (f : k →+* k') (Z : Matrix A D k) :
    (Z.map f).rank ≤ Z.rank := by
  classical
  let M := LinearMap.range Z.mulVecLin
  let b := Module.finBasis k M
  have hc : ∀ y : D, (fun x => Z x y) ∈ M := fun y => ⟨Pi.single y 1, by ext x; simp⟩
  let P : Matrix A (Fin (Module.finrank k M)) k := Matrix.of fun x l => (b l : A → k) x
  let Q : Matrix (Fin (Module.finrank k M)) D k := Matrix.of fun l y => b.repr ⟨fun x => Z x y, hc y⟩ l
  have hPQ : Z = P * Q := by
    ext x y
    have h := congrArg (fun z : M => (z : A → k) x) (b.sum_repr ⟨fun x => Z x y, hc y⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h
    rw [Matrix.mul_apply]
    simp only [P, Q, Matrix.of_apply]
    rw [← h]
    exact Finset.sum_congr rfl fun l _ => mul_comm _ _
  have h : Z.map f = P.map f * Q.map f := by rw [hPQ, Matrix.map_mul]
  rw [h]
  refine (Matrix.rank_mul_le_left _ _).trans ((Matrix.rank_le_card_width _).trans ?_)
  simp [Matrix.rank, M]

theorem rank_map_equiv {A D : Type} [Fintype A] [Fintype D] [DecidableEq D] (j : k ≃+* k') (Z : Matrix A D k) :
    (Z.map j).rank = Z.rank := by
  refine le_antisymm (rank_map_le (j : k →+* k') Z) ?_
  have := rank_map_le (j.symm : k' →+* k) (Z.map j)
  have e : (Z.map j).map (j.symm : k' →+* k) = Z := by ext; simp
  rwa [e] at this

theorem rank_trM {A D A₂ D₂ : Type} [Fintype A] [Fintype D] [DecidableEq D] [Fintype D₂]
    (j : k ≃+* k') (rA : A₂ ≃ A) (cD : D₂ ≃ D) (Z : Matrix A D k) : (trM j rA cD Z).rank = Z.rank := by
  have : trM j rA cD Z = (Z.map j).submatrix rA cD := by ext; rfl
  rw [this, Matrix.rank_submatrix, rank_map_equiv]

theorem row_trM {A D A₂ D₂ : Type} (j : k ≃+* k') (rA : A₂ ≃ A) (cD : D₂ ≃ D) (Z : Matrix A D k) (r : A₂) :
    (trM j rA cD Z).row r = fun c => j (Z.row (rA r) (cD c)) := rfl

theorem read_sum {A D A₂ D₂ : Type} [Fintype A] [Fintype A₂] (j : k ≃+* k') (rA : A₂ ≃ A) (cD : D₂ ≃ D)
    (Z : Matrix A D k) (c : A → k) :
    (fun d => j ((∑ a, c a • Z.row a) (cD d))) = ∑ r, j (c (rA r)) • (trM j rA cD Z).row r := by
  funext d
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_sum, map_mul, row_trM]
  exact (Fintype.sum_equiv rA _ _ fun r => rfl).symm

theorem mem_spanK_of {A D A₂ D₂ : Type} [Fintype A] [Fintype A₂] (j : k ≃+* k') (rA : A₂ ≃ A) (cD : D₂ ≃ D)
    (Z : Matrix A D k) {x : D → k} (hx : x ∈ Submodule.span k (Set.range Z.row)) :
    (fun d => j (x (cD d))) ∈ Submodule.span k' (Set.range (trM j rA cD Z).row) := by
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun k).1 hx
  rw [read_sum j rA cD Z c]
  exact (Submodule.mem_span_range_iff_exists_fun k').2 ⟨_, rfl⟩

end Fields

variable {k k' : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k'] {j : k ≃+* k'}

theorem isLocIso_symm (hj : IsLocIso j) : IsLocIso j.symm :=
  ⟨hj.2.1, by simpa using hj.1, fun x => by rw [← hj.2.2 (j.symm x)]; simp⟩

theorem mem_spanO_of (hj : IsLocIso j) {A D A₂ D₂ : Type} [Fintype A] [Fintype A₂] (rA : A₂ ≃ A) (cD : D₂ ≃ D)
    (Z : Matrix A D k) {x : D → k} (hx : x ∈ Submodule.span 𝒪[k] (Set.range Z.row)) :
    (fun d => j (x (cD d))) ∈ Submodule.span 𝒪[k'] (Set.range (trM j rA cD Z).row) := by
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun 𝒪[k]).1 hx
  have h := read_sum j rA cD Z (fun a => (c a : k))
  have e : (∑ a, c a • Z.row a) = ∑ a, (c a : k) • Z.row a := Finset.sum_congr rfl fun a _ => rfl
  rw [e, h]
  exact (Submodule.mem_span_range_iff_exists_fun 𝒪[k']).2
    ⟨fun r => ⟨j (c (rA r)), (hj.2.2 _).2 (c (rA r)).2⟩, rfl⟩

theorem read_symm {D D₂ : Type} (cD : D₂ ≃ D) (x : D → k) :
    (fun d => j.symm ((fun c => j (x (cD c))) (cD.symm d))) = x := by
  funext d; simp

theorem trM_symm {A D A₂ D₂ : Type} (rA : A₂ ≃ A) (cD : D₂ ≃ D) (Z : Matrix A D k) :
    trM j.symm rA.symm cD.symm (trM j rA cD Z) = Z := trM_symm_trM j rA cD Z

def readEquiv (j : k ≃+* k') {D D₂ : Type} (cD : D₂ ≃ D) : (D → k) ≃ (D₂ → k') where
  toFun x d := j (x (cD d))
  invFun y d := j.symm (y (cD.symm d))
  left_inv x := by funext d; simp
  right_inv y := by funext d; simp

theorem memK_iff {A D A₂ D₂ : Type} [Fintype A] [Fintype A₂] (rA : A₂ ≃ A) (cD : D₂ ≃ D)
    (Z : Matrix A D k) (x : D → k) :
    (fun d => j (x (cD d))) ∈ Submodule.span k' (Set.range (trM j rA cD Z).row) ↔
      x ∈ Submodule.span k (Set.range Z.row) := by
  refine ⟨fun h => ?_, mem_spanK_of j rA cD Z⟩
  have := mem_spanK_of j.symm rA.symm cD.symm _ h
  rwa [read_symm, trM_symm] at this

theorem memO_iff (hj : IsLocIso j) {A D A₂ D₂ : Type} [Fintype A] [Fintype A₂] (rA : A₂ ≃ A) (cD : D₂ ≃ D)
    (Z : Matrix A D k) (x : D → k) :
    (fun d => j (x (cD d))) ∈ Submodule.span 𝒪[k'] (Set.range (trM j rA cD Z).row) ↔
      x ∈ Submodule.span 𝒪[k] (Set.range Z.row) := by
  refine ⟨fun h => ?_, mem_spanO_of hj rA cD Z⟩
  have := mem_spanO_of (isLocIso_symm hj) rA.symm cD.symm _ h
  rwa [read_symm, trM_symm] at this

end PrimFrameTr

open PrimFrameTr in

theorem isPrimFrame_trM_iff {k k' : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k']
    {j : k ≃+* k'} {A D A₂ D₂ : Type} [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] [Fintype A₂]
    [DecidableEq A₂] [Fintype D₂] [DecidableEq D₂] (hj : IsLocIso j) (rA : A₂ ≃ A) (cD : D₂ ≃ D)
    {Λ : Submodule 𝒪[k] (D → k)} {Λ₂ : Submodule 𝒪[k'] (D₂ → k')} (hL : LatCorr j cD Λ Λ₂) (Z : Matrix A D k) :
    IsPrimFrame Λ₂ (trM j rA cD Z) ↔ IsPrimFrame Λ Z := by
  have hc : Fintype.card A₂ = Fintype.card A := Fintype.card_congr rA
  have hm : trM j rA cD Z ∈ matLat A₂ Λ₂ ↔ Z ∈ matLat A Λ := by
    rw [mem_matLat, mem_matLat]
    refine (forall_congr' fun r => ?_).trans (rA.forall_congr_right (q := fun a => Z.row a ∈ Λ))
    exact hL (Z.row (rA r))
  have hs : (Submodule.span 𝒪[k'] (Set.range (trM j rA cD Z).row) =
        (Submodule.span k' (Set.range (trM j rA cD Z).row)).restrictScalars 𝒪[k'] ⊓ Λ₂) ↔
      (Submodule.span 𝒪[k] (Set.range Z.row) =
        (Submodule.span k (Set.range Z.row)).restrictScalars 𝒪[k] ⊓ Λ) := by
    rw [SetLike.ext_iff, SetLike.ext_iff]
    refine ((readEquiv j cD).forall_congr_right).symm.trans (forall_congr' fun x => ?_)
    simp only [Submodule.mem_inf, Submodule.restrictScalars_mem]
    change ((fun d => j (x (cD d))) ∈ _ ↔ (fun d => j (x (cD d))) ∈ _ ∧ (fun d => j (x (cD d))) ∈ Λ₂) ↔ _
    rw [memO_iff hj, memK_iff, hL]
  unfold IsPrimFrame
  rw [rank_trM, hc, hm, hs]
end GlobalTheory.PureMatch.Transport
