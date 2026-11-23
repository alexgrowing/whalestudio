import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
open ValuativeRel
open scoped Matrix

noncomputable section
namespace GlobalTheory.IntRowLattice

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def gens {n d : ℕ} (X : Matrix (Fin n) (Fin d) k) (c : k) : Fin n ⊕ Fin d → (Fin d → k)
  | Sum.inl l => X l
  | Sum.inr j => c • Pi.single j 1

def rowLat {n d : ℕ} (X : Matrix (Fin n) (Fin d) k) (c : k) : Submodule 𝒪[k] (Fin d → k) :=
  Submodule.span 𝒪[k] (Set.range (gens X c))

theorem rowLat_isLattice {n d : ℕ} (X : Matrix (Fin n) (Fin d) k) (c : k) (hc : c ≠ 0) :
    (rowLat X c).IsLattice k where
  fg := Submodule.fg_span (Set.finite_range _)
  span_eq_top := by
    rw [eq_top_iff]
    rw [← (Pi.basisFun k (Fin d)).span_eq, Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    have h1 : (c • Pi.single j 1 : Fin d → k) ∈ (rowLat X c : Set (Fin d → k)) :=
      Submodule.subset_span ⟨Sum.inr j, rfl⟩
    have h2 := Submodule.smul_mem (Submodule.span k (rowLat X c : Set (Fin d → k))) c⁻¹
      (Submodule.subset_span h1)
    rw [smul_smul, inv_mul_cancel₀ hc, one_smul] at h2
    simpa using h2

theorem sum_gens {n d : ℕ} (X : Matrix (Fin n) (Fin d) k) (c : k) (f : Fin n ⊕ Fin d → 𝒪[k]) (j : Fin d) :
    (∑ s, f s • gens X c s) j = ∑ l, (f (Sum.inl l) : k) * X l j + c * (f (Sum.inr j) : k) := by
  simp [Fintype.sum_sum_type, Finset.sum_apply, gens, Subring.smul_def, Pi.single_apply, mul_comm]

theorem exists_iff_rows {n d : ℕ} (X : Matrix (Fin n) (Fin d) k) (c : k) (Y : Matrix (Fin n) (Fin d) k) :
    (∃ (A : Matrix (Fin n) (Fin n) k) (B : Matrix (Fin n) (Fin d) k), (∀ i j, A i j ∈ 𝒪[k]) ∧
      (∀ i j, B i j ∈ 𝒪[k]) ∧ Y = A * X + c • B) ↔ ∀ i, Y i ∈ rowLat X c := by
  constructor
  · rintro ⟨A, B, hA, hB, rfl⟩ i
    rw [rowLat, Submodule.mem_span_range_iff_exists_fun]
    refine ⟨Sum.elim (fun l => ⟨A i l, hA i l⟩) (fun j => ⟨B i j, hB i j⟩), ?_⟩
    ext j
    rw [sum_gens]
    simp [Matrix.mul_apply]
  · intro h
    choose f hf using fun i => (Submodule.mem_span_range_iff_exists_fun 𝒪[k]).1 (h i)
    refine ⟨Matrix.of fun i l => f i (Sum.inl l), Matrix.of fun i j => f i (Sum.inr j), fun i l => (f i _).2,
      fun i j => (f i _).2, ?_⟩
    ext i j
    rw [← hf i, sum_gens]
    simp [Matrix.mul_apply]

theorem mem_iff_repr {d : ℕ} (L : Submodule 𝒪[k] (Fin d → k)) [L.IsLattice k]
    (b : Module.Basis (Fin d) 𝒪[k] L) (y : Fin d → k) :
    y ∈ L ↔ ∀ j, (b.extendOfIsLattice k).repr y j ∈ 𝒪[k] := by
  set bK := b.extendOfIsLattice k
  have hbK : ∀ i, bK i = (b i : Fin d → k) := Module.Basis.extendOfIsLattice_apply k b
  constructor
  · intro hy
    have e2 : y = ∑ l, ((b.repr ⟨y, hy⟩ l : 𝒪[k]) : k) • bK l := by
      have h := congrArg Subtype.val (b.sum_repr ⟨y, hy⟩)
      rw [Submodule.coe_sum] at h
      refine Eq.trans h.symm (Finset.sum_congr rfl fun l _ => ?_)
      rw [Submodule.coe_smul, hbK]
      rfl
    intro j
    rw [e2, bK.repr_sum_self]
    exact (b.repr ⟨y, hy⟩ j).2
  · intro h
    rw [← bK.sum_repr y]
    refine Submodule.sum_mem _ fun l _ => ?_
    have : bK.repr y l • bK l = (⟨_, h l⟩ : 𝒪[k]) • (b l : Fin d → k) := by
      rw [hbK]; rfl
    rw [this]
    exact Submodule.smul_mem _ _ (b l).2

theorem mul_toMatrix_apply {n d : ℕ} (bK : Module.Basis (Fin d) k (Fin d → k)) (Y : Matrix (Fin n) (Fin d) k) (i j) :
    (Y * (bK.toMatrix (Pi.basisFun k (Fin d)))ᵀ) i j = bK.repr (Y i) j := by
  conv_rhs => rw [← (Pi.basisFun k (Fin d)).sum_repr (Y i)]
  simp [Matrix.mul_apply, Module.Basis.toMatrix_apply, Finsupp.smul_apply, mul_comm]

end GlobalTheory.IntRowLattice

namespace GlobalTheory.IntRowLattice

theorem exists_gl_integral_iff : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n d : ℕ) (X : Matrix (Fin n) (Fin d) k) (c : k), c ≠ 0 →
    ∃ h : GL (Fin d) k, ∀ Y : Matrix (Fin n) (Fin d) k,
      (∃ (A : Matrix (Fin n) (Fin n) k) (B : Matrix (Fin n) (Fin d) k), (∀ i j, A i j ∈ 𝒪[k]) ∧ (∀ i j, B i j ∈ 𝒪[k]) ∧ Y = A * X + c • B) ↔
        ∀ i j, (Y * (h : Matrix (Fin d) (Fin d) k)) i j ∈ 𝒪[k] := by
  intro k _ _ _ _ n d X c hc
  haveI := rowLat_isLattice X c hc
  haveI : Module.Free 𝒪[k] (rowLat X c) := Submodule.IsLattice.free k _
  have hr : Module.finrank 𝒪[k] (rowLat X c) = d := by
    rw [Submodule.IsLattice.finrank_of_pi k (rowLat X c), Fintype.card_fin]
  let b := Module.finBasisOfFinrankEq 𝒪[k] (rowLat X c) hr
  let bK := b.extendOfIsLattice k
  let e := Pi.basisFun k (Fin d)
  let h : GL (Fin d) k := ⟨(bK.toMatrix e)ᵀ, (e.toMatrix bK)ᵀ,
    by rw [← Matrix.transpose_mul, e.toMatrix_mul_toMatrix_flip, Matrix.transpose_one],
    by rw [← Matrix.transpose_mul, bK.toMatrix_mul_toMatrix_flip, Matrix.transpose_one]⟩
  refine ⟨h, fun Y => ?_⟩
  rw [exists_iff_rows]
  have key : ∀ i j, (Y * (h : Matrix (Fin d) (Fin d) k)) i j = bK.repr (Y i) j :=
    fun i j => mul_toMatrix_apply bK Y i j
  simp only [key]
  exact forall_congr' fun i => mem_iff_repr (rowLat X c) b (Y i)

end GlobalTheory.IntRowLattice
