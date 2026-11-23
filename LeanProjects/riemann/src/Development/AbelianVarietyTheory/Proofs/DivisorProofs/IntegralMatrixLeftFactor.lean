import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndicatorIntMMemSB
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ScaledIntegerPeriodic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulRightMemSB
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.KSplit GlobalTheory.GJReg
open Classical

namespace GlobalTheory.GJReg

theorem exists_gl_rowSpan_int (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (s : k) :
    s ≠ 0 → ∀ X : Matrix (Fin n) (Fin n) k, ∃ (h : GL (Fin n) k) (A B C D : Matrix (Fin n) (Fin n) k),
      A ∈ intM k (Fin n) (Fin n) ∧ B ∈ intM k (Fin n) (Fin n) ∧ C ∈ intM k (Fin n) (Fin n) ∧ D ∈ intM k (Fin n) (Fin n) ∧
      h.val = A * X + s • B ∧ X = C * h.val ∧ s • (1 : Matrix (Fin n) (Fin n) k) = D * h.val := by
  intro hs X
  set S : Matrix (Fin n) (Fin n) k := s • (1 : Matrix (Fin n) (Fin n) k) with hS
  let v : Fin n ⊕ Fin n → (Fin n → k) := Sum.elim X S
  let L : Submodule 𝒪[k] (Fin n → k) := Submodule.span 𝒪[k] (Set.range v)
  haveI : Module.Finite 𝒪[k] L := Module.Finite.span_of_finite _ (Set.finite_range v)
  haveI : Module.IsTorsionFree 𝒪[k] L := ⟨fun r hr x y hxy => by
    have h0 : (r : k) ≠ 0 := by
      intro h; exact hr.ne_zero (Subtype.ext h)
    apply Subtype.ext
    have := congrArg Subtype.val hxy
    simp only [Submodule.coe_smul, Subring.smul_def] at this
    exact smul_right_injective _ h0 this⟩
  haveI : Module.Free 𝒪[k] L := Module.free_of_finite_type_torsion_free'
  have hSdet : S.det ≠ 0 := by
    simp [hS, Matrix.det_smul, hs]
  have hSli : LinearIndependent k (fun i => S i) := by
    exact Matrix.linearIndependent_rows_of_isUnit ((Matrix.isUnit_iff_isUnit_det S).2 (isUnit_iff_ne_zero.2 hSdet))
  have hSmem : ∀ i, S i ∈ L := fun i => Submodule.subset_span ⟨Sum.inr i, rfl⟩
  have hXmem : ∀ i, X i ∈ L := fun i => Submodule.subset_span ⟨Sum.inl i, rfl⟩
  have hr : Module.finrank 𝒪[k] L = n := by
    apply le_antisymm
    · have hb := (Module.finBasis 𝒪[k] L).linearIndependent.map' L.subtype (by simp)
      rw [LinearIndependent.iff_fractionRing 𝒪[k] k] at hb
      simpa using hb.fintype_card_le_finrank
    · have hli : LinearIndependent 𝒪[k] (fun i => (⟨S i, hSmem i⟩ : L)) := by
        apply LinearIndependent.of_comp L.subtype
        exact (LinearIndependent.iff_fractionRing 𝒪[k] k).2 hSli
      simpa using hli.fintype_card_le_finrank
  let b := Module.finBasisOfFinrankEq 𝒪[k] L hr
  have hexp : ∀ (y : Fin n → k) (hy : y ∈ L) (l : Fin n),
      y l = ∑ j, ((b.repr ⟨y, hy⟩ j : 𝒪[k]) : k) * (b j : Fin n → k) l := by
    intro y hy l
    have := congrArg (fun z : L => (z : Fin n → k) l) (b.sum_repr ⟨y, hy⟩)
    refine this.symm.trans ?_
    simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply, Subring.smul_def, smul_eq_mul]
  let H : Matrix (Fin n) (Fin n) k := Matrix.of fun i l => (b i : Fin n → k) l
  let C : Matrix (Fin n) (Fin n) k := Matrix.of fun i j => ((b.repr ⟨X i, hXmem i⟩ j : 𝒪[k]) : k)
  let D : Matrix (Fin n) (Fin n) k := Matrix.of fun i j => ((b.repr ⟨S i, hSmem i⟩ j : 𝒪[k]) : k)
  have hC : X = C * H := by
    ext i l
    rw [Matrix.mul_apply, hexp (X i) (hXmem i) l]
    rfl
  have hD : S = D * H := by
    ext i l
    rw [Matrix.mul_apply, hexp (S i) (hSmem i) l]
    rfl
  have hHdet : H.det ≠ 0 := by
    intro h0
    apply hSdet
    rw [hD, Matrix.det_mul, h0, mul_zero]
  have hmem : ∀ i, ∃ c : Fin n ⊕ Fin n → 𝒪[k], ∑ x, c x • v x = (b i : Fin n → k) := fun i =>
    (Submodule.mem_span_range_iff_exists_fun 𝒪[k]).1 (b i).2
  choose c hc using hmem
  let A : Matrix (Fin n) (Fin n) k := Matrix.of fun i j => ((c i (Sum.inl j) : 𝒪[k]) : k)
  let B : Matrix (Fin n) (Fin n) k := Matrix.of fun i j => ((c i (Sum.inr j) : 𝒪[k]) : k)
  have hAB : H = A * X + s • B := by
    ext i l
    have := congrFun (hc i) l
    have hv1 : ∀ j, v (Sum.inl j) = X j := fun _ => rfl
    have hv2 : ∀ j, v (Sum.inr j) = S j := fun _ => rfl
    rw [Fintype.sum_sum_type] at this
    simp only [hv1, hv2] at this
    simp only [Finset.sum_apply, Pi.add_apply, Pi.smul_apply, Subring.smul_def, smul_eq_mul, v, Sum.elim_inl,
      Sum.elim_inr, hS, Matrix.smul_apply, Matrix.one_apply, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, if_true] at this
    simp only [H, A, B, Matrix.add_apply, Matrix.mul_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul]
    rw [← this]
    ring
  refine ⟨Matrix.nonsingInvUnit H (isUnit_iff_ne_zero.2 hHdet), A, B, C, D,
    fun i j => (c i (Sum.inl j)).2, fun i j => (c i (Sum.inr j)).2,
    fun i j => (b.repr ⟨X i, hXmem i⟩ j).2, fun i j => (b.repr ⟨S i, hSmem i⟩ j).2, hAB, hC, hD⟩

end GlobalTheory.GJReg
