import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HalfLat
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.GlMapStandardLatticeEqIffMemGLintAdic
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsAdicCompleteAndCardQuotientAdicCompletionInteg

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.SplitHecke GlobalTheory.LFun.ConjPlace GlobalTheory.AdelicU GlobalTheory.LFun.SplitTie

noncomputable section

namespace GlobalTheory.SplitIdx.LocIndex

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) {m n : ℕ}

private theorem mulL_apply' {K : Type} [CommRing K] {a b : ℕ} (P : Matrix (Fin a) (Fin a) K)
    (y : Matrix (Fin a) (Fin b) K) : GlobalTheory.SplitIdx.mulL (n := b) P y = P * y := rfl

private theorem mem_intMat_iff' (y : Matrix (Fin m) (Fin n) (v.adicCompletion F)) :
    y ∈ GlobalTheory.SplitIdx.intMat F v m n ↔ ∀ i j, y i j ∈ v.adicCompletionIntegers F := Iff.rfl

theorem mulL_mul (A B : Matrix (Fin m) (Fin m) (v.adicCompletion F)) :
    GlobalTheory.SplitIdx.mulL (n := n) (A * B) = (GlobalTheory.SplitIdx.mulL (n := n) A).comp (GlobalTheory.SplitIdx.mulL B) :=
  AddMonoidHom.ext fun y => by
    rw [AddMonoidHom.comp_apply, mulL_apply', mulL_apply', mulL_apply', Matrix.mul_assoc]

theorem mulL_mem {P : Matrix (Fin m) (Fin m) (v.adicCompletion F)}
    (hP : ∀ i j, P i j ∈ v.adicCompletionIntegers F) {y : Matrix (Fin m) (Fin n) (v.adicCompletion F)}
    (hy : y ∈ GlobalTheory.SplitIdx.intMat F v m n) : GlobalTheory.SplitIdx.mulL P y ∈ GlobalTheory.SplitIdx.intMat F v m n := by
  refine (mem_intMat_iff' v _).2 fun i j => ?_
  rw [mulL_apply', Matrix.mul_apply]
  exact sum_mem fun k _ => mul_mem (hP i k) ((mem_intMat_iff' v _).1 hy k j)

private theorem entries_mem_integers_of_mem_KGL {k : GL (Fin m) (v.adicCompletion F)} (hk : k ∈ KGL v m) :
    (∀ i j, k.1 i j ∈ v.adicCompletionIntegers F) ∧ (∀ i j, (k⁻¹).1 i j ∈ v.adicCompletionIntegers F) :=
  (GlobalTheory.LatHecke.mem_GLint_iff_entry _ _).1 hk

theorem mulL_mem_iff {k : GL (Fin m) (v.adicCompletion F)} (hk : k ∈ KGL v m)
    (y : Matrix (Fin m) (Fin n) (v.adicCompletion F)) :
    GlobalTheory.SplitIdx.mulL k.1 y ∈ GlobalTheory.SplitIdx.intMat F v m n ↔ y ∈ GlobalTheory.SplitIdx.intMat F v m n := by
  refine ⟨fun h => ?_, fun h => mulL_mem v (entries_mem_integers_of_mem_KGL v hk).1 h⟩
  have e : y = GlobalTheory.SplitIdx.mulL (k⁻¹).1 (GlobalTheory.SplitIdx.mulL (n := n) k.1 y) := by
    rw [mulL_apply', mulL_apply', ← Matrix.mul_assoc, k.inv_mul, Matrix.one_mul]
  rw [e]
  exact mulL_mem v (entries_mem_integers_of_mem_KGL v hk).2 h

theorem map_mulL {k : GL (Fin m) (v.adicCompletion F)} (hk : k ∈ KGL v m) :
    (GlobalTheory.SplitIdx.intMat F v m n).map (GlobalTheory.SplitIdx.mulL k.1) = GlobalTheory.SplitIdx.intMat F v m n := by
  ext y
  rw [AddSubgroup.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact mulL_mem v (entries_mem_integers_of_mem_KGL v hk).1 hx
  · intro hy
    refine ⟨GlobalTheory.SplitIdx.mulL (k⁻¹).1 y, mulL_mem v (entries_mem_integers_of_mem_KGL v hk).2 hy, ?_⟩
    rw [mulL_apply', mulL_apply', ← Matrix.mul_assoc, k.mul_inv, Matrix.one_mul]

theorem comap_mulL {k : GL (Fin m) (v.adicCompletion F)} (hk : k ∈ KGL v m)
    (P : Matrix (Fin m) (Fin m) (v.adicCompletion F)) :
    (GlobalTheory.SplitIdx.intMat F v m n).comap (GlobalTheory.SplitIdx.mulL (k.1 * P)) =
      (GlobalTheory.SplitIdx.intMat F v m n).comap (GlobalTheory.SplitIdx.mulL P) := by
  ext y
  rw [AddSubgroup.mem_comap, AddSubgroup.mem_comap, mulL_mul, AddMonoidHom.comp_apply, mulL_mem_iff v hk]

theorem zpow_mul_mem_iff {ϖ : v.adicCompletion F} (hϖ : IsUnifV F v ϖ) (hϖO : ϖ ∈ v.adicCompletionIntegers F)
    (d : ℤ) (x : v.adicCompletionIntegers F) :
    ϖ ^ d * (x : v.adicCompletion F) ∈ v.adicCompletionIntegers F ↔
      x ∈ Ideal.span {(⟨ϖ, hϖO⟩ : v.adicCompletionIntegers F) ^ (max (-d) 0).toNat} := by
  have hv : Valued.v ϖ = WithZero.exp (-1 : ℤ) := hϖ
  have hne : ϖ ≠ 0 := fun h => by
    rw [h, map_zero] at hv
    exact WithZero.exp_ne_zero hv.symm
  have ht : Valued.v (((⟨ϖ, hϖO⟩ : v.adicCompletionIntegers F) ^ (max (-d) 0).toNat : v.adicCompletionIntegers F) : v.adicCompletion F) ≠ 0 := by
    rw [SubmonoidClass.coe_pow, map_pow]
    exact pow_ne_zero _ ((Valuation.ne_zero_iff _).2 hne)
  rw [GlobalTheory.CNorm.mem_span_singleton_adicCompletionIntegers v ht, SubmonoidClass.coe_pow, map_pow]
  change Valued.v (ϖ ^ d * (x : v.adicCompletion F)) ≤ 1 ↔ _
  rw [map_mul, map_zpow₀, hv]
  have hx1 : Valued.v (x : v.adicCompletion F) ≤ 1 := x.2
  by_cases hx : (x : v.adicCompletion F) = 0
  · rw [hx, map_zero]
    simp
  · have hx0 : Valued.v (x : v.adicCompletion F) ≠ 0 := (Valuation.ne_zero_iff _).2 hx
    rw [← WithZero.exp_log hx0] at hx1 ⊢
    rw [← WithZero.exp_zsmul, ← WithZero.exp_nsmul, ← WithZero.exp_add, ← WithZero.exp_zero,
      WithZero.exp_le_exp, WithZero.exp_le_exp] at *
    simp only [smul_eq_mul, nsmul_eq_mul] at *
    omega

theorem card_quot_pow {ϖ : v.adicCompletion F} (hϖ : IsUnifV F v ϖ) (hϖO : ϖ ∈ v.adicCompletionIntegers F)
    (e : ℕ) :
    Nat.card (v.adicCompletionIntegers F ⧸ Ideal.span {(⟨ϖ, hϖO⟩ : v.adicCompletionIntegers F) ^ e}) =
      qV F v ^ e := by
  have hv : Valued.v ϖ = WithZero.exp (-1 : ℤ) := hϖ
  refine (GlobalTheory.CNorm.isAdicComplete_and_card_quotient_adicCompletionIntegers F v).2 _ e ?_
  rw [SubmonoidClass.coe_pow, map_pow, hv, ← WithZero.exp_nsmul]
  congr 1
  simp

end GlobalTheory.SplitIdx.LocIndex

namespace GlobalTheory.SplitIdx.LocIndex

theorem toNat_sum {m : ℕ} (d : Fin m → ℤ) :
    (∑ i, max (-d i) 0).toNat = ∑ i, (max (-d i) 0).toNat := by
  have h : ∀ i, 0 ≤ max (-d i) 0 := fun i => le_max_right _ _
  apply @Nat.cast_injective ℤ
  rw [Int.toNat_of_nonneg (Finset.sum_nonneg fun i _ => h i), Nat.cast_sum]
  exact Finset.sum_congr rfl fun i _ => (Int.toNat_of_nonneg (h i)).symm

theorem relIndex_intMat : ∀ {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (m n : ℕ) (ϖ : v.adicCompletion F), IsUnifV F v ϖ → ∀ (d : Fin m → ℤ) (t : GL (Fin m) (v.adicCompletion F)), t.1 = Matrix.diagonal (fun i => ϖ ^ d i) → ∀ k₁ ∈ KGL v m, ∀ k₂ ∈ KGL v m, (GlobalTheory.SplitIdx.intMat F v m n).relIndex ((GlobalTheory.SplitIdx.intMat F v m n).map (GlobalTheory.SplitIdx.mulL (n := n) (k₁ * t * k₂).1)) = qV F v ^ (n * (∑ i, max (-d i) 0).toNat) := by
  intro F _ _ v m n ϖ hϖ d t ht k₁ hk₁ k₂ hk₂
  have hv : Valued.v ϖ = WithZero.exp (-1 : ℤ) := hϖ
  have hϖO : ϖ ∈ v.adicCompletionIntegers F := by
    change Valued.v ϖ ≤ 1
    rw [hv, ← WithZero.exp_zero, WithZero.exp_le_exp]
    norm_num
  rw [← AddSubgroup.relIndex_comap, Units.val_mul, Units.val_mul, Matrix.mul_assoc, comap_mulL v hk₁,
    mulL_mul, ← AddSubgroup.comap_comap, AddSubgroup.relIndex_comap, map_mulL v hk₂, ht]
  let ψ : GlobalTheory.SplitIdx.intMat F v m n →+
      ((i : Fin m) → Fin n → v.adicCompletionIntegers F ⧸ Ideal.span {(⟨ϖ, hϖO⟩ : v.adicCompletionIntegers F) ^ (max (-d i) 0).toNat}) :=
    { toFun := fun y i j => Ideal.Quotient.mk _ ⟨y.1 i j, (mem_intMat_iff' v y.1).1 y.2 i j⟩
      map_zero' := by
        funext i j
        exact map_zero (Ideal.Quotient.mk (Ideal.span {(⟨ϖ, hϖO⟩ : v.adicCompletionIntegers F) ^ (max (-d i) 0).toNat}))
      map_add' := fun y z => by
        funext i j
        exact map_add (Ideal.Quotient.mk (Ideal.span {(⟨ϖ, hϖO⟩ : v.adicCompletionIntegers F) ^ (max (-d i) 0).toNat}))
          ⟨y.1 i j, (mem_intMat_iff' v y.1).1 y.2 i j⟩ ⟨z.1 i j, (mem_intMat_iff' v z.1).1 z.2 i j⟩ }
  have hψ : ∀ (y : GlobalTheory.SplitIdx.intMat F v m n) i j, ψ y i j =
      Ideal.Quotient.mk (Ideal.span {(⟨ϖ, hϖO⟩ : v.adicCompletionIntegers F) ^ (max (-d i) 0).toNat}) ⟨y.1 i j, (mem_intMat_iff' v y.1).1 y.2 i j⟩ :=
    fun _ _ _ => rfl
  have hker : ψ.ker = (AddSubgroup.comap (GlobalTheory.SplitIdx.mulL (n := n) (Matrix.diagonal fun i => ϖ ^ d i))
      (GlobalTheory.SplitIdx.intMat F v m n)).addSubgroupOf (GlobalTheory.SplitIdx.intMat F v m n) := by
    ext y
    rw [AddMonoidHom.mem_ker, AddSubgroup.mem_addSubgroupOf, AddSubgroup.mem_comap, mem_intMat_iff',
      mulL_apply']
    simp only [Matrix.diagonal_mul]
    constructor
    · intro h i j
      have h1 : ψ y i j = 0 := congrFun (congrFun h i) j
      rw [hψ, Ideal.Quotient.eq_zero_iff_mem] at h1
      exact (zpow_mul_mem_iff v hϖ hϖO (d i) ⟨y.1 i j, (mem_intMat_iff' v y.1).1 y.2 i j⟩).2 h1
    · intro h
      funext i j
      show ψ y i j = 0
      rw [hψ, Ideal.Quotient.eq_zero_iff_mem]
      exact (zpow_mul_mem_iff v hϖ hϖO (d i) ⟨y.1 i j, (mem_intMat_iff' v y.1).1 y.2 i j⟩).1 (h i j)
  have hsurj : Function.Surjective ψ := by
    intro z
    choose w hw using fun i j => Ideal.Quotient.mk_surjective (z i j)
    refine ⟨⟨fun i j => (w i j : v.adicCompletion F), (mem_intMat_iff' v _).2 fun i j => (w i j).2⟩, ?_⟩
    funext i j
    rw [hψ]
    exact hw i j
  rw [AddSubgroup.relIndex, ← hker, AddSubgroup.index_ker, AddMonoidHom.range_eq_top.2 hsurj,
    AddSubgroup.card_top, Nat.card_pi]
  simp only [Nat.card_pi, card_quot_pow v hϖ hϖO, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    ← pow_mul, Finset.prod_pow_eq_pow_sum]
  congr 1
  rw [toNat_sum, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

end GlobalTheory.SplitIdx.LocIndex
