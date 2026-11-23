import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RpowNegLeNormOfComponent
import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatVecUOfIsSphericalU
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
open NumberField IsDedekindDomain GlobalTheory.LatHecke Formalism.UG

noncomputable section

namespace GlobalTheory.DiagElem

variable {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E))

theorem le_exp_neg_one_of_lt_one {x : WithZero (Multiplicative ℤ)} (h : x < 1) :
    x ≤ WithZero.exp (-1) := by
  rcases eq_or_ne x 0 with rfl | hx
  · exact zero_le
  · rw [← WithZero.exp_log hx] at h ⊢
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at h
    rw [WithZero.exp_le_exp]
    omega

theorem mem_std {n : ℕ} (x : Fin n → w.adicCompletion E) :
    x ∈ (std (w.adicCompletionIntegers E) (w.adicCompletion E) n).1 ↔
      ∀ i, Valued.v (x i) ≤ 1 := by
  constructor
  · intro hx
    refine Submodule.span_induction (p := fun x _ => ∀ i, Valued.v (x i) ≤ 1) ?_ ?_ ?_ ?_ hx
    · rintro _ ⟨j, rfl⟩ i
      by_cases h : i = j
      · subst h; simp
      · simp [Pi.single_apply, h]
    · intro i; simp
    · intro a b _ _ ha hb i
      simpa using (Valued.v.map_add (a i) (b i)).trans (max_le (ha i) (hb i))
    · intro c a _ ha i
      have hc : Valued.v (c : w.adicCompletion E) ≤ 1 := c.2
      show Valued.v ((c : w.adicCompletion E) * a i) ≤ 1
      rw [map_mul]
      exact mul_le_one' hc (ha i)
  · intro hx
    have e : x = ∑ i, (⟨x i, hx i⟩ : w.adicCompletionIntegers E) • Pi.basisFun (w.adicCompletion E) (Fin n) i := by
      ext j
      rw [Finset.sum_apply, Finset.sum_eq_single j (fun b _ hb => by simp [Pi.single_apply, Ne.symm hb]) (by simp)]
      simp only [Pi.basisFun_apply, Pi.smul_apply, Pi.single_eq_same]
      rw [Algebra.smul_def]
      simp
    rw [e]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

def dEnt {n : ℕ} (ϖ : w.adicCompletion E) (S : Finset (Fin n)) (i : Fin n) : w.adicCompletion E :=
  if i ∈ S then ϖ else 1

theorem mem_glMap_diag {n : ℕ} {ϖ : w.adicCompletion E} (hϖ : IsUnifV E w ϖ) (S : Finset (Fin n))
    (d : GL (Fin n) (w.adicCompletion E))
    (hd : (d : Matrix (Fin n) (Fin n) (w.adicCompletion E)) = Matrix.diagonal (dEnt w ϖ S))
    (x : Fin n → w.adicCompletion E) :
    x ∈ glMap d (std (w.adicCompletionIntegers E) (w.adicCompletion E) n).1 ↔
      ∀ i, Valued.v (x i) ≤ Valued.v (dEnt w ϖ S i) := by
  have hϖ0 : ϖ ≠ 0 := fun h0 => by simp [IsUnifV, h0] at hϖ
  have hf0 : ∀ i, dEnt w ϖ S i ≠ 0 := fun i => by unfold dEnt; split_ifs <;> simp [hϖ0]
  simp only [glMap, Submodule.mem_map, LinearMap.coe_restrictScalars, Matrix.toLin'_apply, hd,
    Matrix.mulVec_diagonal, mem_std]
  constructor
  · rintro ⟨y, hy, rfl⟩ i
    rw [Matrix.mulVec_diagonal, map_mul]
    exact mul_le_of_le_one_right' (hy i)
  · intro hx
    refine ⟨fun i => x i / dEnt w ϖ S i, fun i => ?_, ?_⟩
    · rw [map_div₀]
      exact div_le_one_of_le₀ (hx i) zero_le
    · funext i
      rw [Matrix.mulVec_diagonal, mul_div_cancel₀ _ (hf0 i)]

end GlobalTheory.DiagElem

namespace GlobalTheory.DiagElem

variable {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E))

def redS {n : ℕ} (S : Finset (Fin n)) :
    (std (w.adicCompletionIntegers E) (w.adicCompletion E) n).1 →ₗ[w.adicCompletionIntegers E]
      (S → IsLocalRing.ResidueField (w.adicCompletionIntegers E)) where
  toFun x i := IsLocalRing.residue _ ⟨x.1 i, (mem_std w x.1).1 x.2 i⟩
  map_add' x y := by
    funext i
    rw [Pi.add_apply, ← map_add]
    rfl
  map_smul' c x := by
    funext i
    rw [Pi.smul_apply, RingHom.id_apply, Algebra.smul_def, IsLocalRing.ResidueField.algebraMap_eq,
      ← map_mul]
    congr 1

theorem redS_surjective {n : ℕ} (S : Finset (Fin n)) : Function.Surjective (redS w S) := by
  intro c
  choose a ha using fun i : S => IsLocalRing.residue_surjective (c i)
  refine ⟨⟨fun j => if h : j ∈ S then (a ⟨j, h⟩ : w.adicCompletion E) else 0,
    (mem_std w _).2 fun j => ?_⟩, ?_⟩
  · split_ifs
    · exact (a _).2
    · simp
  · funext ⟨i, hi⟩
    change IsLocalRing.residue _ _ = _
    rw [← ha]
    congr 1
    ext
    simp [hi]

theorem glMap_diag_mem_subElem : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n : ℕ) (ϖ : w.adicCompletion E), IsUnifV E w ϖ → ∀ (S : Finset (Fin n)) (d : GL (Fin n) (w.adicCompletion E)), (d : Matrix (Fin n) (Fin n) (w.adicCompletion E)) = Matrix.diagonal (fun i => if i ∈ S then ϖ else 1) → haveI := GlobalTheory.RowSatakeBound.finite_residue w; glMap d (std (w.adicCompletionIntegers E) (w.adicCompletion E) n).1 ∈ Subtype.val '' subElem S.card (std (w.adicCompletionIntegers E) (w.adicCompletion E) n) := by
  intro E _ _ w n ϖ hϖ S d hd
  have hd' : (d : Matrix (Fin n) (Fin n) (w.adicCompletion E)) = Matrix.diagonal (dEnt w ϖ S) := hd
  have hϖle : Valued.v ϖ ≤ WithZero.exp (-1 : ℤ) := hϖ.le
  have hexp : (WithZero.exp (-1 : ℤ) : WithZero (Multiplicative ℤ)) < 1 := by
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; norm_num
  refine ⟨⟨_, glMap_isLattice d (std _ _ n)⟩, ⟨⟨?_, ?_⟩, ?_⟩, rfl⟩
  · intro x hx
    rw [mem_glMap_diag w hϖ S d hd' x] at hx
    rw [mem_std]
    intro i
    refine (hx i).trans ?_
    unfold dEnt
    split_ifs
    · exact hϖle.trans hexp.le
    · simp
  · have hk : (glMap d (std (w.adicCompletionIntegers E) (w.adicCompletion E) n).1).comap
        (std (w.adicCompletionIntegers E) (w.adicCompletion E) n).1.subtype =
        LinearMap.ker (redS w S) := by
      ext x
      rw [Submodule.mem_comap, Submodule.subtype_apply, mem_glMap_diag w hϖ S d hd',
        LinearMap.mem_ker]
      have hx := (mem_std w x.1).1 x.2
      constructor
      · intro h
        funext ⟨i, hi⟩
        change IsLocalRing.residue _ _ = 0
        rw [IsLocalRing.residue_eq_zero_iff]
        apply Valuation.Integer.not_isUnit_iff_valuation_lt_one.mpr
        have := h i
        unfold dEnt at this
        rw [if_pos hi] at this
        exact lt_of_le_of_lt (this.trans hϖle) hexp
      · intro h i
        unfold dEnt
        split_ifs with hi
        · have := congrFun h ⟨i, hi⟩
          change IsLocalRing.residue _ _ = 0 at this
          rw [IsLocalRing.residue_eq_zero_iff] at this
          rw [hϖ]
          exact le_exp_neg_one_of_lt_one (Valuation.Integer.not_isUnit_iff_valuation_lt_one.mp this)
        · rw [map_one]; exact hx i
    change Nat.card ((std (w.adicCompletionIntegers E) (w.adicCompletion E) n).1 ⧸
      (glMap d (std (w.adicCompletionIntegers E) (w.adicCompletion E) n).1).comap
        (std (w.adicCompletionIntegers E) (w.adicCompletion E) n).1.subtype) = _
    rw [hk, Nat.card_congr (LinearMap.quotKerEquivOfSurjective _ (redS_surjective w S)).toEquiv,
      Nat.card_fun, Nat.card_eq_fintype_card (α := S), Fintype.card_coe]
    rfl
  · rw [Submodule.smul_le]
    intro r hr x hx
    rw [mem_glMap_diag w hϖ S d hd']
    rw [mem_std] at hx
    have hr1 : Valued.v (r : w.adicCompletion E) < 1 :=
      Valuation.Integer.not_isUnit_iff_valuation_lt_one.mp hr
    intro i
    have hri : Valued.v ((r • x) i) < 1 := by
      change Valued.v ((r : w.adicCompletion E) * x i) < 1
      rw [map_mul]
      exact lt_of_le_of_lt (mul_le_of_le_one_right' (hx i)) hr1
    unfold dEnt
    split_ifs
    · rw [hϖ]; exact le_exp_neg_one_of_lt_one hri
    · rw [map_one]; exact hri.le

end GlobalTheory.DiagElem
