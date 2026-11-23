import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsPairingSingleNe
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsSymmetricElementaryDivisorsUnitary

noncomputable section

open Matrix Formalism.UG GlobalTheory.Hk3 GlobalTheory.FinWeil GlobalTheory.SphTheta ValuativeRel Classical
open GlobalTheory.LFun (HasSatU IsSatVecU heckeVec)
open GlobalTheory.LGrp (bcParam extProd)
open GlobalTheory.WeilM (UG IsQuad Darboux symp sbClass SB IsWeilB IsWeilPair TestClass schr dbl diagCols)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalThetaInertPlace (str chi IsUnramAdd)
open scoped TensorProduct

namespace GlobalTheory.SphTheta.IntTranslate

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {m : ℕ}

theorem mem_int {α β : Type} {A : Matrix α β L} : A ∈ intMat L α β ↔ ∀ i j, A i j ∈ intL L := Iff.rfl

theorem int_mul {A B : Matrix (Fin m) (Fin m) L} (hA : A ∈ intMat L (Fin m) (Fin m))
    (hB : B ∈ intMat L (Fin m) (Fin m)) : A * B ∈ intMat L (Fin m) (Fin m) := by
  rw [mem_int] at hA hB ⊢
  intro i j
  rw [Matrix.mul_apply]
  exact Subring.sum_mem _ fun k _ => Subring.mul_mem _ (hA i k) (hB k j)

theorem one_int : (1 : Matrix (Fin m) (Fin m) L) ∈ intMat L (Fin m) (Fin m) := by
  rw [mem_int]
  intro i j
  rw [Matrix.one_apply]
  split_ifs
  · exact Subring.one_mem _
  · exact Subring.zero_mem _

theorem int_transpose {A : Matrix (Fin m) (Fin m) L} :
    Aᵀ ∈ intMat L (Fin m) (Fin m) ↔ A ∈ intMat L (Fin m) (Fin m) := by
  simp only [mem_int, Matrix.transpose_apply]
  exact ⟨fun h i j => h j i, fun h i j => h j i⟩

def IsIntUnit (g : GL (Fin m) L) : Prop :=
  g.1 ∈ intMat L (Fin m) (Fin m) ∧ (g⁻¹).1 ∈ intMat L (Fin m) (Fin m)

theorem IsIntUnit.left {g : GL (Fin m) L} (hg : IsIntUnit g) (X : Matrix (Fin m) (Fin m) L) :
    g.1 * X ∈ intMat L (Fin m) (Fin m) ↔ X ∈ intMat L (Fin m) (Fin m) := by
  unfold IsIntUnit at hg
  constructor
  · intro h
    have e : X = (g⁻¹).1 * (g.1 * X) := by rw [← mul_assoc, Units.inv_mul, one_mul]
    rw [e]
    exact int_mul hg.2 h
  · intro h
    exact int_mul hg.1 h

theorem IsIntUnit.right {g : GL (Fin m) L} (hg : IsIntUnit g) (X : Matrix (Fin m) (Fin m) L) :
    X * g.1 ∈ intMat L (Fin m) (Fin m) ↔ X ∈ intMat L (Fin m) (Fin m) := by
  unfold IsIntUnit at hg
  constructor
  · intro h
    have e : X = (X * g.1) * (g⁻¹).1 := by rw [mul_assoc, Units.mul_inv, mul_one]
    rw [e]
    exact int_mul h hg.2
  · intro h
    exact int_mul h hg.1

theorem isIntUnit_of_mem {g : GL (Fin m) L} (h : g ∈ GLint (Fin m) (intL L)) : IsIntUnit g := by
  unfold IsIntUnit
  exact ⟨mem_int.2 fun i j => P.cartan_entries_of_mem (intL L) g h i j,
    mem_int.2 fun i j => P.cartan_entries_of_mem (intL L) g⁻¹ (inv_mem h) i j⟩

theorem antiJ_transpose : (antiJ L m)ᵀ = antiJ L m := by
  ext i j
  simp only [Matrix.transpose_apply, antiJ]
  rw [Nat.add_comm j.val i.val]

theorem isIntUnit_antiG : IsIntUnit (antiG L m) := by
  have hJ : antiJ L m ∈ intMat L (Fin m) (Fin m) := by
    rw [mem_int]
    intro i j
    simp only [antiJ]
    split_ifs
    · exact Subring.one_mem _
    · exact Subring.zero_mem _
  exact And.intro hJ hJ

def glT (g : GL (Fin m) L) : GL (Fin m) L :=
  ⟨g.1ᵀ, (g⁻¹).1ᵀ, by rw [← Matrix.transpose_mul, g.inv_mul, Matrix.transpose_one],
    by rw [← Matrix.transpose_mul, g.mul_inv, Matrix.transpose_one]⟩

theorem IsIntUnit.glT {g : GL (Fin m) L} (hg : IsIntUnit g) : IsIntUnit (glT g) := by
  unfold IsIntUnit at hg ⊢
  exact ⟨int_transpose.2 hg.1, int_transpose.2 hg.2⟩

theorem ordL_congr {x y : L} (h : Valued.v x = Valued.v y) : ordL x = ordL y := by
  simp only [ordL, h]

theorem diag_mul {A B : Matrix (Fin m) (Fin m) L} (hA : A.BlockTriangular id) (hB : B.BlockTriangular id)
    (r : Fin m) : (A * B) r r = A r r * B r r := by
  rw [Matrix.mul_apply, Finset.sum_eq_single r]
  · intro k _ hk
    rcases lt_or_gt_of_ne hk with h | h
    · rw [hA (show id k < id r from h), zero_mul]
    · rw [hB (show id r < id k from h), mul_zero]
  · intro h
    exact absurd (Finset.mem_univ r) h

private lemma valued_v_le_one_of_mem_intL {x : L} (h : x ∈ intL L) : Valued.v x ≤ 1 := h

theorem v_diag_le {A B : GL (Fin m) L} (hA : A.1.BlockTriangular id) (hB : B.1.BlockTriangular id)
    (h : (A⁻¹).1 * B.1 ∈ intMat L (Fin m) (Fin m)) (r : Fin m) : Valued.v (B.1 r r) ≤ Valued.v (A.1 r r) := by
  have hAi : (A⁻¹).1.BlockTriangular id := by
    rw [Matrix.coe_units_inv]
    exact Matrix.blockTriangular_inv_of_blockTriangular hA
  have h1 : (A⁻¹).1 r r * A.1 r r = 1 := by
    rw [← diag_mul hAi hA r, Units.inv_mul, Matrix.one_apply_eq]
  have h2 : Valued.v ((A⁻¹).1 r r * B.1 r r) ≤ 1 := by
    rw [← diag_mul hAi hB r]
    exact valued_v_le_one_of_mem_intL ((mem_int.1 h) r r)
  have h3 : Valued.v ((A⁻¹).1 r r) * Valued.v (A.1 r r) = 1 := by
    rw [← map_mul, h1, map_one]
  calc Valued.v (B.1 r r) = Valued.v ((A⁻¹).1 r r * B.1 r r) * Valued.v (A.1 r r) := by
        rw [map_mul, mul_comm (Valued.v ((A⁻¹).1 r r)) (Valued.v (B.1 r r)), mul_assoc, h3, mul_one]
    _ ≤ 1 * Valued.v (A.1 r r) := by gcongr
    _ = Valued.v (A.1 r r) := one_mul _

theorem ordL_diag_eq {A B : GL (Fin m) L} (hA : A.1.BlockTriangular id) (hB : B.1.BlockTriangular id)
    (h1 : (A⁻¹).1 * B.1 ∈ intMat L (Fin m) (Fin m)) (h2 : (B⁻¹).1 * A.1 ∈ intMat L (Fin m) (Fin m)) (r : Fin m) :
    ordL (A.1 r r) = ordL (B.1 r r) := by
  apply ordL_congr
  exact le_antisymm (v_diag_le hB hA h2 r) (v_diag_le hA hB h1 r)

end GlobalTheory.SphTheta.IntTranslate

namespace GlobalTheory.SphTheta.IntTranslate

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {m : ℕ}

theorem exists_min_of_preorder {κ : Type} (R : κ → κ → Prop) (hR : ∀ x, R x x)
    (ht : ∀ x y z, R x y → R y z → R x z) :
    ∀ s : Finset κ, s.Nonempty → ∃ k ∈ s, ∀ l ∈ s, R l k → R k l := by
  intro s
  induction s using Finset.induction_on with
  | empty =>
    intro h
    simp at h
  | @insert a s ha ih =>
    intro _
    rcases s.eq_empty_or_nonempty with hs | hs
    · subst hs
      refine ⟨a, by simp, fun l hl _ => ?_⟩
      simp at hl
      subst hl
      exact hR _
    · obtain ⟨k, hk, hmin⟩ := ih hs
      by_cases hak : R a k ∧ ¬ R k a
      · refine ⟨a, Finset.mem_insert_self a s, fun l hl hla => ?_⟩
        rw [Finset.mem_insert] at hl
        rcases hl with rfl | hl
        · exact hR _
        · exact ht _ _ _ hak.1 (hmin l hl (ht _ _ _ hla hak.1))
      · refine ⟨k, Finset.mem_insert_of_mem hk, fun l hl hlk => ?_⟩
        rw [Finset.mem_insert] at hl
        rcases hl with rfl | hl
        · by_contra hc
          exact hak ⟨hlk, hc⟩
        · exact hmin l hl hlk

theorem mem_iff_of_mutual {A B : GL (Fin m) L} (h1 : (A⁻¹).1 * B.1 ∈ intMat L (Fin m) (Fin m))
    (h2 : (B⁻¹).1 * A.1 ∈ intMat L (Fin m) (Fin m)) (t : Matrix (Fin m) (Fin m) L) :
    t * B.1 ∈ intMat L (Fin m) (Fin m) ↔ t * A.1 ∈ intMat L (Fin m) (Fin m) := by
  constructor
  · intro h
    have e : t * A.1 = (t * B.1) * ((B⁻¹).1 * A.1) := by
      rw [mul_assoc, ← mul_assoc B.1, Units.mul_inv, one_mul]
    rw [e]
    exact int_mul h h2
  · intro h
    have e : t * B.1 = (t * A.1) * ((A⁻¹).1 * B.1) := by
      rw [mul_assoc, ← mul_assoc A.1, Units.mul_inv, one_mul]
    rw [e]
    exact int_mul h h1

theorem sum_mul_eq_zero_of_indicator {κ : Type} (a : κ → ℂ) (W : κ → GL (Fin m) L) (g : κ → ℂ)
    (hg : ∀ k l, ((W k)⁻¹).1 * (W l).1 ∈ intMat L (Fin m) (Fin m) →
      ((W l)⁻¹).1 * (W k).1 ∈ intMat L (Fin m) (Fin m) → g k = g l) :
    ∀ s : Finset κ, (∀ t : GL (Fin m) L,
      ∑ k ∈ s, a k * (if t.1 * (W k).1 ∈ intMat L (Fin m) (Fin m) then 1 else 0) = 0) →
      ∑ k ∈ s, a k * g k = 0 := by
  intro s
  induction s using Finset.strongInduction with
  | H s ih =>
    intro H
    rcases s.eq_empty_or_nonempty with hs | hs
    · subst hs
      simp
    · obtain ⟨k, hk, hmax⟩ := exists_min_of_preorder
        (fun x y => ((W y)⁻¹).1 * (W x).1 ∈ intMat L (Fin m) (Fin m))
        (fun x => by simp only [Units.inv_mul]; exact one_int)
        (fun x y z hxy hyz => by
          have := int_mul hyz hxy
          rwa [mul_assoc, ← mul_assoc (W y).1, Units.mul_inv, one_mul] at this)
        s hs
      have hsum : ∑ l ∈ s.filter (fun l => ((W k)⁻¹).1 * (W l).1 ∈ intMat L (Fin m) (Fin m)), a l = 0 := by
        have := H (W k)⁻¹
        simp only [mul_ite, mul_one, mul_zero] at this
        rw [← Finset.sum_filter] at this
        exact this
      have hsub : ∀ t : GL (Fin m) L,
          ∑ l ∈ s.filter (fun l => ¬ (((W k)⁻¹).1 * (W l).1 ∈ intMat L (Fin m) (Fin m))),
            a l * (if t.1 * (W l).1 ∈ intMat L (Fin m) (Fin m) then 1 else 0) = 0 := by
        intro t
        have e : ∀ l ∈ s.filter (fun l => ((W k)⁻¹).1 * (W l).1 ∈ intMat L (Fin m) (Fin m)),
            a l * (if t.1 * (W l).1 ∈ intMat L (Fin m) (Fin m) then 1 else 0) =
              a l * (if t.1 * (W k).1 ∈ intMat L (Fin m) (Fin m) then 1 else 0) := by
          intro l hl
          rw [Finset.mem_filter] at hl
          rw [mem_iff_of_mutual hl.2 (hmax l hl.1 hl.2)]
        have h0 : ∑ l ∈ s.filter (fun l => ((W k)⁻¹).1 * (W l).1 ∈ intMat L (Fin m) (Fin m)),
            a l * (if t.1 * (W l).1 ∈ intMat L (Fin m) (Fin m) then 1 else 0) = 0 := by
          rw [Finset.sum_congr rfl e, ← Finset.sum_mul, hsum, zero_mul]
        have := H t
        rw [← Finset.sum_filter_add_sum_filter_not s
          (fun l => ((W k)⁻¹).1 * (W l).1 ∈ intMat L (Fin m) (Fin m)), h0, zero_add] at this
        exact this
      have hrest := ih _ (Finset.filter_ssubset.2 ⟨k, hk, by
        simp only [not_not, Units.inv_mul]
        exact one_int⟩) hsub
      have e : ∀ l ∈ s.filter (fun l => ((W k)⁻¹).1 * (W l).1 ∈ intMat L (Fin m) (Fin m)),
          a l * g l = a l * g k := by
        intro l hl
        rw [Finset.mem_filter] at hl
        rw [hg k l hl.2 (hmax l hl.1 hl.2)]
      rw [← Finset.sum_filter_add_sum_filter_not s
        (fun l => ((W k)⁻¹).1 * (W l).1 ∈ intMat L (Fin m) (Fin m)), hrest, add_zero,
        Finset.sum_congr rfl e, ← Finset.sum_mul, hsum, zero_mul]

end GlobalTheory.SphTheta.IntTranslate

namespace GlobalTheory.SphTheta.IntTranslate

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {m : ℕ}

theorem glT_val (g : GL (Fin m) L) : (glT g).1 = g.1ᵀ := rfl

theorem antiG_val : (antiG L m).1 = antiJ L m := rfl

def leftSum {ι : Type} [Fintype ι] (c : ι → ℂ) (U : ι → GL (Fin m) L) (t : GL (Fin m) L) : ℂ :=
  ∑ i, c i * (if t.1 * (U i).1 ∈ intMat L (Fin m) (Fin m) then 1 else 0)

def rightSum {κ : Type} [Fintype κ] (c' : κ → ℂ) (V : κ → GL (Fin m) L) (t : GL (Fin m) L) : ℂ :=
  ∑ j, c' j * (if (V j).1 * t.1 ∈ intMat L (Fin m) (Fin m) then 1 else 0)

theorem leftSum_mul {ι : Type} [Fintype ι] (c : ι → ℂ) (U : ι → GL (Fin m) L) {g : GL (Fin m) L}
    (hg : IsIntUnit g) (t : GL (Fin m) L) : leftSum c U (g * t) = leftSum c U t := by
  simp only [leftSum, Units.val_mul, mul_assoc, hg.left]

theorem rightSum_mul {κ : Type} [Fintype κ] (c' : κ → ℂ) (V : κ → GL (Fin m) L) {g : GL (Fin m) L}
    (hg : IsIntUnit g) (t : GL (Fin m) L) : rightSum c' V (t * g) = rightSum c' V t := by
  simp only [rightSum, Units.val_mul, ← mul_assoc, hg.right]

private lemma glT_mul (x y : GL (Fin m) L) : glT (x * y) = glT y * glT x := by
  ext1
  simp only [glT_val, Units.val_mul, Matrix.transpose_mul]

private lemma mul_antiG_glT_mem_intMat_iff (t X : GL (Fin m) L) :
    t.1 * (antiG L m * glT X * antiG L m).1 ∈ intMat L (Fin m) (Fin m) ↔
      X.1 * (antiG L m * glT t).1 ∈ intMat L (Fin m) (Fin m) := by
  rw [← int_transpose, ← (isIntUnit_antiG (L := L) (m := m)).left (X.1 * (antiG L m * glT t).1)]
  simp only [Units.val_mul, glT_val, antiG_val, Matrix.transpose_mul, Matrix.transpose_transpose,
    antiJ_transpose, mul_assoc]

theorem leftSum_eq_swap {ϖ : L} {σ : L →+* L} {q : ℕ} (hU : IsUnramInv ϖ σ q) {ι κ : Type} [Fintype ι] [Fintype κ]
    (c : ι → ℂ) (c' : κ → ℂ) (U : ι → GL (Fin m) L) (V : κ → GL (Fin m) L)
    (H : ∀ t : GL (Fin m) L, leftSum c U t = rightSum c' V t) (t : GL (Fin m) L) :
    leftSum c U t = leftSum c' (fun j => antiG L m * glT (V j) * antiG L m) t := by
  have hR : ∀ x g : GL (Fin m) L, IsIntUnit g → leftSum c U (x * g) = leftSum c U x :=
    fun x g hg => by rw [H, H, rightSum_mul c' V hg]
  have hT : leftSum c U (glT t) = leftSum c U t := by
    obtain ⟨a, -, k₁, hk₁, k₂, hk₂, e⟩ := GlobalTheory.LFun.UnitaryDiv.exists_cartan hU t
    obtain ⟨D, hD⟩ : ∃ D : GL (Fin m) L, D = k₁⁻¹ * t * k₂⁻¹ := ⟨_, rfl⟩
    have htD : t = k₁ * D * k₂ := by
      rw [hD]
      group
    have hDv : D.1 = Matrix.diagonal (fun i => ϖ ^ a i) := by
      rw [hD, Units.val_mul, Units.val_mul, e]
      simp only [← mul_assoc, Units.inv_mul, one_mul]
      rw [mul_assoc, Units.mul_inv, mul_one]
    have hDT : glT D = D := by
      ext1
      rw [glT_val, hDv, Matrix.diagonal_transpose]
    calc leftSum c U (glT t) = leftSum c U (glT k₂ * (D * glT k₁)) := by
          rw [htD, glT_mul, glT_mul, hDT]
      _ = leftSum c U (D * glT k₁) := leftSum_mul c U (IsIntUnit.glT (isIntUnit_of_mem hk₂)) _
      _ = leftSum c U D := hR _ _ (IsIntUnit.glT (isIntUnit_of_mem hk₁))
      _ = leftSum c U (D * k₂) := (hR _ _ (isIntUnit_of_mem hk₂)).symm
      _ = leftSum c U (k₁ * (D * k₂)) := (leftSum_mul c U (isIntUnit_of_mem hk₁) _).symm
      _ = leftSum c U t := by rw [htD, mul_assoc]
  have hsw : leftSum c' (fun j => antiG L m * glT (V j) * antiG L m) t =
      rightSum c' V (antiG L m * glT t) := by
    dsimp only [leftSum, rightSum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_antiG_glT_mem_intMat_iff]
  rw [hsw, ← H, leftSum_mul c U isIntUnit_antiG, hT]

private lemma antiJ_mul_mul_antiJ_apply (M : Matrix (Fin m) (Fin m) L) (r s : Fin m) :
    (antiJ L m * M * antiJ L m) r s = M r.rev s.rev := by
  have hl : ∀ (N : Matrix (Fin m) (Fin m) L) (r s : Fin m), (antiJ L m * N) r s = N r.rev s := by
    intro N r s
    rw [Matrix.mul_apply, Finset.sum_eq_single r.rev]
    · have h1 : r.val + r.rev.val + 1 = m := by
        rw [Fin.val_rev]
        have := r.isLt
        omega
      simp only [antiJ]
      rw [if_pos h1, one_mul]
    · intro b _ hb
      have h2 : ¬ (r.val + b.val + 1 = m) := by
        intro h
        apply hb
        ext
        rw [Fin.val_rev]
        omega
      simp only [antiJ]
      rw [if_neg h2, zero_mul]
    · intro h
      exact absurd (Finset.mem_univ _) h
  have hr : ∀ (N : Matrix (Fin m) (Fin m) L) (r s : Fin m), (N * antiJ L m) r s = N r s.rev := by
    intro N r s
    rw [Matrix.mul_apply, Finset.sum_eq_single s.rev]
    · have h1 : s.rev.val + s.val + 1 = m := by
        rw [Fin.val_rev]
        have := s.isLt
        omega
      simp only [antiJ]
      rw [if_pos h1, mul_one]
    · intro b _ hb
      have h2 : ¬ (b.val + s.val + 1 = m) := by
        intro h
        apply hb
        ext
        rw [Fin.val_rev]
        omega
      simp only [antiJ]
      rw [if_neg h2, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ _) h
  rw [hr, hl]

end GlobalTheory.SphTheta.IntTranslate

namespace GlobalTheory.SphTheta

open IntTranslate in

theorem sum_ordL_diag_eq_of_indicator : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L)
    (σ : L →+* L) (q : ℕ), IsUnramInv ϖ σ q → ∀ (m : ℕ) (ι κ : Type) [Fintype ι] [Fintype κ] (c : ι → ℂ)
    (c' : κ → ℂ) (U : ι → GL (Fin m) L) (V : κ → GL (Fin m) L), (∀ i, (U i).1.BlockTriangular id) →
    (∀ j, (V j).1.BlockTriangular id) → (∀ t : GL (Fin m) L, ∑ i, c i * (if t.1 * (U i).1 ∈ intMat L (Fin m) (Fin m)
      then 1 else 0) = ∑ j, c' j * (if (V j).1 * t.1 ∈ intMat L (Fin m) (Fin m) then 1 else 0)) →
    ∀ f : (Fin m → ℤ) → ℂ, ∑ i, c i * f (fun r => ordL ((U i).1 r r)) =
      ∑ j, c' j * f (fun r => ordL ((V j).1 r.rev r.rev)) := by
  intro L _ _ ϖ σ q hU m ι κ _ _ c c' U V hUt hVt H f
  have hsw : ∀ t : GL (Fin m) L, leftSum c U t = leftSum c' (fun j => antiG L m * glT (V j) * antiG L m) t :=
    fun t => leftSum_eq_swap hU c c' U V H t
  have htri : ∀ k, (Sum.elim U (fun j => antiG L m * glT (V j) * antiG L m) k).1.BlockTriangular id := by
    rintro (i | j)
    · exact hUt i
    · intro r s hrs
      simp only [Sum.elim_inr, Units.val_mul, glT_val, antiG_val]
      rw [GlobalTheory.SphTheta.IntTranslate.antiJ_mul_mul_antiJ_apply, Matrix.transpose_apply]
      exact hVt j (show id r.rev < id s.rev from Fin.rev_lt_rev.2 hrs)
  have hd : ∀ j r, (antiG L m * glT (V j) * antiG L m).1 r r = (V j).1 r.rev r.rev := by
    intro j r
    simp only [Units.val_mul, glT_val, antiG_val]
    rw [GlobalTheory.SphTheta.IntTranslate.antiJ_mul_mul_antiJ_apply, Matrix.transpose_apply]
  have hz : ∀ t : GL (Fin m) L, ∑ k ∈ Finset.univ, Sum.elim c (fun j => -c' j) k *
      (if t.1 * (Sum.elim U (fun j => antiG L m * glT (V j) * antiG L m) k).1 ∈ intMat L (Fin m) (Fin m)
        then 1 else 0) = 0 := by
    intro t
    rw [Fintype.sum_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr, neg_mul, Finset.sum_neg_distrib, ← sub_eq_add_neg]
    exact sub_eq_zero.2 (hsw t)
  have key := sum_mul_eq_zero_of_indicator (Sum.elim c (fun j => -c' j))
    (Sum.elim U (fun j => antiG L m * glT (V j) * antiG L m))
    (fun k => f (fun r => ordL ((Sum.elim U (fun j => antiG L m * glT (V j) * antiG L m) k).1 r r)))
    (fun k l h1 h2 => congrArg f (funext fun r => ordL_diag_eq (htri k) (htri l) h1 h2 r))
    Finset.univ hz
  rw [Fintype.sum_sum_type] at key
  simp only [Sum.elim_inl, Sum.elim_inr, neg_mul, Finset.sum_neg_distrib, hd, ← sub_eq_add_neg] at key
  exact sub_eq_zero.1 key

end GlobalTheory.SphTheta
