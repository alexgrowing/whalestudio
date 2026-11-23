import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.SpectralGap.BesselIntegralSquareIntegrable
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.UHMulInv
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.MulVecFixOfSupp

noncomputable section

open Matrix
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.Lap

theorem mul_mem_UH' {k r : ℕ} {g x : Mat k r} (hg : g ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r))
    (hx : x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) : g * x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) := by
  have hg' : gᴴ * Formalism.QuantumDeterminants.Hpk k r * g = Formalism.QuantumDeterminants.Hpk k r := hg
  have hx' : xᴴ * Formalism.QuantumDeterminants.Hpk k r * x = Formalism.QuantumDeterminants.Hpk k r := hx
  show (g * x)ᴴ * Formalism.QuantumDeterminants.Hpk k r * (g * x) = Formalism.QuantumDeterminants.Hpk k r
  rw [Matrix.conjTranspose_mul]
  calc xᴴ * gᴴ * Formalism.QuantumDeterminants.Hpk k r * (g * x) = xᴴ * (gᴴ * Formalism.QuantumDeterminants.Hpk k r * g) * x := by
        simp only [Matrix.mul_assoc]
    _ = _ := by rw [hg', hx']

theorem inv_mem_UH' {k r : ℕ} {g : Mat k r} (hg : g ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) :
    g⁻¹ ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) := by
  have hg' : gᴴ * Formalism.QuantumDeterminants.Hpk k r * g = Formalism.QuantumDeterminants.Hpk k r := hg
  have h1 : g * g⁻¹ = 1 := ReciprocityTheory.ChartRestriction.DS.Xi.StepA.UH_mul_inv k r hg
  show (g⁻¹)ᴴ * Formalism.QuantumDeterminants.Hpk k r * g⁻¹ = Formalism.QuantumDeterminants.Hpk k r
  calc (g⁻¹)ᴴ * Formalism.QuantumDeterminants.Hpk k r * g⁻¹ = (g⁻¹)ᴴ * (gᴴ * Formalism.QuantumDeterminants.Hpk k r * g) * g⁻¹ := by rw [hg']
    _ = (g * g⁻¹)ᴴ * Formalism.QuantumDeterminants.Hpk k r * (g * g⁻¹) := by
        rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
    _ = _ := by rw [h1]; simp

def blkW (k r : ℕ) (y : Mat k r) : Matrix (Fin k) (Fin k) ℂ :=
  fun a b => y ⟨r + a.val, by omega⟩ ⟨r + b.val, by omega⟩

theorem mulVec_bvec_apply' {m : ℕ} (y : Matrix (Fin m) (Fin m) ℂ) (i j : Fin m) :
    (y *ᵥ Formalism.QuantumDeterminants.bvec j) i = y i j := by
  simp [Formalism.QuantumDeterminants.bvec, Matrix.mulVec, dotProduct, Pi.single_apply]

theorem col_std {m : ℕ} {y : Matrix (Fin m) (Fin m) ℂ} {j : Fin m}
    (h : y *ᵥ Formalism.QuantumDeterminants.bvec j = Formalism.QuantumDeterminants.bvec j) (i : Fin m) : y i j = if i = j then 1 else 0 := by
  have h' := congrFun h i
  rw [mulVec_bvec_apply'] at h'
  rw [h']
  simp [Formalism.QuantumDeterminants.bvec, Pi.single_apply]

theorem mulVec_fix_of_supp {m : ℕ} (y : Matrix (Fin m) (Fin m) ℂ) (v : Fin m → ℂ)
    (h : ∀ j, v j ≠ 0 → ∀ i, y i j = if i = j then 1 else 0) : y *ᵥ v = v := by
  first | exact UpperTheory.Reformulated.B.Qi20.mulVec_fix_of_supp .. | (apply UpperTheory.Reformulated.B.Qi20.mulVec_fix_of_supp <;> assumption) | (intros; apply UpperTheory.Reformulated.B.Qi20.mulVec_fix_of_supp <;> assumption) | (apply @UpperTheory.Reformulated.B.Qi20.mulVec_fix_of_supp <;> assumption) | (intros; apply @UpperTheory.Reformulated.B.Qi20.mulVec_fix_of_supp <;> assumption) | (apply @UpperTheory.Reformulated.B.Qi20.mulVec_fix_of_supp <;> first | assumption | infer_instance)

theorem sum_blk {k r : ℕ} (f : Fin (2 * r + k + 1) → ℂ)
    (hf : ∀ l : Fin (2 * r + k + 1), ¬(r ≤ l.val ∧ l.val < r + k) → f l = 0) :
    ∑ l, f l = ∑ c : Fin k, f ⟨r + c.val, by omega⟩ := by
  let e : Fin k ↪ Fin (2 * r + k + 1) :=
    ⟨fun c => ⟨r + c.val, by omega⟩, fun a b h => Fin.ext (by
      have h' := congrArg Fin.val h
      dsimp only at h'
      omega)⟩
  have hm : (∑ c : Fin k, f ⟨r + c.val, by omega⟩) = ∑ l ∈ Finset.univ.map e, f l := by
    rw [Finset.sum_map]
    rfl
  rw [hm]
  refine (Finset.sum_subset (Finset.subset_univ _) ?_).symm
  intro l _ hl
  apply hf
  rintro ⟨h1, h2⟩
  apply hl
  rw [Finset.mem_map]
  exact ⟨⟨l.val - r, by omega⟩, Finset.mem_univ _, Fin.ext (by show r + (l.val - r) = l.val; omega)⟩

theorem Hpk_apply_blk_out {k r : ℕ} {m i : Fin (2 * r + k + 1)} (hm : r ≤ m.val ∧ m.val < r + k)
    (hi : ¬(r ≤ i.val ∧ i.val < r + k)) : Formalism.QuantumDeterminants.Hpk k r m i = 0 := by
  have c1 : ¬(m.val < r ∧ m.val + i.val = 2 * r + k) := by omega
  have c2 : ¬(i.val < r ∧ m.val + i.val = 2 * r + k) := by omega
  have c3 : ¬(r ≤ m.val ∧ m.val ≤ r + k ∧ m = i) := by
    rintro ⟨-, -, rfl⟩
    exact hi hm
  simp only [Formalism.QuantumDeterminants.Hpk]
  rw [if_neg c1, if_neg c2, if_neg c3]

theorem Hpk_apply_blk_row {k r : ℕ} {m l : Fin (2 * r + k + 1)} (hm : r ≤ m.val ∧ m.val < r + k) :
    Formalism.QuantumDeterminants.Hpk k r m l = if m = l then 1 else 0 := by
  have hl := l.isLt
  have c1 : ¬(m.val < r ∧ m.val + l.val = 2 * r + k) := by omega
  have c2 : ¬(l.val < r ∧ m.val + l.val = 2 * r + k) := by omega
  simp only [Formalism.QuantumDeterminants.Hpk]
  rw [if_neg c1, if_neg c2]
  by_cases h : m = l
  · have c3 : r ≤ m.val ∧ m.val ≤ r + k ∧ m = l := ⟨hm.1, by omega, h⟩
    have c4 : ¬(m.val = r + k) := by omega
    rw [if_pos c3, if_neg c4, if_pos h]
  · have c3 : ¬(r ≤ m.val ∧ m.val ≤ r + k ∧ m = l) := fun h' => h h'.2.2
    rw [if_neg c3, if_neg h]

theorem std_out {k r : ℕ} {y : Mat k r} (hy : y ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r))
    (hfix : ∀ j : Fin (2 * r + k + 1), ¬(r ≤ j.val ∧ j.val < r + k) → y *ᵥ Formalism.QuantumDeterminants.bvec j = Formalism.QuantumDeterminants.bvec j) :
    (∀ j : Fin (2 * r + k + 1), ¬(r ≤ j.val ∧ j.val < r + k) → ∀ i, y i j = if i = j then 1 else 0) ∧
      ∀ i : Fin (2 * r + k + 1), ¬(r ≤ i.val ∧ i.val < r + k) → ∀ j, y i j = if i = j then 1 else 0 := by
  have hcol : ∀ j : Fin (2 * r + k + 1), ¬(r ≤ j.val ∧ j.val < r + k) → ∀ i, y i j = if i = j then 1 else 0 :=
    fun j hj i => col_std (hfix j hj) i
  refine ⟨hcol, ?_⟩
  intro i hi j
  have hy' : yᴴ * Formalism.QuantumDeterminants.Hpk k r * y = Formalism.QuantumDeterminants.Hpk k r := hy
  set v := Formalism.QuantumDeterminants.Hpk k r *ᵥ Formalism.QuantumDeterminants.bvec i with hv
  have hyv : y *ᵥ v = v := by
    refine mulVec_fix_of_supp y v fun m hm => hcol m ?_
    intro hmB
    apply hm
    rw [hv, mulVec_bvec_apply']
    exact Hpk_apply_blk_out hmB hi
  have h2 : yᴴ *ᵥ (Formalism.QuantumDeterminants.Hpk k r *ᵥ v) = Formalism.QuantumDeterminants.Hpk k r *ᵥ v := by
    calc yᴴ *ᵥ (Formalism.QuantumDeterminants.Hpk k r *ᵥ v) = yᴴ *ᵥ (Formalism.QuantumDeterminants.Hpk k r *ᵥ (y *ᵥ v)) := by rw [hyv]
      _ = (yᴴ * Formalism.QuantumDeterminants.Hpk k r * y) *ᵥ v := by rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
      _ = _ := by rw [hy']
  have hHH : Formalism.QuantumDeterminants.Hpk k r *ᵥ v = Formalism.QuantumDeterminants.bvec i := by
    rw [hv]
    exact ReciprocityTheory.ChartRestriction.DS.Xi.StepA.Hpk_mulVec_mulVec k r _
  rw [hHH] at h2
  have h3 := col_std h2 j
  rw [Matrix.conjTranspose_apply] at h3
  have h4 := congrArg star h3
  rw [star_star] at h4
  rw [h4]
  by_cases hij : i = j
  · rw [if_pos hij.symm, if_pos hij, star_one]
  · rw [if_neg (Ne.symm hij), if_neg hij, star_zero]

theorem eq_blockW {k r : ℕ} {y : Mat k r}
    (hcol : ∀ j : Fin (2 * r + k + 1), ¬(r ≤ j.val ∧ j.val < r + k) → ∀ i, y i j = if i = j then 1 else 0)
    (hrow : ∀ i : Fin (2 * r + k + 1), ¬(r ≤ i.val ∧ i.val < r + k) → ∀ j, y i j = if i = j then 1 else 0) :
    y = Formalism.MainNotions.S.blockW k r (blkW k r y) := by
  ext i j
  by_cases hi : r ≤ i.val ∧ i.val < r + k
  · by_cases hj : r ≤ j.val ∧ j.val < r + k
    · simp only [Formalism.MainNotions.S.blockW, dif_pos hi, dif_pos hj, blkW]
      congr 1 <;> apply Fin.ext <;> simp <;> omega
    · simp only [Formalism.MainNotions.S.blockW, dif_pos hi, dif_neg hj]
      rw [hcol j hj i, if_neg]
      rintro rfl
      exact hj hi
  · simp only [Formalism.MainNotions.S.blockW, dif_neg hi]
    exact hrow i hi j

theorem blkW_mul {k r : ℕ} (y₁ y₂ : Mat k r)
    (hrow : ∀ i : Fin (2 * r + k + 1), ¬(r ≤ i.val ∧ i.val < r + k) → ∀ j, y₂ i j = if i = j then 1 else 0) :
    blkW k r (y₁ * y₂) = blkW k r y₁ * blkW k r y₂ := by
  ext a b
  simp only [blkW, Matrix.mul_apply]
  rw [sum_blk]
  intro l hl
  rw [hrow l hl, if_neg, mul_zero]
  intro h
  apply hl
  rw [h]
  exact ⟨by simp, by simp⟩

theorem blkW_one {k r : ℕ} : blkW k r (1 : Mat k r) = 1 := by
  ext a b
  simp only [blkW, Matrix.one_apply, Fin.mk.injEq, Nat.add_left_cancel_iff, Fin.val_inj]

theorem blkW_unitary {k r : ℕ} {y : Mat k r} (hy : y ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r))
    (hrow : ∀ i : Fin (2 * r + k + 1), ¬(r ≤ i.val ∧ i.val < r + k) → ∀ j, y i j = if i = j then 1 else 0) :
    (blkW k r y)ᴴ * blkW k r y = 1 := by
  have hy' : yᴴ * Formalism.QuantumDeterminants.Hpk k r * y = Formalism.QuantumDeterminants.Hpk k r := hy
  have hrow0 : ∀ (l i : Fin (2 * r + k + 1)), ¬(r ≤ l.val ∧ l.val < r + k) → (r ≤ i.val ∧ i.val < r + k) →
      y l i = 0 := by
    intro l i hl hi
    rw [hrow l hl i, if_neg]
    rintro rfl
    exact hl hi
  have hrowH : ∀ i m : Fin (2 * r + k + 1), (r ≤ i.val ∧ i.val < r + k) →
      (yᴴ * Formalism.QuantumDeterminants.Hpk k r) i m = star (y m i) := by
    intro i m hi
    rw [Matrix.mul_apply, Finset.sum_eq_single m]
    · rw [Matrix.conjTranspose_apply]
      by_cases hm : r ≤ m.val ∧ m.val < r + k
      · rw [Hpk_apply_blk_row hm, if_pos rfl, mul_one]
      · rw [hrow0 m i hm hi, star_zero, zero_mul]
    · intro l _ hlm
      rw [Matrix.conjTranspose_apply]
      by_cases hl : r ≤ l.val ∧ l.val < r + k
      · rw [Hpk_apply_blk_row hl, if_neg hlm, mul_zero]
      · rw [hrow0 l i hl hi, star_zero, zero_mul]
    · intro h
      exact absurd (Finset.mem_univ m) h
  ext a b
  have hA : r ≤ r + a.val ∧ r + a.val < r + k := ⟨by omega, by omega⟩
  have hB : r ≤ r + b.val ∧ r + b.val < r + k := ⟨by omega, by omega⟩
  have e := congrFun (congrFun hy' ⟨r + a.val, by omega⟩) ⟨r + b.val, by omega⟩
  rw [Hpk_apply_blk_row hA, Matrix.mul_apply] at e
  have hr' : ∀ m : Fin (2 * r + k + 1),
      (yᴴ * Formalism.QuantumDeterminants.Hpk k r) ⟨r + a.val, by omega⟩ m = star (y m ⟨r + a.val, by omega⟩) :=
    fun m => hrowH _ m hA
  simp only [hr'] at e
  rw [sum_blk] at e
  · rw [Matrix.mul_apply, Matrix.one_apply]
    simp only [Matrix.conjTranspose_apply, blkW]
    rw [e]
    simp only [Fin.mk.injEq, Nat.add_left_cancel_iff, Fin.val_inj]
  · intro l hl
    rw [hrow0 l ⟨r + b.val, by omega⟩ hl hB, mul_zero]

theorem jm_allPos (k : ℕ) : Formalism.REAL.Jm (Formalism.MainNotions.S.allPos k) = 1 := by
  ext a b
  simp [Formalism.REAL.Jm, Formalism.MainNotions.S.allPos, Matrix.diagonal_apply, Matrix.one_apply]

theorem conj_facts {k r : ℕ} {z : Fin (2 * r + k + 1) → ℂ} (hT : 0 < Formalism.QuantumDeterminants.Tz k r z) {g : Mat k r}
    (hg : Formalism.MainNotions.S.IsFrameW k r z g) {x : Mat k r} (hx : x ∈ Formalism.QuantumDeterminants.UWset k r z) :
    g⁻¹ * x * g ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) ∧
      ∀ j : Fin (2 * r + k + 1), ¬(r ≤ j.val ∧ j.val < r + k) →
        (g⁻¹ * x * g) *ᵥ Formalism.QuantumDeterminants.bvec j = Formalism.QuantumDeterminants.bvec j := by
  obtain ⟨hgH, hgE, hgZ⟩ := hg
  obtain ⟨hxH, hxE, hxZ⟩ := hx
  refine ⟨mul_mem_UH' (mul_mem_UH' (inv_mem_UH' hgH) hxH) hgH, ?_⟩
  have hginv : ∀ v, g *ᵥ v = v → g⁻¹ *ᵥ v = v := by
    intro v hv
    calc g⁻¹ *ᵥ v = g⁻¹ *ᵥ (g *ᵥ v) := by rw [hv]
      _ = v := by rw [Matrix.mulVec_mulVec, ReciprocityTheory.ChartRestriction.DS.Xi.StepA.UH_inv_mul k r hgH, Matrix.one_mulVec]
  have hfix : ∀ v, g *ᵥ v = v → x *ᵥ v = v → (g⁻¹ * x * g) *ᵥ v = v := by
    intro v hg1 hx1
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hg1, hx1, hginv v hg1]
  intro j hj
  have hjl := j.isLt
  by_cases h1 : j.val < r
  · have ej : j = Formalism.QuantumDeterminants.eI k r ⟨j.val, h1⟩ := Fin.ext rfl
    rw [ej]
    exact hfix _ (hgE _).1 (hxE _).1
  · by_cases h2 : j.val = r + k
    · have ej : j = Formalism.QuantumDeterminants.wI k r (Fin.last k) := Fin.ext (by simp [Formalism.QuantumDeterminants.wI]; omega)
      rw [ej]
      set t : ℂ := ((Real.sqrt (Formalism.QuantumDeterminants.Tz k r z) : ℝ) : ℂ) with ht
      have ht0 : t ≠ 0 := by
        rw [ht]
        exact_mod_cast (Real.sqrt_pos.2 hT).ne'
      have hz' : g⁻¹ *ᵥ z = t • Formalism.QuantumDeterminants.bvec (Formalism.QuantumDeterminants.wI k r (Fin.last k)) := by
        rw [← hgZ, Matrix.mulVec_mulVec, ReciprocityTheory.ChartRestriction.DS.Xi.StepA.UH_inv_mul k r hgH, Matrix.one_mulVec]
      have hm : t • ((g⁻¹ * x * g) *ᵥ Formalism.QuantumDeterminants.bvec (Formalism.QuantumDeterminants.wI k r (Fin.last k))) =
          t • Formalism.QuantumDeterminants.bvec (Formalism.QuantumDeterminants.wI k r (Fin.last k)) := by
        rw [← Matrix.mulVec_smul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hgZ, hxZ, hz']
      exact smul_right_injective _ ht0 hm
    · have ej : j = Formalism.QuantumDeterminants.esI k r ⟨2 * r + k - j.val, by omega⟩ :=
        Fin.ext (by simp [Formalism.QuantumDeterminants.esI]; omega)
      rw [ej]
      exact hfix _ (hgE _).2 (hxE _).2

theorem mem_UWset_mul {k r : ℕ} {z : Fin (2 * r + k + 1) → ℂ} {a b : Mat k r}
    (ha : a ∈ Formalism.QuantumDeterminants.UWset k r z) (hb : b ∈ Formalism.QuantumDeterminants.UWset k r z) : a * b ∈ Formalism.QuantumDeterminants.UWset k r z := by
  obtain ⟨haH, haE, haZ⟩ := ha
  obtain ⟨hbH, hbE, hbZ⟩ := hb
  refine ⟨mul_mem_UH' haH hbH, fun c => ⟨?_, ?_⟩, ?_⟩
  · rw [← Matrix.mulVec_mulVec, (hbE c).1, (haE c).1]
  · rw [← Matrix.mulVec_mulVec, (hbE c).2, (haE c).2]
  · rw [← Matrix.mulVec_mulVec, hbZ, haZ]

theorem continuous_blkW_conj {k r : ℕ} (g : Mat k r) : Continuous fun x : Mat k r => blkW k r (g⁻¹ * x * g) := by
  have hc : Continuous fun x : Mat k r => g⁻¹ * x * g :=
    (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
  exact continuous_matrix fun a b => hc.matrix_elem _ _

theorem hcTypeW_uRep : HCTypeWURepStatement := by
  intro k r z u Vp _ _ π hz hT hπ
  obtain ⟨g, hg, hρ⟩ := hπ
  have hgH : g ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) := hg.1
  obtain ⟨hρC, hρI, hρc⟩ := hρ.2.2.1
  have key : ∀ x ∈ Formalism.QuantumDeterminants.UWset k r z,
      blkW k r (g⁻¹ * x * g) ∈ Formalism.MainNotions.S.UJset (Formalism.MainNotions.S.allPos k) ∧
        π x = π (g * Formalism.MainNotions.S.blockW k r (blkW k r (g⁻¹ * x * g)) * g⁻¹) ∧
        ∀ i : Fin (2 * r + k + 1), ¬(r ≤ i.val ∧ i.val < r + k) → ∀ j,
          (g⁻¹ * x * g) i j = if i = j then 1 else 0 := by
    intro x hx
    obtain ⟨hyH, hfix⟩ := conj_facts hT hg hx
    obtain ⟨hcol, hrow⟩ := std_out hyH hfix
    refine ⟨?_, ?_, hrow⟩
    · show Formalism.REAL.inUJ (Formalism.MainNotions.S.allPos k) (blkW k r (g⁻¹ * x * g))
      unfold Formalism.REAL.inUJ
      rw [jm_allPos, Matrix.mul_one, blkW_unitary hyH hrow]
    · rw [← eq_blockW hcol hrow]
      congr 1
      simp only [Matrix.mul_assoc]
      rw [ReciprocityTheory.ChartRestriction.DS.Xi.StepA.UH_mul_inv k r hgH, Matrix.mul_one, ← Matrix.mul_assoc,
        ReciprocityTheory.ChartRestriction.DS.Xi.StepA.UH_mul_inv k r hgH, Matrix.one_mul]
  have h1mem : (1 : Mat k r) ∈ Formalism.QuantumDeterminants.UWset k r z := by
    refine ⟨?_, fun a => ⟨Matrix.one_mulVec _, Matrix.one_mulVec _⟩, Matrix.one_mulVec _⟩
    show (1 : Mat k r)ᴴ * Formalism.QuantumDeterminants.Hpk k r * 1 = Formalism.QuantumDeterminants.Hpk k r
    simp
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · rw [(key 1 h1mem).2.1]
    have e1 : g⁻¹ * (1 : Mat k r) * g = 1 := by
      rw [Matrix.mul_one, ReciprocityTheory.ChartRestriction.DS.Xi.StepA.UH_inv_mul k r hgH]
    rw [e1, blkW_one]
    exact hρC.1
  · intro a ha b hb
    have hab := mem_UWset_mul ha hb
    rw [(key _ hab).2.1, (key a ha).2.1, (key b hb).2.1]
    have e : g⁻¹ * (a * b) * g = (g⁻¹ * a * g) * (g⁻¹ * b * g) := by
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc g g⁻¹, ReciprocityTheory.ChartRestriction.DS.Xi.StepA.UH_mul_inv k r hgH, Matrix.one_mul]
    rw [e, blkW_mul _ _ (key b hb).2.2]
    exact hρC.2 _ (key a ha).1 _ (key b hb).1
  · intro x hx v
    rw [(key x hx).2.1]
    exact hρI _ (key x hx).1 v
  · intro v
    have hc : ContinuousOn
        ((fun h => π (g * Formalism.MainNotions.S.blockW k r h * g⁻¹) v) ∘ fun x : Mat k r => blkW k r (g⁻¹ * x * g))
        (Formalism.QuantumDeterminants.UWset k r z) :=
      (hρc v).comp (continuous_blkW_conj g).continuousOn fun x hx => (key x hx).1
    refine hc.congr fun x hx => ?_
    simp only [Function.comp]
    rw [← (key x hx).2.1]

end ReciprocityTheory.ChartRestriction.DS.Lap
