import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FourierMatch
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConjTransposeVecMulVecSelf
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsCompactIntMatrix

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

noncomputable section

namespace GlobalTheory.JR.UnitChar

section Alg
variable {r : ℕ} {E : Type} [NontriviallyNormedField E] [StarRing E]

def BddPow (g : unitaryGroup (Fin r) E) : Prop :=
  ∃ B : ℝ, ∀ n : ℕ, ∀ i j, ‖((g ^ n : unitaryGroup (Fin r) E) : Matrix (Fin r) (Fin r) E) i j‖ ≤ B

theorem pow_one_sub_smul [IsUltrametricDist E] (P : Matrix (Fin r) (Fin r) E) (c s : E) (hP : P * P = s • P)
    (hζ : ‖1 - c * s‖ ≤ 1) (n : ℕ) : ∃ b : E, (1 - c • P) ^ n = 1 - b • P ∧ ‖b‖ ≤ ‖c‖ := by
  induction n with
  | zero => exact ⟨0, by simp, by simp⟩
  | succ n ih =>
    obtain ⟨b, hb, hbn⟩ := ih
    refine ⟨b * (1 - c * s) + c, ?_, ?_⟩
    · rw [pow_succ, hb, sub_mul, mul_sub, mul_sub, one_mul, mul_one, one_mul, smul_mul_smul_comm, hP, smul_smul]
      simp only [mul_sub, mul_one, add_smul, sub_smul, mul_smul]
      abel
    · calc ‖b * (1 - c * s) + c‖ ≤ max ‖b * (1 - c * s)‖ ‖c‖ := IsUltrametricDist.norm_add_le_max _ _
        _ ≤ ‖c‖ := by
          refine max_le ?_ le_rfl
          rw [norm_mul]
          calc ‖b‖ * ‖1 - c * s‖ ≤ ‖b‖ * 1 := mul_le_mul_of_nonneg_left hζ (norm_nonneg _)
            _ ≤ ‖c‖ := by rw [mul_one]; exact hbn

theorem bddPow_of_eq [IsUltrametricDist E] (g : unitaryGroup (Fin r) E) (P : Matrix (Fin r) (Fin r) E) (c s : E)
    (hP : P * P = s • P) (hζ : ‖1 - c * s‖ ≤ 1) (hg : (g : Matrix (Fin r) (Fin r) E) = 1 - c • P) : BddPow g := by
  refine ⟨1 + ‖c‖ * ∑ i, ∑ j, ‖P i j‖, fun n i j => ?_⟩
  obtain ⟨b, hb, hbn⟩ := pow_one_sub_smul P c s hP hζ n
  have hP1 : ‖P i j‖ ≤ ∑ i, ∑ j, ‖P i j‖ :=
    (Finset.single_le_sum (f := fun j => ‖P i j‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ j)).trans
      (Finset.single_le_sum (f := fun i => ∑ j, ‖P i j‖)
        (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ i))
  have h1 : ‖(1 : Matrix (Fin r) (Fin r) E) i j‖ ≤ 1 := by
    rw [Matrix.one_apply]; split_ifs <;> simp
  rw [SubmonoidClass.coe_pow, hg, hb, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  calc ‖(1 : Matrix (Fin r) (Fin r) E) i j - b * P i j‖ ≤ ‖(1 : Matrix (Fin r) (Fin r) E) i j‖ + ‖b * P i j‖ :=
        norm_sub_le _ _
    _ ≤ 1 + ‖c‖ * ∑ i, ∑ j, ‖P i j‖ := by
        rw [norm_mul]
        exact add_le_add h1 ((mul_le_mul_of_nonneg_right hbn (norm_nonneg _)).trans
            (mul_le_mul_of_nonneg_left hP1 (norm_nonneg _)))

def refl (w : Fin r → E) (a : E) (ha : a ≠ 0) (hN : star w ⬝ᵥ w = a + star a) : unitaryGroup (Fin r) E :=
  ⟨1 - a⁻¹ • vecMulVec w (star w), GlobalTheory.UnitWitt.refl_mem w a ha hN⟩

theorem bddPow_refl [IsUltrametricDist E] (hstar : ∀ y : E, ‖star y‖ = ‖y‖) (w : Fin r → E) (a : E) (ha : a ≠ 0)
    (hN : star w ⬝ᵥ w = a + star a) : BddPow (refl w a ha hN) := by
  refine bddPow_of_eq _ (vecMulVec w (star w)) a⁻¹ (a + star a) ?_ ?_ rfl
  · rw [GlobalTheory.UnitWitt.vecMulVec_self_mul, hN]
  · have : 1 - a⁻¹ * (a + star a) = -(star a / a) := by field_simp; ring
    rw [this, norm_neg, norm_div, hstar, div_self (norm_ne_zero_iff.2 ha)]

theorem refl_mulVec (w : Fin r → E) (a : E) (ha : a ≠ 0) (hN : star w ⬝ᵥ w = a + star a) (u : Fin r → E) :
    ((refl w a ha hN : unitaryGroup (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ u = u - (a⁻¹ * (star w ⬝ᵥ u)) • w := by
  show (1 - a⁻¹ • vecMulVec w (star w)) *ᵥ u = _
  have h1 : (a⁻¹ • vecMulVec w (star w)) *ᵥ u = a⁻¹ • (vecMulVec w (star w) *ᵥ u) := by
    ext i; simp [mulVec, dotProduct, Finset.mul_sum, mul_assoc]
  rw [sub_mulVec, one_mulVec, h1, GlobalTheory.UnitWitt.vecMulVec_mulVec_eq, smul_smul]

def col (g : Matrix (Fin r) (Fin r) E) (i : Fin r) : Fin r → E := fun l => g l i

theorem col_mul (A B : Matrix (Fin r) (Fin r) E) (i : Fin r) : col (A * B) i = A *ᵥ col B i := by
  ext j; rfl

theorem col_orth (g : unitaryGroup (Fin r) E) (i k : Fin r) :
    star (col (g : Matrix (Fin r) (Fin r) E) i) ⬝ᵥ col (g : Matrix (Fin r) (Fin r) E) k =
      (1 : Matrix (Fin r) (Fin r) E) i k := by
  have h := congrFun (congrFun (mem_unitaryGroup_iff'.1 g.2) i) k
  rw [← h]
  simp [Matrix.mul_apply, dotProduct, col, Matrix.star_apply]

def StdFrom (m : ℕ) (g : unitaryGroup (Fin r) E) : Prop :=
  ∀ i : Fin r, m ≤ (i : ℕ) → col (g : Matrix (Fin r) (Fin r) E) i = Pi.single i 1

theorem entry_zero_of_col (g : unitaryGroup (Fin r) E) {i k : Fin r} (hik : i ≠ k)
    (hi : col (g : Matrix (Fin r) (Fin r) E) i = Pi.single i 1) : (g : Matrix (Fin r) (Fin r) E) i k = 0 := by
  have h := col_orth g i k
  rw [hi, Matrix.one_apply_ne hik] at h
  simpa [col] using h

end Alg

section Gen
variable {r : ℕ} {E : Type} [NontriviallyNormedField E] [StarRing E]

theorem star_single_one (k : Fin r) : star (Pi.single k (1 : E) : Fin r → E) = Pi.single k 1 := by
  ext j; by_cases h : j = k <;> simp [Pi.single_apply, h]

theorem bddPow_one : BddPow (1 : unitaryGroup (Fin r) E) := by
  refine ⟨1, fun n i j => ?_⟩
  rw [one_pow, OneMemClass.coe_one, Matrix.one_apply]; split_ifs <;> simp

theorem exists_sign [IsUltrametricDist E] (hstar : ∀ y : E, ‖star y‖ = ‖y‖) (h2 : (2 : E) ≠ 0)
    (g : unitaryGroup (Fin r) E) (k : Fin r)
    (hg : ∀ i : Fin r, k < i → col (g : Matrix (Fin r) (Fin r) E) i = Pi.single i 1) :
    ∃ D : unitaryGroup (Fin r) E, BddPow D ∧
      (∀ i : Fin r, k < i → col ((D * g : unitaryGroup (Fin r) E) : Matrix (Fin r) (Fin r) E) i = Pi.single i 1) ∧
      ((D * g : unitaryGroup (Fin r) E) : Matrix (Fin r) (Fin r) E) k k ≠ 1 := by
  by_cases hk : (g : Matrix (Fin r) (Fin r) E) k k = 1
  · have hN : star (Pi.single k (1 : E)) ⬝ᵥ Pi.single k 1 = (2 : E)⁻¹ + star (2 : E)⁻¹ := by
      rw [star_single_one, star_inv₀, star_ofNat, dotProduct_single, Pi.single_eq_same, mul_one, ← two_mul,
        mul_inv_cancel₀ h2]
    refine ⟨refl (Pi.single k 1) 2⁻¹ (inv_ne_zero h2) hN, bddPow_refl hstar _ _ _ _, ?_, ?_⟩
    · intro i hi
      rw [MulMemClass.coe_mul, col_mul, refl_mulVec, hg i hi, star_single_one, dotProduct_single,
        Pi.single_apply, if_neg (ne_of_gt hi), zero_mul, mul_zero, zero_smul, sub_zero]
    · have h := congrFun (col_mul (refl (Pi.single k (1 : E)) 2⁻¹ (inv_ne_zero h2) hN : Matrix (Fin r) (Fin r) E)
        (g : Matrix (Fin r) (Fin r) E) k) k
      rw [refl_mulVec, star_single_one, single_dotProduct] at h
      rw [MulMemClass.coe_mul]
      change col _ k k ≠ 1
      rw [h]
      simp only [col, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.single_eq_same, hk, inv_inv, one_mul, mul_one]
      intro h'
      apply h2
      linear_combination -h'
  · exact ⟨1, bddPow_one, by simpa using hg, by simpa using hk⟩

theorem exists_refl [IsUltrametricDist E] (hstar : ∀ y : E, ‖star y‖ = ‖y‖)
    (g : unitaryGroup (Fin r) E) (k : Fin r)
    (hg : ∀ i : Fin r, k < i → col (g : Matrix (Fin r) (Fin r) E) i = Pi.single i 1)
    (hk : (g : Matrix (Fin r) (Fin r) E) k k ≠ 1) :
    ∃ R : unitaryGroup (Fin r) E, BddPow R ∧
      ∀ i : Fin r, k ≤ i → col ((R * g : unitaryGroup (Fin r) E) : Matrix (Fin r) (Fin r) E) i = Pi.single i 1 := by
  set w := col (g : Matrix (Fin r) (Fin r) E) k with hw
  have hww : star w ⬝ᵥ w = 1 := by rw [hw, col_orth, Matrix.one_apply_eq]
  have hwk : w k = (g : Matrix (Fin r) (Fin r) E) k k := rfl
  have hwi : ∀ i, k < i → w i = 0 := fun i hi => entry_zero_of_col g (ne_of_gt hi) (hg i hi)
  set v := w - Pi.single k 1 with hv
  set a := 1 - w k with ha_def
  have ha : a ≠ 0 := sub_ne_zero.2 (by rw [hwk]; exact Ne.symm hk)
  have hvw : star v ⬝ᵥ w = a := by
    rw [hv, star_sub, sub_dotProduct, hww, star_single_one, single_dotProduct, one_mul]
  have hN : star v ⬝ᵥ v = a + star a := by
    rw [dotProduct_sub, hvw, star_sub, sub_dotProduct, star_single_one, single_dotProduct, dotProduct_single,
      Pi.single_eq_same, Pi.star_apply, ha_def, star_sub, star_one]
    try simp only [Pi.sub_apply, Pi.single_eq_same, Pi.star_apply, star_sub, star_one]
    ring
  refine ⟨refl v a ha hN, bddPow_refl hstar _ _ _ _, fun i hi => ?_⟩
  rcases eq_or_lt_of_le hi with h | h
  · subst h
    rw [MulMemClass.coe_mul, col_mul, refl_mulVec, ← hw, hvw, inv_mul_cancel₀ ha, one_smul, hv, sub_sub_cancel]
  · rw [MulMemClass.coe_mul, col_mul, refl_mulVec, hg i h, dotProduct_single, mul_one]
    have : v i = 0 := by rw [hv, Pi.sub_apply, hwi i h, Pi.single_apply, if_neg (ne_of_gt h), sub_zero]
    rw [Pi.star_apply, this, star_zero, mul_zero, zero_smul, sub_zero]

theorem hom_eq_one_of_bddPow [IsUltrametricDist E] (hstar : ∀ y : E, ‖star y‖ = ‖y‖) (h2 : (2 : E) ≠ 0)
    {M : Type} [Monoid M] (φ : unitaryGroup (Fin r) E →* M) (hφ : ∀ g, BddPow g → φ g = 1)
    (g : unitaryGroup (Fin r) E) : φ g = 1 := by
  have key : ∀ m : ℕ, ∀ g : unitaryGroup (Fin r) E, StdFrom m g → φ g = 1 := by
    intro m
    induction m with
    | zero =>
      intro g hg
      have : g = 1 := by
        apply Subtype.ext
        ext j i
        have := congrFun (hg i (Nat.zero_le _)) j
        simpa [col, Matrix.one_apply, Pi.single_apply] using this
      rw [this, map_one]
    | succ m ih =>
      intro g hg
      by_cases hm : m < r
      · let k : Fin r := ⟨m, hm⟩
        have hg' : ∀ i : Fin r, k < i → col (g : Matrix (Fin r) (Fin r) E) i = Pi.single i 1 :=
          fun i hi => hg i (Fin.lt_def.1 hi)
        obtain ⟨D, hD, hDg, hDk⟩ := exists_sign hstar h2 g k hg'
        obtain ⟨R, hR, hRg⟩ := exists_refl hstar (D * g) k hDg hDk
        have h1 : φ (R * (D * g)) = 1 := ih _ fun i hi => hRg i (Fin.le_def.2 hi)
        rw [map_mul, map_mul, hφ R hR, hφ D hD, one_mul, one_mul] at h1
        exact h1
      · exact ih g fun i hi => absurd i.isLt (by omega)
  exact key r g fun i hi => absurd i.isLt (by omega)

end Gen

section Top

theorem real_eq_one {x y C : ℝ} (hx : 0 < x) (hy : 0 < y) (hxy : x * y = 1) (hxn : ∀ n : ℕ, x ^ n ≤ C)
    (hyn : ∀ n : ℕ, y ^ n ≤ C) : x = 1 := by
  have le1 : ∀ z : ℝ, (∀ n : ℕ, z ^ n ≤ C) → z ≤ 1 := by
    intro z h
    by_contra hlt
    push_neg at hlt
    obtain ⟨n, hn⟩ := ((tendsto_pow_atTop_atTop_of_one_lt hlt).eventually_gt_atTop C).exists
    exact absurd (h n) (not_le.2 hn)
  have hx1 := le1 x hxn
  have hy1 := le1 y hyn
  nlinarith

variable {E : Type} [NontriviallyNormedField E] [StarRing E]

theorem two_ne_zero_of_unram {F : Type} [NontriviallyNormedField F] [NormedAlgebra F E] [hU : Unram F E] :
    (2 : E) ≠ 0 := by
  haveI : CharZero F := hU.charZero
  intro h
  apply (two_ne_zero : (2 : F) ≠ 0)
  apply (algebraMap F E).injective
  rw [map_ofNat, map_zero]; exact h

theorem isCompact_bdd (r : ℕ) [ContinuousStar E] [ProperSpace E] (B : ℝ) :
    IsCompact {h : unitaryGroup (Fin r) E | ∀ i j, ‖(h : Matrix (Fin r) (Fin r) E) i j‖ ≤ B} := by
  have hc : IsCompact {A : Matrix (Fin r) (Fin r) E | ∀ i j, ‖A i j‖ ≤ B} := by
    have h : IsCompact (Set.pi Set.univ fun _ : Fin r => Set.pi Set.univ fun _ : Fin r =>
        Metric.closedBall (0 : E) B) :=
      isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall _ _
    have e : {A : Matrix (Fin r) (Fin r) E | ∀ i j, ‖A i j‖ ≤ B} = (Set.pi Set.univ fun _ : Fin r =>
        Set.pi Set.univ fun _ : Fin r => Metric.closedBall (0 : E) B) := by
      ext A
      exact ⟨fun H i _ j _ => mem_closedBall_zero_iff.2 (H i j),
        fun H i j => mem_closedBall_zero_iff.1 (H i trivial j trivial)⟩
    rw [e]; exact h
  exact (isClosed_unitary (R := Matrix (Fin r) (Fin r) E)).isClosedEmbedding_subtypeVal.isCompact_preimage hc

theorem bddPow_inv {r : ℕ} (hstar : ∀ y : E, ‖star y‖ = ‖y‖) {g : unitaryGroup (Fin r) E} (hg : BddPow g) :
    BddPow g⁻¹ := by
  obtain ⟨B, hB⟩ := hg
  refine ⟨B, fun n i j => ?_⟩
  rw [inv_pow]
  change ‖(star ((g ^ n : unitaryGroup (Fin r) E) : Matrix (Fin r) (Fin r) E)) i j‖ ≤ B
  rw [Matrix.star_apply, hstar]
  exact hB n j i

variable {F : Type} [NontriviallyNormedField F] [NormedAlgebra F E]

theorem char_eq_one [hU : Unram F E] (r : ℕ) (ch : unitaryGroup (Fin r) E →* ℝ) (hc : Continuous ch)
    (hpos : ∀ g, 0 < ch g) (g : unitaryGroup (Fin r) E) : ch g = 1 := by
  haveI := hU.ultraE
  haveI := hU.lcE
  haveI : ProperSpace E := ProperSpace.of_locallyCompactSpace E
  haveI : NormedStarGroup E := ⟨fun y => (hU.norm_star y).le⟩
  refine hom_eq_one_of_bddPow hU.norm_star (two_ne_zero_of_unram (F := F)) ch (fun g hg => ?_) g
  obtain ⟨B, hB⟩ := hg
  obtain ⟨B', hB'⟩ := bddPow_inv hU.norm_star ⟨B, hB⟩
  obtain ⟨T, hT⟩ := (isCompact_bdd r (max B B')).exists_bound_of_continuousOn hc.continuousOn
  have hxy : ch g * ch g⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
  refine real_eq_one (hpos g) (hpos g⁻¹) hxy (C := T) (fun n => ?_) (fun n => ?_)
  · rw [← map_pow]
    exact (le_abs_self _).trans ((Real.norm_eq_abs _) ▸ hT _ fun i j => (hB n i j).trans (le_max_left _ _))
  · rw [← map_pow]
    exact (le_abs_self _).trans ((Real.norm_eq_abs _) ▸ hT _ fun i j => (hB' n i j).trans (le_max_right _ _))

theorem isMulRightInvariant [hU : Unram F E] (r : ℕ) (M : Meas r F E) :
    letI := M.mU; M.μU.IsMulRightInvariant := by
  letI := M.mU
  haveI := M.bU
  haveI := M.haarU
  haveI := hU.ultraE
  haveI := hU.lcE
  haveI : ProperSpace E := ProperSpace.of_locallyCompactSpace E
  haveI : NormedStarGroup E := ⟨fun y => (hU.norm_star y).le⟩
  haveI : SecondCountableTopology (Matrix (Fin r) (Fin r) E) :=
    inferInstanceAs (SecondCountableTopology (Fin r → Fin r → E))
  haveI : LocallyCompactSpace (Matrix (Fin r) (Fin r) E) :=
    inferInstanceAs (LocallyCompactSpace (Fin r → Fin r → E))
  haveI : LocallyCompactSpace (unitaryGroup (Fin r) E) :=
    (isClosed_unitary (R := Matrix (Fin r) (Fin r) E)).locallyCompactSpace
  haveI : SecondCountableTopology (unitaryGroup (Fin r) E) :=
    (isClosed_unitary (R := Matrix (Fin r) (Fin r) E)).isClosedEmbedding_subtypeVal.isEmbedding.secondCountableTopology
  have hmap : ∀ g, Measure.map (· * g) M.μU = (Measure.modularCharacter g) • M.μU := fun g => by
    change _ = Measure.modularCharacterFun g • _
    rw [Measure.modularCharacterFun_eq_haarScalarFactor M.μU g]
    exact Measure.isMulLeftInvariant_eq_smul _ _
  have hK : MeasurableSet (uO r E : Set (unitaryGroup (Fin r) E)) := (MeasExist.isOpen_uO r E).measurableSet
  have hbound : ∀ C : ℝ, 0 ≤ C → ∀ h : unitaryGroup (Fin r) E,
      (∀ i j, ‖((h⁻¹ : unitaryGroup (Fin r) E) : Matrix (Fin r) (Fin r) E) i j‖ ≤ C) →
      (Measure.modularCharacter h : ENNReal) ≤
        M.μU {x | ∀ i j, ‖(x : Matrix (Fin r) (Fin r) E) i j‖ ≤ C} := by
    intro C hC h hh
    have e1 : (Measure.map (· * h) M.μU) (uO r E) = (Measure.modularCharacter h • M.μU) (uO r E) := by
      rw [hmap h]
    rw [Measure.map_apply (measurable_mul_const h) hK, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul, M.volU, mul_one] at e1
    rw [← e1]
    apply measure_mono
    intro x hx i j
    have hx' : (x : Matrix (Fin r) (Fin r) E) =
        ((x * h : unitaryGroup (Fin r) E) : Matrix (Fin r) (Fin r) E) *
          ((h⁻¹ : unitaryGroup (Fin r) E) : Matrix (Fin r) (Fin r) E) := by
      rw [← MulMemClass.coe_mul, mul_inv_cancel_right]
    rw [hx', Matrix.mul_apply]
    apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hC
    intro l _
    rw [norm_mul]
    calc _ ≤ 1 * C := mul_le_mul (hx i l) (hh l j) (norm_nonneg _) zero_le_one
      _ = C := one_mul C
  have hone : ∀ g : unitaryGroup (Fin r) E, Measure.modularCharacter g = 1 := by
    refine hom_eq_one_of_bddPow hU.norm_star (two_ne_zero_of_unram (F := F))
      (Measure.modularCharacter (G := unitaryGroup (Fin r) E)) (fun g hg => ?_)
    obtain ⟨B, hB⟩ := hg
    obtain ⟨B', hB'⟩ := bddPow_inv hU.norm_star ⟨B, hB⟩
    set C := max (max B B') 0 with hC
    have hfin : M.μU {x | ∀ i j, ‖(x : Matrix (Fin r) (Fin r) E) i j‖ ≤ C} ≠ ⊤ :=
      ((isCompact_bdd r C).measure_lt_top).ne
    set T := (M.μU {x | ∀ i j, ‖(x : Matrix (Fin r) (Fin r) E) i j‖ ≤ C}).toNNReal
    have key : ∀ h : unitaryGroup (Fin r) E,
        (∀ i j, ‖((h⁻¹ : unitaryGroup (Fin r) E) : Matrix (Fin r) (Fin r) E) i j‖ ≤ C) →
        (Measure.modularCharacter h : ℝ) ≤ T := by
      intro h hh
      have h1 := ENNReal.toNNReal_mono hfin (hbound C (le_max_right _ _) h hh)
      rw [ENNReal.toNNReal_coe] at h1
      exact_mod_cast h1
    have hxy : (Measure.modularCharacter g : ℝ) * (Measure.modularCharacter g⁻¹ : ℝ) = 1 := by
      rw [← NNReal.coe_mul, ← map_mul, mul_inv_cancel, map_one, NNReal.coe_one]
    apply NNReal.coe_injective
    rw [NNReal.coe_one]
    refine real_eq_one (Measure.modularCharacterFun_pos g) (Measure.modularCharacterFun_pos g⁻¹) hxy (C := T)
      (fun n => ?_) (fun n => ?_)
    · change ((Measure.modularCharacter g : NNReal) : ℝ) ^ n ≤ T
      rw [← NNReal.coe_pow, ← map_pow]
      refine key _ fun i j => ?_
      rw [← inv_pow]
      exact (hB' n i j).trans ((le_max_right _ _).trans (le_max_left _ _))
    · change ((Measure.modularCharacter g⁻¹ : NNReal) : ℝ) ^ n ≤ T
      rw [← NNReal.coe_pow, ← map_pow]
      refine key _ fun i j => ?_
      rw [inv_pow, inv_inv]
      exact (hB n i j).trans ((le_max_left _ _).trans (le_max_left _ _))
  exact ⟨fun g => by rw [hmap g, hone g, one_smul]⟩

end Top

theorem posChar_trivial_and_unimodular : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E]
    [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ),
    (∀ ch : Matrix.unitaryGroup (Fin r) E →* ℝ, Continuous ch → (∀ g, 0 < ch g) → ∀ g, ch g = 1) ∧
      ∀ M : Meas r F E, (letI := M.mU; M.μU.IsMulRightInvariant) := by
  intro F E _ _ _ _ _ r
  exact ⟨fun ch hc hpos g => char_eq_one (F := F) r ch hc hpos g, fun M => isMulRightInvariant r M⟩

end GlobalTheory.JR.UnitChar
