import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.PlaceCh
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.PsiInv

noncomputable section

namespace PI.AprimeInfW

open MeasureTheory Topology Filter Metric Set Formalism.MainNotions.S Formalism.MainNotions.S.Gauge
open scoped Matrix

section Coords

variable {n : ℕ}

def rlM (n : ℕ) : Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] EuclideanSpace ℝ (Fin n × Fin n × Bool) where
  toFun X := (WithLp.equiv 2 _).symm (realifyFun X)
  map_add' X Y := by
    ext p
    simp only [realifyFun, WithLp.equiv_symm_apply, PiLp.add_apply, Matrix.add_apply]
    split_ifs <;> simp
  map_smul' c X := by
    ext p
    simp only [realifyFun, WithLp.equiv_symm_apply, PiLp.smul_apply, Matrix.smul_apply, RingHom.id_apply]
    split_ifs <;> simp

def urM (n : ℕ) : EuclideanSpace ℝ (Fin n × Fin n × Bool) →ₗ[ℝ] Matrix (Fin n) (Fin n) ℂ where
  toFun x := unrealify x
  map_add' x y := by
    ext i j
    apply Complex.ext <;> simp [unrealify]
  map_smul' c x := by
    ext i j
    apply Complex.ext <;> simp [unrealify]

theorem ur_rl (X : Matrix (Fin n) (Fin n) ℂ) : urM n (rlM n X) = X := unr_re X

theorem rl_ur (x : EuclideanSpace ℝ (Fin n × Fin n × Bool)) : rlM n (urM n x) = x := by
  ext ⟨i, j, b⟩
  cases b <;> simp [rlM, urM, realifyFun, unrealify]

theorem frob_ur (x : EuclideanSpace ℝ (Fin n × Fin n × Bool)) : frob (urM n x) = ‖x‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type]
  unfold frob
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Fintype.sum_bool, Complex.sq_norm, Complex.normSq_apply]
  simp [urM, unrealify, Real.norm_eq_abs, sq]
  ring

def subC (ε : Fin n → Bool) (S : Finset (Fin n)) : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ) where
  carrier := {M | InCompl ε S M}
  zero_mem' := ⟨by simp, fun _ _ _ _ => rfl⟩
  add_mem' := by
    intro A B hA hB
    refine ⟨?_, fun i hi j hj => ?_⟩
    · rw [Matrix.conjTranspose_add, Matrix.add_mul, Matrix.mul_add]
      have := congrArg₂ (· + ·) hA.1 hB.1
      simp only [add_zero] at this
      rw [← this]; abel
    · show A i j + B i j = 0
      rw [hA.2 i hi j hj, hB.2 i hi j hj, add_zero]
  smul_mem' := by
    intro c A hA
    refine ⟨?_, fun i hi j hj => ?_⟩
    · show (c • A)ᴴ * Formalism.REAL.Jm ε + Formalism.REAL.Jm ε * (c • A) = 0
      rw [Matrix.conjTranspose_smul, star_trivial, Matrix.smul_mul, Matrix.mul_smul, ← smul_add, hA.1, smul_zero]
    · show c • A i j = 0
      rw [hA.2 i hi j hj, smul_zero]

def subB (ε : Fin n → Bool) (S : Finset (Fin n)) : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ) where
  carrier := {M | InBlock ε S M}
  zero_mem' := ⟨by simp, fun _ _ _ => rfl⟩
  add_mem' := by
    intro A B hA hB
    refine ⟨?_, fun i j hij => ?_⟩
    · rw [Matrix.conjTranspose_add, Matrix.add_mul, Matrix.mul_add]
      have := congrArg₂ (· + ·) hA.1 hB.1
      simp only [add_zero] at this
      rw [← this]; abel
    · show A i j + B i j = 0
      rw [hA.2 i j hij, hB.2 i j hij, add_zero]
  smul_mem' := by
    intro c A hA
    refine ⟨?_, fun i j hij => ?_⟩
    · show (c • A)ᴴ * Formalism.REAL.Jm ε + Formalism.REAL.Jm ε * (c • A) = 0
      rw [Matrix.conjTranspose_smul, star_trivial, Matrix.smul_mul, Matrix.mul_smul, ← smul_add, hA.1, smul_zero]
    · show c • A i j = 0
      rw [hA.2 i j hij, smul_zero]

def blk (S : Finset (Fin n)) (X : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  fun i j => if i ∈ S ∧ j ∈ S then X i j else 0

theorem lie_entry (ε : Fin n → Bool) (X : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) :
    (Xᴴ * Formalism.REAL.Jm ε + Formalism.REAL.Jm ε * X) i j =
      star (X j i) * (if ε j then 1 else -1) + (if ε i then 1 else -1) * X i j := by
  simp [Formalism.REAL.Jm, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.conjTranspose_apply]

theorem blk_lie (ε : Fin n → Bool) (S : Finset (Fin n)) (X : Matrix (Fin n) (Fin n) ℂ)
    (hX : Xᴴ * Formalism.REAL.Jm ε + Formalism.REAL.Jm ε * X = 0) :
    (blk S X)ᴴ * Formalism.REAL.Jm ε + Formalism.REAL.Jm ε * blk S X = 0 := by
  ext i j
  have h := congrFun (congrFun hX i) j
  rw [lie_entry] at h ⊢
  by_cases hij : i ∈ S ∧ j ∈ S
  · have hji : j ∈ S ∧ i ∈ S := ⟨hij.2, hij.1⟩
    simp only [blk, if_pos hij, if_pos hji]
    simpa using h
  · have hji : ¬ (j ∈ S ∧ i ∈ S) := fun h' => hij ⟨h'.2, h'.1⟩
    simp [blk, if_neg hij, if_neg hji]

end Coords

section Split

variable {n : ℕ}

theorem sup_eq_gLie (ε : Fin n → Bool) (S : Finset (Fin n)) :
    (subC ε S).map (rlM n) ⊔ (subB ε S).map (rlM n) = gLie ε := by
  apply le_antisymm
  · refine sup_le ?_ ?_
    · rintro _ ⟨X, hX, rfl⟩
      exact skewLie_holds n ε X hX.1
    · rintro _ ⟨X, hX, rfl⟩
      exact skewLie_holds n ε X hX.1
  · intro x hx
    set X := urM n x with hXd
    have hXl : Xᴴ * Formalism.REAL.Jm ε + Formalism.REAL.Jm ε * X = 0 := lieSkew_holds n ε x hx
    have hb : blk S X ∈ subB ε S := by
      refine ⟨blk_lie ε S X hXl, fun i j hij => ?_⟩
      have : ¬ (i ∈ S ∧ j ∈ S) := by tauto
      simp [blk, this]
    have hc : X - blk S X ∈ subC ε S := by
      refine ⟨?_, fun i hi j hj => ?_⟩
      · rw [Matrix.conjTranspose_sub, Matrix.sub_mul, Matrix.mul_sub, sub_add_sub_comm, hXl, blk_lie ε S X hXl,
          sub_zero]
      · show X i j - blk S X i j = 0
        simp [blk, hi, hj]
    have e : x = rlM n (X - blk S X) + rlM n (blk S X) := by
      rw [← map_add, sub_add_cancel, hXd, rl_ur]
    rw [e]
    exact Submodule.add_mem_sup (Submodule.mem_map_of_mem hc) (Submodule.mem_map_of_mem hb)

theorem orth_CB (ε : Fin n → Bool) (S : Finset (Fin n)) :
    ∀ x ∈ (subC ε S).map (rlM n), ∀ y ∈ (subB ε S).map (rlM n), inner ℝ x y = 0 := by
  rintro _ ⟨A, hA, rfl⟩ _ ⟨B, hB, rfl⟩
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  refine Finset.sum_eq_zero fun p _ => ?_
  obtain ⟨i, j, b⟩ := p
  by_cases hij : i ∈ S ∧ j ∈ S
  · have h0 : A i j = 0 := hA.2 i hij.1 j hij.2
    cases b <;> simp [rlM, realifyFun, h0]
  · have h0 : B i j = 0 := hB.2 i j (by tauto)
    cases b <;> simp [rlM, realifyFun, h0]

end Split

section Chart

variable {n : ℕ}

theorem exp_blk_mul_proj (S : Finset (Fin n)) (M : Matrix (Fin n) (Fin n) ℂ)
    (hM : ∀ i j, (i ∉ S ∨ j ∉ S) → M i j = 0) :
    NormedSpace.exp M * Matrix.diagonal (fun k => if k ∈ S then (0 : ℂ) else 1) =
      Matrix.diagonal (fun k => if k ∈ S then (0 : ℂ) else 1) := by
  apply exp_mul_of_mul_eq_zero
  ext a b
  rw [Matrix.mul_diagonal]
  by_cases hb : b ∈ S
  · simp [hb]
  · simp [hb, hM a b (Or.inr hb)]

set_option backward.isDefEq.respectTransparency false in
theorem exp_neg_mul_exp {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) :
    NormedSpace.exp M * NormedSpace.exp (-M) = 1 := by
  rw [← Matrix.exp_add_of_commute M (-M) (Commute.neg_right (Commute.refl M)), add_neg_cancel,
    NormedSpace.exp_zero]

set_option backward.isDefEq.respectTransparency false in
theorem exp_neg_mul_exp' {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) :
    NormedSpace.exp (-M) * NormedSpace.exp M = 1 := by
  rw [← Matrix.exp_add_of_commute (-M) M (Commute.neg_left (Commute.refl M)), neg_add_cancel,
    NormedSpace.exp_zero]

theorem chart_injOn {α β : Type} [Fintype α] [Fintype β] (ε : Fin n → Bool) (S : Finset (Fin n))
    (L₀ : EuclideanSpace ℝ α →ₗ[ℝ] Matrix (Fin n) (Fin n) ℂ) (L₁ : EuclideanSpace ℝ β →ₗ[ℝ] Matrix (Fin n) (Fin n) ℂ)
    (h3 : ∀ z, InCompl ε S (L₀ z)) (h4 : ∀ z, frob (L₀ z) = ‖z‖ ^ 2)
    (h7 : ∀ z, InBlock ε S (L₁ z)) (h8 : ∀ z, frob (L₁ z) = ‖z‖ ^ 2) :
    ∃ r : ℝ, 0 < r ∧ Set.InjOn (fun z : EuclideanSpace ℝ α × EuclideanSpace ℝ β =>
      expU ε (L₀ z.1) * expU ε (L₁ z.2)) (ball 0 r) := by
  set P := Matrix.diagonal (fun k => if k ∈ S then (0 : ℂ) else 1) with hP
  have hz : ∀ {γ : Type} [Fintype γ] (L' : EuclideanSpace ℝ γ →ₗ[ℝ] Matrix (Fin n) (Fin n) ℂ),
      (∀ z, frob (L' z) = ‖z‖ ^ 2) → ∀ x, L' x = 0 → x = 0 := by
    intro γ _ L' hn x hx
    have := hn x
    rw [hx] at this
    simp only [frob, Matrix.zero_apply, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
      Finset.sum_const_zero] at this
    exact norm_eq_zero.1 (pow_eq_zero_iff (n := 2) (by norm_num) |>.1 this.symm)
  obtain ⟨r1, hr1, hi1⟩ := exp_mul_injOn (V := Unit) (LinearMap.pi fun _ => L₀) (fun _ => P) fun x hx =>
    hz L₀ h4 x (lie_zero_of_cols ε S _ (h3 x).1 (h3 x).2 (hx ()))
  obtain ⟨r2, hr2, hi2⟩ := exp_mul_injOn (V := Unit) (LinearMap.pi fun _ => L₁) (fun _ => 1) fun x hx =>
    hz L₁ h8 x (by simpa using hx ())
  refine ⟨min r1 r2, lt_min hr1 hr2, fun z hz' z' hz'' he => ?_⟩
  have hb1 : ∀ p : EuclideanSpace ℝ α × EuclideanSpace ℝ β, p ∈ ball 0 (min r1 r2) → p.1 ∈ ball 0 r1 ∧ p.2 ∈ ball 0 r2 := by
    intro p hp
    rw [mem_ball_zero_iff, Prod.norm_def] at hp
    exact ⟨mem_ball_zero_iff.2 ((le_max_left _ _).trans_lt (hp.trans_le (min_le_left _ _))),
      mem_ball_zero_iff.2 ((le_max_right _ _).trans_lt (hp.trans_le (min_le_right _ _)))⟩

  have hm : NormedSpace.exp (L₀ z.1) * NormedSpace.exp (L₁ z.2) =
      NormedSpace.exp (L₀ z'.1) * NormedSpace.exp (L₁ z'.2) := by
    have := congrArg (fun g : Formalism.REAL.UJ ε => ((g : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)) he
    simp only [Subgroup.coe_mul, Units.val_mul] at this
    rwa [expU_val _ _ (h3 z.1).1, expU_val _ _ (h7 z.2).1, expU_val _ _ (h3 z'.1).1,
      expU_val _ _ (h7 z'.2).1] at this
  have hblk : ∀ y, ∀ i j, (i ∉ S ∨ j ∉ S) → (-L₁ y) i j = 0 := fun y i j hij => by
    simp [(h7 y).2 i j hij]
  have hx : z.1 = z'.1 := by
    apply hi1 (hb1 z hz').1 (hb1 z' hz'').1
    funext u
    show NormedSpace.exp (L₀ z.1) * P = NormedSpace.exp (L₀ z'.1) * P
    have e1 : NormedSpace.exp (L₀ z.1) =
        NormedSpace.exp (L₀ z'.1) * NormedSpace.exp (L₁ z'.2) * NormedSpace.exp (-L₁ z.2) := by
      rw [← hm, Matrix.mul_assoc, exp_neg_mul_exp, Matrix.mul_one]
    rw [e1, Matrix.mul_assoc, Matrix.mul_assoc, exp_blk_mul_proj S _ (hblk z.2), exp_blk_mul_proj S _ (h7 z'.2).2]
  have hy : z.2 = z'.2 := by
    apply hi2 (hb1 z hz').2 (hb1 z' hz'').2
    funext u
    show NormedSpace.exp (L₁ z.2) * 1 = NormedSpace.exp (L₁ z'.2) * 1
    rw [hx] at hm
    have := congrArg (fun A => NormedSpace.exp (-L₀ z'.1) * A) hm
    simp only [← Matrix.mul_assoc, exp_neg_mul_exp', Matrix.one_mul] at this
    rw [this]
  exact Prod.ext hx hy

end Chart

theorem placeChartV_of (hE : ExpProdU) : PlaceChartV := by
  intro n ε S hSε hgd
  set m := (subC ε S).map (rlM n) with hm
  set h := (subB ε S).map (rlM n) with hh
  let bm := stdOrthonormalBasis ℝ m
  let bh := stdOrthonormalBasis ℝ h
  let L0' : EuclideanSpace ℝ (Fin (Module.finrank ℝ m)) ≃ₗᵢ[ℝ] m := bm.repr.symm
  let L1' : EuclideanSpace ℝ (Fin (Module.finrank ℝ h)) ≃ₗᵢ[ℝ] h := bh.repr.symm
  obtain ⟨r, hr, D, hDc, hD0, hDm, hdens⟩ :=
    hE n ε m h (sup_eq_gLie ε S) (orth_CB ε S) _ _ L0' L1' hgd
  let L₀ : EuclideanSpace ℝ (Fin (Module.finrank ℝ m)) →ₗ[ℝ] Matrix (Fin n) (Fin n) ℂ :=
    (urM n).comp (m.subtype.comp L0'.toLinearEquiv.toLinearMap)
  let P₀ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ m)) :=
    L0'.symm.toLinearEquiv.toLinearMap.comp ((m.orthogonalProjection : _ →L[ℝ] m).toLinearMap.comp (rlM n))
  let L₁ : EuclideanSpace ℝ (Fin (Module.finrank ℝ h)) →ₗ[ℝ] Matrix (Fin n) (Fin n) ℂ :=
    (urM n).comp (h.subtype.comp L1'.toLinearEquiv.toLinearMap)
  let P₁ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ h)) :=
    L1'.symm.toLinearEquiv.toLinearMap.comp ((h.orthogonalProjection : _ →L[ℝ] h).toLinearMap.comp (rlM n))
  have hL0 : ∀ z, L₀ z = urM n (L0' z : EuclideanSpace ℝ (Fin n × Fin n × Bool)) := fun z => rfl
  have hL1 : ∀ z, L₁ z = urM n (L1' z : EuclideanSpace ℝ (Fin n × Fin n × Bool)) := fun z => rfl
  have h1 : ∀ z, P₀ (L₀ z) = z := by
    intro z
    show L0'.symm (m.orthogonalProjection (rlM n (urM n (L0' z : EuclideanSpace ℝ (Fin n × Fin n × Bool))))) = z
    rw [rl_ur, Submodule.orthogonalProjection_mem_subspace_eq_self, LinearIsometryEquiv.symm_apply_apply]
  have h2 : ∀ M, InCompl ε S M → L₀ (P₀ M) = M := by
    intro M hM
    have hmem : rlM n M ∈ m := Submodule.mem_map_of_mem (p := subC ε S) hM
    show urM n (L0' (L0'.symm (m.orthogonalProjection (rlM n M))) : EuclideanSpace ℝ (Fin n × Fin n × Bool)) = M
    rw [LinearIsometryEquiv.apply_symm_apply,
      Submodule.orthogonalProjection_mem_subspace_eq_self (⟨rlM n M, hmem⟩ : m)]
    exact ur_rl M
  have h3 : ∀ z, InCompl ε S (L₀ z) := by
    intro z
    obtain ⟨X, hX, hXe⟩ := (L0' z).2
    rw [hL0, ← hXe, ur_rl]
    exact hX
  have h4 : ∀ z, frob (L₀ z) = ‖z‖ ^ 2 := by
    intro z
    rw [hL0, frob_ur]
    exact congrArg (· ^ 2) ((Submodule.coe_norm (L0' z)).symm.trans (L0'.norm_map z))
  have h5 : ∀ z, P₁ (L₁ z) = z := by
    intro z
    show L1'.symm (h.orthogonalProjection (rlM n (urM n (L1' z : EuclideanSpace ℝ (Fin n × Fin n × Bool))))) = z
    rw [rl_ur, Submodule.orthogonalProjection_mem_subspace_eq_self, LinearIsometryEquiv.symm_apply_apply]
  have h6 : ∀ M, InBlock ε S M → L₁ (P₁ M) = M := by
    intro M hM
    have hmem : rlM n M ∈ h := Submodule.mem_map_of_mem (p := subB ε S) hM
    show urM n (L1' (L1'.symm (h.orthogonalProjection (rlM n M))) : EuclideanSpace ℝ (Fin n × Fin n × Bool)) = M
    rw [LinearIsometryEquiv.apply_symm_apply,
      Submodule.orthogonalProjection_mem_subspace_eq_self (⟨rlM n M, hmem⟩ : h)]
    exact ur_rl M
  have h7 : ∀ z, InBlock ε S (L₁ z) := by
    intro z
    obtain ⟨X, hX, hXe⟩ := (L1' z).2
    rw [hL1, ← hXe, ur_rl]
    exact hX
  have h8 : ∀ z, frob (L₁ z) = ‖z‖ ^ 2 := by
    intro z
    rw [hL1, frob_ur]
    exact congrArg (· ^ 2) ((Submodule.coe_norm (L1' z)).symm.trans (L1'.norm_map z))
  obtain ⟨rI, hrI, hinj⟩ := chart_injOn ε S L₀ L₁ h3 h4 h7 h8
  have hofr : ∀ z, ENNReal.ofReal (max (D z) 0) = ENNReal.ofReal (D z) := by
    intro z
    rcases le_total (D z) 0 with hz | hz
    · rw [max_eq_right hz, ENNReal.ofReal_zero, ENNReal.ofReal_of_nonpos hz]
    · rw [max_eq_left hz]
  refine ⟨_, _, inferInstance, inferInstance, L₀, P₀, L₁, P₁, min r rI, fun z => max (D z) 0,
    h1, h2, h3, h4, h5, h6, h7, h8, lt_min hr hrI, hDc.max continuousAt_const, ?_, hDm.max measurable_const,
    fun z => le_max_right _ _, ?_, hinj.mono (ball_subset_ball (min_le_right _ _)), fun A hA hAm => ?_⟩
  · simp only
    rw [hD0]
    exact max_eq_left hgd.2.le
  · exact (continuous_expU ε (fun z : EuclideanSpace ℝ (Fin (Module.finrank ℝ m)) ×
        EuclideanSpace ℝ (Fin (Module.finrank ℝ h)) => L₀ z.1)
      (L₀.continuous_of_finiteDimensional.comp continuous_fst) fun z => (h3 z.1).1).mul
      (continuous_expU ε (fun z : EuclideanSpace ℝ (Fin (Module.finrank ℝ m)) ×
        EuclideanSpace ℝ (Fin (Module.finrank ℝ h)) => L₁ z.2)
      (L₁.continuous_of_finiteDimensional.comp continuous_snd) fun z => (h7 z.2).1)
  · have := hdens A (hA.trans (ball_subset_ball (min_le_left _ _))) hAm
    simp_rw [hofr]
    exact this

end PI.AprimeInfW
