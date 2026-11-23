import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.PermutationSigns.PadMHerm

noncomputable section

open NumberField Matrix MeasureTheory UpperTheory.V.KT UpperTheory.V.KL

namespace PositivityTheory.KB.BlockInvariants

variable {L : Type} [Field L] [NumberField L] {N : ℕ}

open scoped MatrixOrder in
open ComplexOrder in
theorem sqrt_fac {A : Matrix (Fin N) (Fin N) ℂ} (hA : A.PosDef) :
    ∃ B : GL (Fin N) ℂ, A = (B : Matrix (Fin N) (Fin N) ℂ)ᴴ * B := by
  classical
  obtain ⟨B, hB⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hA.posSemidef.nonneg
  have hdet : IsUnit B.det := by
    have h1 : IsUnit (star B * B).det := (Matrix.isUnit_iff_isUnit_det _).mp (hB ▸ hA.isUnit)
    rw [Matrix.det_mul] at h1
    exact isUnit_of_mul_isUnit_right h1
  have hu : IsUnit B := (Matrix.isUnit_iff_isUnit_det _).mpr hdet
  refine ⟨hu.unit, ?_⟩
  simpa [Matrix.star_eq_conjTranspose] using hB

private theorem mat_actL_eq_conjTranspose_inv_mul_mul_inv (g : Gp L N) (h : HS L N) (w : InfinitePlace L) :
    mat (actL g h) w = ((g w : Matrix (Fin N) (Fin N) ℂ)⁻¹)ᴴ * mat h w * (g w : Matrix (Fin N) (Fin N) ℂ)⁻¹ := by
  simp [actL, actM, mat, mkHS]
  rfl

private theorem UpqT_mat_one' (w : InfinitePlace L) : mat (one L N).1 w = 1 := by
  simp [one, mat, mkHS]
  rfl

private theorem gl_coe_mul_coe_inv_eq_one (B : GL (Fin N) ℂ) :
    (B : Matrix (Fin N) (Fin N) ℂ) * (B : Matrix (Fin N) (Fin N) ℂ)⁻¹ = 1 :=
  Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp B.isUnit)

private theorem gl_coe_inv_mul_coe_eq_one (B : GL (Fin N) ℂ) :
    (B : Matrix (Fin N) (Fin N) ℂ)⁻¹ * (B : Matrix (Fin N) (Fin N) ℂ) = 1 :=
  Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp B.isUnit)

theorem trans_pos {h : HS L N} (hh : h ∈ Pos L N) : ∃ g : Gp L N, actL g h = (one L N).1 := by
  simp only [Pos, Set.mem_setOf_eq] at hh
  choose B hB using fun w => sqrt_fac (hh w)
  refine ⟨B, HS_ext fun w => ?_⟩
  rw [mat_actL_eq_conjTranspose_inv_mul_mul_inv, UpqT_mat_one', hB w]
  calc _ = ((B w : Matrix (Fin N) (Fin N) ℂ) * (B w : Matrix (Fin N) (Fin N) ℂ)⁻¹)ᴴ *
        ((B w : Matrix (Fin N) (Fin N) ℂ) * (B w : Matrix (Fin N) (Fin N) ℂ)⁻¹) := by
          rw [Matrix.conjTranspose_mul]
          simp only [Matrix.mul_assoc]
    _ = 1 := by rw [gl_coe_mul_coe_inv_eq_one]; simp

theorem actL_sec {h : HS L N} (hh : h ∈ Pos L N) : actL (sec h) h = (one L N).1 :=
  Classical.epsilon_spec (trans_pos hh)

private theorem actL_inv_actL' (g : Gp L N) (h : HS L N) : actL g⁻¹ (actL g h) = h := by
  refine HS_ext fun w => ?_
  rw [mat_actL_eq_conjTranspose_inv_mul_mul_inv, mat_actL_eq_conjTranspose_inv_mul_mul_inv]
  have e : ((g⁻¹ w : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ)⁻¹ = (g w : Matrix (Fin N) (Fin N) ℂ) := by
    rw [Pi.inv_apply, Matrix.coe_units_inv, Matrix.nonsing_inv_nonsing_inv _
      ((Matrix.isUnit_iff_isUnit_det _).mp (g w).isUnit)]
  rw [e]
  calc _ = ((g w : Matrix (Fin N) (Fin N) ℂ)⁻¹ * (g w : Matrix (Fin N) (Fin N) ℂ))ᴴ * mat h w *
        ((g w : Matrix (Fin N) (Fin N) ℂ)⁻¹ * (g w : Matrix (Fin N) (Fin N) ℂ)) := by
          rw [Matrix.conjTranspose_mul]
          simp only [Matrix.mul_assoc]
    _ = mat h w := by rw [gl_coe_inv_mul_coe_eq_one]; simp

theorem actL_inv_sec {h : HS L N} (hh : h ∈ Pos L N) : actL (sec h)⁻¹ (one L N).1 = h := by
  rw [← actL_sec hh, actL_inv_actL']

private theorem actL_mul' (a b : Gp L N) (x : HS L N) : actL (a * b) x = actL a (actL b x) := by
  refine HS_ext fun w => ?_
  rw [mat_actL_eq_conjTranspose_inv_mul_mul_inv, mat_actL_eq_conjTranspose_inv_mul_mul_inv, mat_actL_eq_conjTranspose_inv_mul_mul_inv, Pi.mul_apply, Units.val_mul, Matrix.mul_inv_rev,
    Matrix.conjTranspose_mul]
  simp only [Matrix.mul_assoc]

open ComplexOrder in
private theorem actL_mem_Pos (g : Gp L N) {h : HS L N} (hh : h ∈ Pos L N) : actL g h ∈ Pos L N := by
  simp only [Pos, Set.mem_setOf_eq] at hh ⊢
  intro w
  rw [mat_actL_eq_conjTranspose_inv_mul_mul_inv, ← Matrix.coe_units_inv]
  have hB : IsUnit (((g w)⁻¹ : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) := Units.isUnit _
  have hBh : IsUnit (((g w)⁻¹ : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ)ᴴ := by
    refine (Matrix.isUnit_iff_isUnit_det _).mpr ?_
    rw [Matrix.det_conjTranspose]
    exact ((Matrix.isUnit_iff_isUnit_det _).mp hB).star
  exact ((hh w).posSemidef.conjTranspose_mul_mul_same _).posDef_iff_isUnit.mpr
    ((hBh.mul (hh w).isUnit).mul hB)

theorem fInv_ext {q : ℕ} {β : HS L N [⋀^Fin q]→L[ℝ] ℝ} (hβ : UInv β) (g : Gp L N) : FInv (ext β) g := by
  intro h hh
  have hgh := actL_mem_Pos g hh
  have e1 : actL (sec (actL g h)) (actL g h) = (one L N).1 := actL_sec hgh
  have hu : actL (sec (actL g h) * g * (sec h)⁻¹) (one L N).1 = (one L N).1 := by
    rw [actL_mul', actL_mul', actL_inv_sec hh, e1]
  have hβu := hβ _ hu
  have hmul : sec (actL g h) * g = (sec (actL g h) * g * (sec h)⁻¹) * sec h := by group
  ext v
  simp only [ContinuousAlternatingMap.compContinuousLinearMap_apply]
  calc β (fun i => actL (sec (actL g h)) (actL g (v i)))
      = β (fun i => actL (sec (actL g h) * g * (sec h)⁻¹) (actL (sec h) (v i))) := by
        congr 1
        funext i
        rw [← actL_mul', ← actL_mul', ← hmul]
    _ = β (fun i => actL (sec h) (v i)) := by
        have := congrArg (fun f => f (fun i => actL (sec h) (v i))) hβu
        simpa [Function.comp_def] using this

theorem ext_one {q : ℕ} {β : HS L N [⋀^Fin q]→L[ℝ] ℝ} (hβ : UInv β) : ext β (one L N).1 = β := by
  have hu := hβ (sec (one L N).1) (actL_sec (one L N).2)
  ext v
  have := congrArg (fun f => f v) hu
  simpa [ext, Function.comp_def] using this

theorem ext_uniq {q : ℕ} {ω : Form (HS L N) q} (hω : ∀ g, FInv ω g) {h : HS L N} (hh : h ∈ Pos L N) :
    ω h = ext (ω (one L N).1) h := by
  have h1 := hω (sec h)
  unfold FInv at h1
  have h2 := h1 h hh
  rw [actL_sec hh] at h2
  rw [← h2]
  ext v
  simp [ext]

theorem uInv_of {q : ℕ} {ω : Form (HS L N) q} (hω : ∀ g, FInv ω g) : UInv (ω (one L N).1) := by
  unfold UInv
  intro u hu
  have h1 := hω u
  unfold FInv at h1
  have h2 := h1 _ (one L N).2
  rwa [hu] at h2

theorem ext_sum {q : ℕ} {ι : Type} [Fintype ι] (c : ι → ℝ) (β : ι → HS L N [⋀^Fin q]→L[ℝ] ℝ) (h : HS L N) :
    ext (∑ x, c x • β x) h = ∑ x, c x • ext (β x) h := by
  ext v
  simp [ext, ContinuousAlternatingMap.sum_apply]

theorem ext_smul {q : ℕ} (c : ℝ) (β : HS L N [⋀^Fin q]→L[ℝ] ℝ) (h : HS L N) :
    ext (c • β) h = c • ext β h := by
  ext v
  simp [ext]

theorem ext_zero {q : ℕ} (h : HS L N) : ext (0 : HS L N [⋀^Fin q]→L[ℝ] ℝ) h = 0 := by
  ext v
  simp [ext]

open ComplexOrder in
theorem convex_pos : Convex ℝ (Pos L N) := by
  intro x hx y hy a b ha hb hab
  simp only [Pos, Set.mem_setOf_eq] at *
  intro w
  have hm : mat (a • x + b • y) w = (a : ℂ) • mat x w + (b : ℂ) • mat y w := by simp [mat]
  rw [hm]
  rcases ha.lt_or_eq with ha' | ha'
  · exact (Matrix.PosDef.smul (hx w) (Complex.zero_lt_real.mpr ha')).add_posSemidef
      ((hy w).posSemidef.smul (Complex.zero_le_real.mpr hb))
  · subst ha'
    have hb1 : b = 1 := by linarith
    subst hb1
    simpa using hy w

theorem simplex_mem {q : ℕ} {y : Fin (q + 1) → HS L N} (hy : ∀ j, y j ∈ Pos L N) {t : Fin q → ℝ}
    (ht : (∀ j, 0 ≤ t j) ∧ ∑ j, t j ≤ 1) : y 0 + ∑ j, t j • (y j.succ - y 0) ∈ Pos L N := by
  obtain ⟨h0, h1⟩ := ht
  have hw : ∀ i ∈ (Finset.univ : Finset (Fin (q + 1))),
      0 ≤ (Fin.cons (1 - ∑ j, t j) t : Fin (q + 1) → ℝ) i := by
    intro i _
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa [sub_nonneg] using h1
    · simpa using h0 j
  have key := convex_pos.sum_mem hw (by simp [Fin.sum_univ_succ]) (fun i _ => hy i)
  convert key using 1
  simp [Fin.sum_univ_succ, smul_sub, Finset.sum_sub_distrib, sub_smul, ← Finset.sum_smul]
  abel

theorem simplex_eq {q : ℕ} : {t : Fin q → ℝ | (∀ j, 0 ≤ t j) ∧ ∑ j, t j ≤ 1} =
    (⋂ j, {t : Fin q → ℝ | 0 ≤ t j}) ∩ {t | ∑ j, t j ≤ 1} := by
  ext t; simp

private theorem isClosed_nonneg_sum_le_one_simplex {q : ℕ} :
    IsClosed {t : Fin q → ℝ | (∀ j, 0 ≤ t j) ∧ ∑ j, t j ≤ 1} := by
  rw [simplex_eq]
  refine (isClosed_iInter fun j => ?_).inter ?_
  · exact isClosed_le continuous_const (continuous_apply j)
  · exact isClosed_le (continuous_finset_sum _ fun j _ => continuous_apply j) continuous_const

theorem simplex_meas {q : ℕ} : MeasurableSet {t : Fin q → ℝ | (∀ j, 0 ≤ t j) ∧ ∑ j, t j ≤ 1} := isClosed_nonneg_sum_le_one_simplex.measurableSet

theorem simplex_compact {q : ℕ} : IsCompact {t : Fin q → ℝ | (∀ j, 0 ≤ t j) ∧ ∑ j, t j ≤ 1} := by
  refine (isCompact_univ_pi fun _ : Fin q => isCompact_Icc (a := (0 : ℝ)) (b := 1)).of_isClosed_subset
    isClosed_nonneg_sum_le_one_simplex ?_
  rintro t ⟨h0, h1⟩ j -
  refine ⟨h0 j, le_trans ?_ h1⟩
  exact Finset.single_le_sum (fun i _ => h0 i) (Finset.mem_univ j)

theorem intP_congr {q : ℕ} {ω ω' : Form (HS L N) q} (hω : ∀ h ∈ Pos L N, ω h = ω' h) :
    intP ω = intP ω' := by
  funext y
  unfold intP intS
  refine setIntegral_congr_fun simplex_meas fun t ht => ?_
  simp only
  rw [hω _ (simplex_mem (fun j => (y j).2) ht)]

theorem intS_pull {V V' : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup V']
    [NormedSpace ℝ V'] {q : ℕ} (ω : Form V' q) (P : V →L[ℝ] V') (e : V') (y : Fin (q + 1) → V) :
    intS ω (fun j => P (y j) + e) = intS (pullF ω P e) y := by
  unfold intS pullF
  congr 1
  funext t
  simp only [ContinuousAlternatingMap.compContinuousLinearMap_apply]
  congr 1
  · simp only [map_add, map_sum, map_sub, map_smul, add_sub_add_right_eq_sub]
    abel
  · funext j
    simp

theorem intP_smul {q : ℕ} (c : ℝ) (ω : Form (HS L N) q) :
    intP (fun h => c • ω h) = fun y => c * intP ω y := by
  funext y
  unfold intP intS
  simp only [ContinuousAlternatingMap.smul_apply, smul_eq_mul]
  exact integral_const_mul c _

theorem intP_integrable {q : ℕ} {ω : Form (HS L N) q} (hω : ContinuousOn ω (Pos L N)) (y : Fin (q + 1) → Pos L N) :
    IntegrableOn (fun t : Fin q → ℝ => ω ((y 0).1 + ∑ j, t j • ((y j.succ).1 - (y 0).1))
      fun j => (y j.succ).1 - (y 0).1) {t : Fin q → ℝ | (∀ j, 0 ≤ t j) ∧ ∑ j, t j ≤ 1} := by
  apply ContinuousOn.integrableOn_compact simplex_compact
  have ha : Continuous (fun t : Fin q → ℝ => (y 0).1 + ∑ j, t j • ((y j.succ).1 - (y 0).1)) := by
    fun_prop
  have hc : ContinuousOn (fun t : Fin q → ℝ => ω ((y 0).1 + ∑ j, t j • ((y j.succ).1 - (y 0).1)))
      {t : Fin q → ℝ | (∀ j, 0 ≤ t j) ∧ ∑ j, t j ≤ 1} :=
    hω.comp ha.continuousOn (fun t ht => simplex_mem (fun j => (y j).2) ht)
  exact (continuous_eval_const (fun j => (y j.succ).1 - (y 0).1)).comp_continuousOn hc

theorem intP_sum {q : ℕ} {ι : Type} [Fintype ι] (c : ι → ℝ) (ω : ι → Form (HS L N) q)
    (hω : ∀ x, ContinuousOn (ω x) (Pos L N)) :
    intP (fun h => ∑ x, c x • ω x h) = fun y => ∑ x, c x * intP (ω x) y := by
  funext y
  unfold intP intS
  have e : ∀ p (v : Fin q → HS L N), (∑ x, c x • ω x p) v = ∑ x, c x * ω x p v := by
    intro p v
    simp
  simp only [e]
  rw [MeasureTheory.integral_finset_sum _ fun x _ => (intP_integrable (hω x) y).const_mul (c x)]
  simp only [MeasureTheory.integral_const_mul]

theorem intP_inv {q : ℕ} {ω : Form (HS L N) q} (hω : ∀ g, FInv ω g) (g : Gp L N) (y : Fin (q + 1) → Pos L N) :
    intP ω (fun j => g • y j) = intP ω y := by
  have hs : ∀ p : Pos L N, ((g • p : Pos L N) : HS L N) = actL g p.1 := fun p => rfl
  unfold intP intS
  refine MeasureTheory.setIntegral_congr_fun simplex_meas fun t ht => ?_
  simp only [hs]
  have hmem := simplex_mem (fun j => (y j).2) ht
  have hF := hω g
  unfold FInv at hF
  have h1 := hF _ hmem
  rw [← h1]
  simp only [ContinuousAlternatingMap.compContinuousLinearMap_apply, map_add, map_sum, map_sub, map_smul,
    Function.comp_def]

def evL {G H Y : Type} [Group G] [Group H] [MulAction H Y] (ρ : G →* H) {m : ℕ}
    (F : (Fin (m + 1) → Y) → ℝ) (y : Y) : Chn G m →ₗ[ℝ] ℝ :=
  Finsupp.linearCombination ℝ fun g => F fun j => ρ (Fin.partialProd g j) • y

theorem evL_apply {G H Y : Type} [Group G] [Group H] [MulAction H Y] (ρ : G →* H) {m : ℕ}
    (F : (Fin (m + 1) → Y) → ℝ) (y : Y) (z : Chn G m) : evL ρ F y z = ev ρ F y z := by
  rfl

theorem partialProd_map {G H : Type} [Group G] [Group H] (f : G →* H) {m : ℕ} (g : Fin m → G) (j : Fin (m + 1)) :
    Fin.partialProd (fun i => f (g i)) j = f (Fin.partialProd g j) := by
  induction j using Fin.induction with
  | zero => simp
  | succ j ih => simp [Fin.partialProd_succ, ih]

theorem ev_cmap {G H K Y : Type} [Group G] [Group H] [Group K] [MulAction K Y] (ρ : H →* K) (f : G →* H)
    {m : ℕ} (F : (Fin (m + 1) → Y) → ℝ) (y : Y) (z : Chn G m) :
    ev ρ F y (cmap f m z) = ev (ρ.comp f) F y z := by
  simp [ev, cmap]
  rw [Finsupp.sum_mapDomain_index (fun _ => by simp) (fun _ _ _ => by ring)]
  simp [partialProd_map]

theorem ev_sum {G H Y : Type} [Group G] [Group H] [MulAction H Y] (ρ : G →* H) {m : ℕ} {ι : Type} [Fintype ι]
    (c : ι → ℝ) (F : ι → (Fin (m + 1) → Y) → ℝ) (y : Y) (z : Chn G m) :
    ev ρ (fun p => ∑ x, c x * F x p) y z = ∑ x, c x * ev ρ (F x) y z := by
  simp only [ev, Finsupp.sum, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun g _ => by ring

theorem ev_mul {G H Y : Type} [Group G] [Group H] [MulAction H Y] (ρ : G →* H) {m : ℕ}
    (c : ℝ) (F : (Fin (m + 1) → Y) → ℝ) (y : Y) (z : Chn G m) :
    ev ρ (fun p => c * F p) y z = c * ev ρ F y z := by
  simp [ev, Finsupp.sum, Finset.mul_sum, mul_left_comm]

end PositivityTheory.KB.BlockInvariants

end
