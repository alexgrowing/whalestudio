import Formalism.SharpRestriction.CuspSpanNormBounds.FrobeniusCoefficientMemLp.BigCellConjI
import Formalism.SharpRestriction.CuspSpanNormBounds.SpanMemOfImage

set_option linter.unusedVariables false

noncomputable section

namespace Formalism.MainNotions.S.Pv.Frames

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.MainNotions.FrameBoundFromBesselTorus

variable {k r : ℕ}

def cA (k r : ℕ) (x : Mt k r) : Mt k r := fun i j => (tTi k r * Matrix.of x * tT k r) i j

def cAi (k r : ℕ) (x : Mt k r) : Mt k r := fun i j => (tT k r * Matrix.of x * tTi k r) i j

theorem of_cA (x : Mt k r) : Matrix.of (cA k r x) = tTi k r * Matrix.of x * tT k r := by ext i j; rfl

theorem of_cAi (x : Mt k r) : Matrix.of (cAi k r x) = tT k r * Matrix.of x * tTi k r := by ext i j; rfl

theorem conjI_conj (M : Mx k r) : tTi k r * (tT k r * M * tTi k r) * tT k r = M := by
  have h : tTi k r * (tT k r * M * tTi k r) * tT k r = (tTi k r * tT k r) * M * (tTi k r * tT k r) := by
    simp only [Matrix.mul_assoc]
  rw [h, tTi_mul_tT, Matrix.one_mul, Matrix.mul_one]

theorem conj_conjI (M : Mx k r) : tT k r * (tTi k r * M * tT k r) * tTi k r = M := by
  have h : tT k r * (tTi k r * M * tT k r) * tTi k r = (tT k r * tTi k r) * M * (tT k r * tTi k r) := by
    simp only [Matrix.mul_assoc]
  rw [h, tT_mul_tTi, Matrix.one_mul, Matrix.mul_one]

theorem conjI_mul (M N : Mx k r) : tTi k r * (M * N) * tT k r = (tTi k r * M * tT k r) * (tTi k r * N * tT k r) := by
  have h : (tTi k r * M * tT k r) * (tTi k r * N * tT k r) = tTi k r * M * (tT k r * tTi k r) * N * tT k r := by
    simp only [Matrix.mul_assoc]
  rw [h, tT_mul_tTi, Matrix.mul_one, Matrix.mul_assoc (tTi k r) M N]

theorem conj_mul (M N : Mx k r) : tT k r * (M * N) * tTi k r = (tT k r * M * tTi k r) * (tT k r * N * tTi k r) := by
  have h : (tT k r * M * tTi k r) * (tT k r * N * tTi k r) = tT k r * M * (tTi k r * tT k r) * N * tTi k r := by
    simp only [Matrix.mul_assoc]
  rw [h, tTi_mul_tT, Matrix.mul_one, Matrix.mul_assoc (tT k r) M N]

theorem cA_cAi (x : Mt k r) : cA k r (cAi k r x) = x := by
  funext i j
  show (tTi k r * Matrix.of (cAi k r x) * tT k r) i j = x i j
  rw [of_cAi, conjI_conj, Matrix.of_apply]

theorem cAi_cA (x : Mt k r) : cAi k r (cA k r x) = x := by
  funext i j
  show (tT k r * Matrix.of (cA k r x) * tTi k r) i j = x i j
  rw [of_cA, conj_conjI, Matrix.of_apply]

theorem continuous_cA : Continuous (cA k r) := by
  unfold cA
  simp only [Matrix.mul_apply, Matrix.of_apply]
  fun_prop

theorem continuous_cAi : Continuous (cAi k r) := by
  unfold cAi
  simp only [Matrix.mul_apply, Matrix.of_apply]
  fun_prop

def cAE (k r : ℕ) : Mt k r ≃ᵐ Mt k r where
  toFun := cA k r
  invFun := cAi k r
  left_inv := cAi_cA
  right_inv := cA_cAi
  measurable_toFun := continuous_cA.measurable
  measurable_invFun := continuous_cAi.measurable

theorem cAE_coe : ⇑(cAE k r) = cA k r := rfl

theorem conjI_delta {M : Mx k r} {i j : Fin (2 * r + k + 1)} (h : M i j = if i = j then 1 else 0) :
    (tTi k r * M * tT k r) i j = if i = j then 1 else 0 := by
  have hd : ∀ l, star (dT k r l) * dT k r l = 1 := fun l => by
    have h1 := congrFun (congrFun (tTi_mul_tT k r) l) l
    simpa [tTi, tT] using h1
  simp only [tTi, tT, Matrix.diagonal_mul, Matrix.mul_diagonal, h]
  split_ifs with hij
  · subst hij
    rw [mul_one]
    exact hd i
  · rw [mul_zero, zero_mul]

theorem conj_delta {M : Mx k r} {i j : Fin (2 * r + k + 1)} (h : M i j = if i = j then 1 else 0) :
    (tT k r * M * tTi k r) i j = if i = j then 1 else 0 := by
  have hd : ∀ l, dT k r l * star (dT k r l) = 1 := fun l => by
    have h1 := congrFun (congrFun (tT_mul_tTi k r) l) l
    simpa [tTi, tT] using h1
  simp only [tTi, tT, Matrix.diagonal_mul, Matrix.mul_diagonal, h]
  split_ifs with hij
  · subst hij
    rw [mul_one]
    exact hd i
  · rw [mul_zero, zero_mul]

theorem conjI_mem_UH {M : Mx k r} (h : M ∈ UH (Hpk k r)) : tTi k r * M * tT k r ∈ UH (Hpk k r) := by
  have hT : (tT k r)ᴴ * Hpk k r * tT k r = Hpk k r := tT_mem_UH k r
  have hTi : (tTi k r)ᴴ * Hpk k r * tTi k r = Hpk k r := by
    calc (tTi k r)ᴴ * Hpk k r * tTi k r = (tTi k r)ᴴ * ((tT k r)ᴴ * Hpk k r * tT k r) * tTi k r := by rw [hT]
      _ = (tT k r * tTi k r)ᴴ * Hpk k r * (tT k r * tTi k r) := by
          rw [Matrix.conjTranspose_mul]
          simp only [Matrix.mul_assoc]
      _ = Hpk k r := by rw [tT_mul_tTi, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]
  have hM : Mᴴ * Hpk k r * M = Hpk k r := h
  show (tTi k r * M * tT k r)ᴴ * Hpk k r * (tTi k r * M * tT k r) = Hpk k r
  calc (tTi k r * M * tT k r)ᴴ * Hpk k r * (tTi k r * M * tT k r)
      = (tT k r)ᴴ * (Mᴴ * ((tTi k r)ᴴ * Hpk k r * tTi k r) * M) * tT k r := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = Hpk k r := by rw [hTi, hM, hT]

theorem conj_mem_UH {M : Mx k r} (h : M ∈ UH (Hpk k r)) : tT k r * M * tTi k r ∈ UH (Hpk k r) := by
  have hT : (tT k r)ᴴ * Hpk k r * tT k r = Hpk k r := tT_mem_UH k r
  have hTi : (tTi k r)ᴴ * Hpk k r * tTi k r = Hpk k r := by
    calc (tTi k r)ᴴ * Hpk k r * tTi k r = (tTi k r)ᴴ * ((tT k r)ᴴ * Hpk k r * tT k r) * tTi k r := by rw [hT]
      _ = (tT k r * tTi k r)ᴴ * Hpk k r * (tT k r * tTi k r) := by
          rw [Matrix.conjTranspose_mul]
          simp only [Matrix.mul_assoc]
      _ = Hpk k r := by rw [tT_mul_tTi, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]
  have hM : Mᴴ * Hpk k r * M = Hpk k r := h
  show (tT k r * M * tTi k r)ᴴ * Hpk k r * (tT k r * M * tTi k r) = Hpk k r
  calc (tT k r * M * tTi k r)ᴴ * Hpk k r * (tT k r * M * tTi k r)
      = (tTi k r)ᴴ * (Mᴴ * ((tT k r)ᴴ * Hpk k r * tT k r) * M) * tTi k r := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = Hpk k r := by rw [hT, hM, hTi]

theorem conjI_mem_Nset {M : Mx k r} (h : M ∈ Nset k r) : tTi k r * M * tT k r ∈ Nset k r := ⟨conjI_mem_UH h.1, fun a i hai => conjI_delta (h.2.1 a i hai),
  fun i j h1 h2 h3 => conjI_delta (h.2.2 i j h1 h2 h3)⟩

theorem conj_mem_Nset {M : Mx k r} (h : M ∈ Nset k r) : tT k r * M * tTi k r ∈ Nset k r := ⟨conj_mem_UH h.1, fun a i hai => conj_delta (h.2.1 a i hai),
  fun i j h1 h2 h3 => conj_delta (h.2.2 i j h1 h2 h3)⟩

theorem conjI_mem_Nset_iff (M : Mx k r) : tTi k r * M * tT k r ∈ Nset k r ↔ M ∈ Nset k r := by
  constructor
  · intro h
    have h1 := conj_mem_Nset h
    rwa [conj_conjI] at h1
  · exact conjI_mem_Nset

theorem conjI_mem_RStab_iff (g a : Mx k r) :
    tTi k r * a * tT k r ∈ RStab k r (tTi k r * g * tT k r) ↔ a ∈ RStab k r g := by
  have hinv1 : (tTi k r)⁻¹ = tT k r := Matrix.inv_eq_left_inv (tT_mul_tTi k r)
  have hinv2 : (tT k r)⁻¹ = tTi k r := Matrix.inv_eq_left_inv (tTi_mul_tT k r)
  have hg : (tTi k r * g * tT k r)⁻¹ * (tTi k r * a * tT k r) * (tTi k r * g * tT k r) =
      tTi k r * (g⁻¹ * a * g) * tT k r := by
    rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, hinv1, hinv2]
    calc tTi k r * (g⁻¹ * tT k r) * (tTi k r * a * tT k r) * (tTi k r * g * tT k r)
        = tTi k r * g⁻¹ * (tT k r * tTi k r) * a * (tT k r * tTi k r) * g * tT k r := by
          simp only [Matrix.mul_assoc]
      _ = tTi k r * (g⁻¹ * a * g) * tT k r := by
          rw [tT_mul_tTi]
          simp only [Matrix.mul_one, Matrix.mul_assoc]
  simp only [RStab, Set.mem_setOf_eq]
  rw [hg, conjI_mem_Nset_iff, conjI_mem_Nset_iff]

def uF (k r : ℕ) (i j : Fin (2 * r + k + 1)) : ℂ := star (dT k r i) * dT k r j

theorem dT_normSq (i : Fin (2 * r + k + 1)) : Complex.normSq (dT k r i) = 1 := by
  have h1 := congrFun (congrFun (tTi_mul_tT k r) i) i
  simp [tTi, tT] at h1
  rw [← Complex.normSq_eq_conj_mul_self] at h1
  exact_mod_cast h1

theorem uF_norm (i j : Fin (2 * r + k + 1)) : Complex.normSq (uF k r i j) = 1 := by
  rw [uF, Complex.normSq_mul, Complex.star_def, Complex.normSq_conj, dT_normSq, dT_normSq, one_mul]

def uE (k r : ℕ) : EuclideanSpace ℝ (IxE k r) →ₗ[ℝ] EuclideanSpace ℝ (IxE k r) where
  toFun y := WithLp.toLp 2 (fun p => if p.2.2 then (uF k r p.1 p.2.1 * ⟨y (p.1, p.2.1, false), y (p.1, p.2.1, true)⟩).im
    else (uF k r p.1 p.2.1 * ⟨y (p.1, p.2.1, false), y (p.1, p.2.1, true)⟩).re)
  map_add' x y := by
    ext ⟨i, j, b⟩
    cases b <;> simp [Complex.mul_re, Complex.mul_im] <;> ring
  map_smul' c x := by
    ext ⟨i, j, b⟩
    cases b <;> simp [Complex.mul_re, Complex.mul_im] <;> ring

def uEI (k r : ℕ) : EuclideanSpace ℝ (IxE k r) →ₗ[ℝ] EuclideanSpace ℝ (IxE k r) where
  toFun y := WithLp.toLp 2 (fun p => if p.2.2 then (star (uF k r p.1 p.2.1) * ⟨y (p.1, p.2.1, false), y (p.1, p.2.1, true)⟩).im
    else (star (uF k r p.1 p.2.1) * ⟨y (p.1, p.2.1, false), y (p.1, p.2.1, true)⟩).re)
  map_add' x y := by
    ext ⟨i, j, b⟩
    cases b <;> simp [Complex.mul_re, Complex.mul_im] <;> ring
  map_smul' c x := by
    ext ⟨i, j, b⟩
    cases b <;> simp [Complex.mul_re, Complex.mul_im] <;> ring

theorem unrealify_uE (y : EuclideanSpace ℝ (IxE k r)) :
    unrealify (uE k r y) = tTi k r * unrealify y * tT k r := by
  ext i j
  apply Complex.ext <;>
    simp [unrealify, uE, uF, tTi, tT, Matrix.diagonal_mul, Matrix.mul_diagonal, Complex.mul_re,
      Complex.mul_im] <;> ring

theorem unrealify_uEI (y : EuclideanSpace ℝ (IxE k r)) :
    unrealify (uEI k r y) = tT k r * unrealify y * tTi k r := by
  ext i j
  apply Complex.ext <;>
    simp [unrealify, uEI, uF, tTi, tT, Matrix.diagonal_mul, Matrix.mul_diagonal, Complex.mul_re,
      Complex.mul_im] <;> ring

theorem realify_unrealify (y : EuclideanSpace ℝ (IxE k r)) : (WithLp.equiv 2 _).symm (realifyFun (unrealify y)) = y := by
  ext ⟨i, j, b⟩
  cases b <;> simp [realifyFun, unrealify]

theorem uE_realify (X : Mx k r) :
    uE k r ((WithLp.equiv 2 _).symm (realifyFun X)) = (WithLp.equiv 2 _).symm (realifyFun (tTi k r * X * tT k r)) := by
  have ur : ∀ X : Mx k r, unrealify ((WithLp.equiv 2 _).symm (realifyFun X)) = X := fun X => by
    ext i j
    apply Complex.ext <;> simp [unrealify, realifyFun]
  have hinj : ∀ y y' : EuclideanSpace ℝ (IxE k r), unrealify y = unrealify y' → y = y' := fun y y' h => by
    rw [← realify_unrealify y, ← realify_unrealify y', h]
  apply hinj
  rw [unrealify_uE, ur, ur]

theorem uEI_realify (X : Mx k r) :
    uEI k r ((WithLp.equiv 2 _).symm (realifyFun X)) = (WithLp.equiv 2 _).symm (realifyFun (tT k r * X * tTi k r)) := by
  have ur : ∀ X : Mx k r, unrealify ((WithLp.equiv 2 _).symm (realifyFun X)) = X := fun X => by
    ext i j
    apply Complex.ext <;> simp [unrealify, realifyFun]
  have hinj : ∀ y y' : EuclideanSpace ℝ (IxE k r), unrealify y = unrealify y' → y = y' := fun y y' h => by
    rw [← realify_unrealify y, ← realify_unrealify y', h]
  apply hinj
  rw [unrealify_uEI, ur, ur]

theorem uE_uEI (y : EuclideanSpace ℝ (IxE k r)) : uE k r (uEI k r y) = y := by
  have ur : ∀ X : Mx k r, unrealify ((WithLp.equiv 2 _).symm (realifyFun X)) = X := fun X => by
    ext i j
    apply Complex.ext <;> simp [unrealify, realifyFun]
  have hinj : ∀ y y' : EuclideanSpace ℝ (IxE k r), unrealify y = unrealify y' → y = y' := fun y y' h => by
    rw [← realify_unrealify y, ← realify_unrealify y', h]
  apply hinj
  rw [unrealify_uE, unrealify_uEI, conjI_conj]

theorem uEI_uE (y : EuclideanSpace ℝ (IxE k r)) : uEI k r (uE k r y) = y := by
  have ur : ∀ X : Mx k r, unrealify ((WithLp.equiv 2 _).symm (realifyFun X)) = X := fun X => by
    ext i j
    apply Complex.ext <;> simp [unrealify, realifyFun]
  have hinj : ∀ y y' : EuclideanSpace ℝ (IxE k r), unrealify y = unrealify y' → y = y' := fun y y' h => by
    rw [← realify_unrealify y, ← realify_unrealify y', h]
  apply hinj
  rw [unrealify_uEI, unrealify_uE, conj_conjI]

theorem uE_norm_sq (y : EuclideanSpace ℝ (IxE k r)) : ‖uE k r y‖ ^ 2 = ‖y‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have hu := uF_norm (k := k) (r := r) i j
  rw [Complex.normSq_apply] at hu
  simp [uE, Real.norm_eq_abs, sq_abs, Complex.mul_re, Complex.mul_im]
  linear_combination (y (i, j, false) ^ 2 + y (i, j, true) ^ 2) * hu

theorem uE_norm (y : EuclideanSpace ℝ (IxE k r)) : ‖uE k r y‖ = ‖y‖ := by
  rw [← Real.sqrt_sq (norm_nonneg (uE k r y)), uE_norm_sq, Real.sqrt_sq (norm_nonneg y)]

theorem exp_conjI (X : Mx k r) : NormedSpace.exp (tTi k r * X * tT k r) = tTi k r * NormedSpace.exp X * tT k r := by
  have hinv : (tTi k r)⁻¹ = tT k r := Matrix.inv_eq_left_inv (tT_mul_tTi k r)
  have hU : IsUnit (tTi k r) := ⟨⟨tTi k r, tT k r, tTi_mul_tT k r, tT_mul_tTi k r⟩, rfl⟩
  have h := Matrix.exp_conj (tTi k r) X hU
  rwa [hinv] at h

theorem exp_conj' (X : Mx k r) : NormedSpace.exp (tT k r * X * tTi k r) = tT k r * NormedSpace.exp X * tTi k r := by
  have hinv : (tT k r)⁻¹ = tTi k r := Matrix.inv_eq_left_inv (tTi_mul_tT k r)
  have hU : IsUnit (tT k r) := ⟨⟨tT k r, tTi k r, tT_mul_tTi k r, tTi_mul_tT k r⟩, rfl⟩
  have h := Matrix.exp_conj (tT k r) X hU
  rwa [hinv] at h

theorem conjI_mem_lieOf (X : Mx k r) (hX : X ∈ lieOf (Nset k r)) : tTi k r * X * tT k r ∈ lieOf (Nset k r) := by
  intro t
  show NormedSpace.exp ((t : ℂ) • (tTi k r * X * tT k r)) ∈ Nset k r
  have e : (t : ℂ) • (tTi k r * X * tT k r) = tTi k r * ((t : ℂ) • X) * tT k r := by
    rw [Matrix.mul_smul, Matrix.smul_mul]
  rw [e, exp_conjI]
  exact conjI_mem_Nset (hX t)

theorem conj_mem_lieOf (X : Mx k r) (hX : X ∈ lieOf (Nset k r)) : tT k r * X * tTi k r ∈ lieOf (Nset k r) := by
  intro t
  show NormedSpace.exp ((t : ℂ) • (tT k r * X * tTi k r)) ∈ Nset k r
  have e : (t : ℂ) • (tT k r * X * tTi k r) = tT k r * ((t : ℂ) • X) * tTi k r := by
    rw [Matrix.mul_smul, Matrix.smul_mul]
  rw [e, exp_conj']
  exact conj_mem_Nset (hX t)

theorem uE_mem : ∀ x ∈ lieE (Nset k r), uE k r x ∈ lieE (Nset k r) := by
  intro x hx
  unfold lieE at hx ⊢
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨X, hX, rfl⟩ := hy
    show uE k r ((WithLp.equiv 2 _).symm (realifyFun X)) ∈ _
    rw [uE_realify]
    exact Submodule.subset_span ⟨_, conjI_mem_lieOf X hX, rfl⟩
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add y z _ _ hy hz => rw [map_add]; exact Submodule.add_mem _ hy hz
  | smul c y _ hy => rw [map_smul]; exact Submodule.smul_mem _ c hy

theorem uEI_mem : ∀ x ∈ lieE (Nset k r), uEI k r x ∈ lieE (Nset k r) := by
  intro x hx
  unfold lieE at hx ⊢
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨X, hX, rfl⟩ := hy
    show uEI k r ((WithLp.equiv 2 _).symm (realifyFun X)) ∈ _
    rw [uEI_realify]
    exact Submodule.subset_span ⟨_, conj_mem_lieOf X hX, rfl⟩
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add y z _ _ hy hz => rw [map_add]; exact Submodule.add_mem _ hy hz
  | smul c y _ hy => rw [map_smul]; exact Submodule.smul_mem _ c hy

def uL (k r : ℕ) : lieE (Nset k r) ≃ₗᵢ[ℝ] lieE (Nset k r) where
  toLinearEquiv := LinearEquiv.ofLinear ((uE k r).restrict uE_mem) ((uEI k r).restrict uEI_mem)
    (LinearMap.ext fun x => Subtype.ext (uE_uEI _)) (LinearMap.ext fun x => Subtype.ext (uEI_uE _))
  norm_map' x := by
    show ‖((uE k r).restrict uE_mem x : EuclideanSpace ℝ (IxE k r))‖ = ‖(x : EuclideanSpace ℝ (IxE k r))‖
    rw [LinearMap.coe_restrict_apply]
    exact uE_norm _

theorem cA_expL (x : lieE (Nset k r)) : cA k r (expL (Nset k r) x) = expL (Nset k r) (uL k r x) := by
  funext i j
  show (tTi k r * Matrix.of (expL (Nset k r) x) * tT k r) i j =
    NormedSpace.exp (unrealify ((uL k r x : lieE (Nset k r)) : EuclideanSpace ℝ (IxE k r))) i j
  have h1 : Matrix.of (expL (Nset k r) x) = NormedSpace.exp (unrealify (x : EuclideanSpace ℝ (IxE k r))) := rfl
  have h2 : ((uL k r x : lieE (Nset k r)) : EuclideanSpace ℝ (IxE k r)) = uE k r x := rfl
  rw [h1, h2, unrealify_uE, exp_conjI]

theorem map_cA_haarLie (κN : ENNReal) : (haarLie (Nset k r) κN).map (cA k r) = haarLie (Nset k r) κN := by
  have e : cA k r ∘ expL (Nset k r) = expL (Nset k r) ∘ (uL k r) := funext cA_expL
  have h0 : haarLie (Nset k r) κN = κN • (volume : Measure (lieE (Nset k r))).map (expL (Nset k r)) := rfl
  rw [h0, Measure.map_smul, Measure.map_map continuous_cA.measurable (continuous_expL _).measurable, e,
    ← Measure.map_map (continuous_expL _).measurable (uL k r).continuous.measurable,
    (uL k r).measurePreserving.map_eq]

theorem map_cA_UW {z : Fin (2 * r + k + 1) → ℂ} {μ : Measure (Mt k r)} (h : IsHaarOn (UWset k r z) μ) :
    μ.map (cA k r) = μ := by
  have hae : cA k r =ᵐ[μ] id := by
    have h3 := h.2.2.1
    rw [Filter.EventuallyEq, ae_iff]
    refine measure_mono_null (fun x hx => ?_) h3
    simp only [Set.mem_ofPred_eq] at hx ⊢
    intro hU
    apply hx
    funext i j
    show (tTi k r * Matrix.of x * tT k r) i j = x i j
    rw [UW_conjI hU]; rfl
  rw [Measure.map_congr hae, Measure.map_id]

def thP (k r : ℕ) : PairSp k r → PairSp k r :=
  Prod.map (Prod.map (cA k r) (cA k r)) (Prod.map (cA k r) (cA k r))

def thPI (k r : ℕ) : PairSp k r → PairSp k r :=
  Prod.map (Prod.map (cAi k r) (cAi k r)) (Prod.map (cAi k r) (cAi k r))

def thE (k r : ℕ) : PairSp k r ≃ᵐ PairSp k r where
  toFun := thP k r
  invFun := thPI k r
  left_inv := fun p => Prod.ext (Prod.ext (cAi_cA _) (cAi_cA _)) (Prod.ext (cAi_cA _) (cAi_cA _))
  right_inv := fun p => Prod.ext (Prod.ext (cA_cAi _) (cA_cAi _)) (Prod.ext (cA_cAi _) (cA_cAi _))
  measurable_toFun := (continuous_cA.measurable.prodMap continuous_cA.measurable).prodMap
    (continuous_cA.measurable.prodMap continuous_cA.measurable)
  measurable_invFun := (continuous_cAi.measurable.prodMap continuous_cAi.measurable).prodMap
    (continuous_cAi.measurable.prodMap continuous_cAi.measurable)

theorem thE_coe : ⇑(thE k r) = thP k r := rfl

theorem map_thP_pairMeas (L : LocBessel k r) : (pairMeas L).map (thP k r) = pairMeas L := by
  have := L.hμW.1.1
  have := L.hμW'.1.1
  have : SFinite L.μN := sFinite_haarLie _ _
  have mA := (continuous_cA (k := k) (r := r)).measurable
  unfold pairMeas thP
  rw [← Measure.map_prod_map _ _ (mA.prodMap mA) (mA.prodMap mA), ← Measure.map_prod_map _ _ mA mA,
    ← Measure.map_prod_map _ _ mA mA, map_cA_UW L.hμW.1, map_cA_UW L.hμW'.1]
  unfold LocBessel.μN
  rw [map_cA_haarLie]

end Formalism.MainNotions.S.Pv.Frames

end
