import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LocalWeightCharts.WavePacketL1L2

noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal

namespace WlocSk.PtD

open WlocSk Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.CayleySignature Formalism.L2.SG.WuDecay Formalism.L2.SG.SplitPrimeNormLemmas

variable {k r : ℕ}

def tau (k r : ℕ) (i : Fin (2 * r + k + 1)) : Fin (2 * r + k + 1) :=
  ⟨if i.val < r ∨ r + k < i.val then 2 * r + k - i.val else i.val, by split_ifs <;> omega⟩

def sgn (k r : ℕ) (i : Fin (2 * r + k + 1)) : ℂ := if i.val = r + k then -1 else 1

theorem hpk_row (i m : Fin (2 * r + k + 1)) :
    Hpk k r i m = if m = tau k r i then sgn k r i else 0 := by
  unfold Hpk tau sgn
  simp only [Fin.ext_iff]
  split_ifs <;> first | rfl | (exfalso; omega)

theorem hpk_mul_apply (A : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
    (i j : Fin (2 * r + k + 1)) : (Hpk k r * A) i j = sgn k r i * A (tau k r i) j := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (tau k r i)]
  · rw [hpk_row, if_pos rfl]
  · intro m _ hm
    rw [hpk_row, if_neg hm, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem tau_tau (i : Fin (2 * r + k + 1)) : tau k r (tau k r i) = i := by
  unfold tau
  apply Fin.ext
  simp only
  split_ifs <;> omega

theorem sgn_tau (i : Fin (2 * r + k + 1)) : sgn k r (tau k r i) = sgn k r i := by
  unfold sgn tau
  simp only
  split_ifs <;> first | rfl | (exfalso; omega)

theorem sgn_mul_self (i : Fin (2 * r + k + 1)) : sgn k r i * sgn k r i = 1 := by
  unfold sgn
  split_ifs <;> norm_num

theorem hpk_sq : Hpk k r * Hpk k r = 1 := by
  ext i j
  rw [hpk_mul_apply, hpk_row, tau_tau, sgn_tau, Matrix.one_apply]
  by_cases h : j = i
  · rw [if_pos h, if_pos h.symm, sgn_mul_self]
  · rw [if_neg h, if_neg (Ne.symm h), mul_zero]

theorem gr_left_inv {g : Mat k r} (hg : g ∈ Gr k r) : Hpk k r * gᴴ * Hpk k r * g = 1 := by
  have hg' : gᴴ * Hpk k r * g = Hpk k r := hg
  calc Hpk k r * gᴴ * Hpk k r * g = Hpk k r * (gᴴ * Hpk k r * g) := by
        simp only [Matrix.mul_assoc]
    _ = 1 := by rw [hg', hpk_sq]

theorem gr_isUnit {g : Mat k r} (hg : g ∈ Gr k r) : IsUnit g.det :=
  Matrix.isUnit_det_of_left_inverse (gr_left_inv hg)

theorem gr_inv_eq {g : Mat k r} (hg : g ∈ Gr k r) : g⁻¹ = Hpk k r * gᴴ * Hpk k r :=
  Matrix.inv_eq_left_inv (gr_left_inv hg)

theorem gr_one : (1 : Mat k r) ∈ Gr k r := by
  show (1 : Mat k r)ᴴ * Hpk k r * 1 = Hpk k r
  rw [conjTranspose_one, Matrix.one_mul, Matrix.mul_one]

theorem gr_mul {g h : Mat k r} (hg : g ∈ Gr k r) (hh : h ∈ Gr k r) : g * h ∈ Gr k r := by
  have hg' : gᴴ * Hpk k r * g = Hpk k r := hg
  have hh' : hᴴ * Hpk k r * h = Hpk k r := hh
  show (g * h)ᴴ * Hpk k r * (g * h) = Hpk k r
  rw [conjTranspose_mul]
  calc hᴴ * gᴴ * Hpk k r * (g * h) = hᴴ * (gᴴ * Hpk k r * g) * h := by
        simp only [Matrix.mul_assoc]
    _ = Hpk k r := by rw [hg', hh']

theorem gr_isClosed : IsClosed (Gr k r) := by
  have : Gr k r = (fun g : Mat k r => gᴴ * Hpk k r * g) ⁻¹' {Hpk k r} := rfl
  rw [this]
  exact isClosed_singleton.preimage
    (((continuous_id.matrix_conjTranspose).matrix_mul continuous_const).matrix_mul continuous_id)

theorem opn_nonneg (M : Mat k r) : 0 ≤ opn M := norm_nonneg _

theorem opn_mul (A B : Mat k r) : opn (A * B) ≤ opn A * opn B := by
  unfold opn
  rw [map_mul]
  exact norm_mul_le _ _

theorem opn_conjTranspose (A : Mat k r) : opn Aᴴ = opn A := by
  unfold opn
  rw [← Matrix.star_eq_conjTranspose, map_star, norm_star]

local instance instAlgCLM (n : ℕ) :
    Algebra ℂ (EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)) := ContinuousLinearMap.algebra
local instance instModCLM (n : ℕ) :
    Module ℂ (EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)) := ContinuousLinearMap.module

theorem opn_continuous : Continuous (fun M : Mat k r => opn M) := by
  unfold opn
  have h : Continuous (fun M : Mat k r => Matrix.toEuclideanCLM (n := Fin (2 * r + k + 1)) (𝕜 := ℂ) M) :=
    LinearMap.continuous_of_finiteDimensional
      ((Matrix.toEuclideanCLM (n := Fin (2 * r + k + 1)) (𝕜 := ℂ)).toAlgEquiv.toLinearEquiv.toLinearMap)
  exact continuous_norm.comp h

theorem opn_inv_le {g : Mat k r} (hg : g ∈ Gr k r) :
    opn g⁻¹ ≤ opn (Hpk k r) * opn (Hpk k r) * opn g := by
  rw [gr_inv_eq hg]
  calc opn (Hpk k r * gᴴ * Hpk k r) ≤ opn (Hpk k r * gᴴ) * opn (Hpk k r) := opn_mul _ _
    _ ≤ opn (Hpk k r) * opn gᴴ * opn (Hpk k r) :=
        mul_le_mul_of_nonneg_right (opn_mul _ _) (opn_nonneg _)
    _ = opn (Hpk k r) * opn (Hpk k r) * opn g := by rw [opn_conjTranspose]; ring

theorem opn_le_mul_inv (y : Mat k r) {t : Mat k r} (ht : t ∈ Gr k r) :
    opn y ≤ opn (y * t) * opn t⁻¹ := by
  have : y = y * t * t⁻¹ := by
    rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (gr_isUnit ht), Matrix.mul_one]
  calc opn y = opn (y * t * t⁻¹) := by rw [← this]
    _ ≤ _ := opn_mul _ _

theorem opn_pos {g : Mat k r} (hg : g ∈ Gr k r) : 0 < opn g := by
  rcases (opn_nonneg g).lt_or_eq with h | h
  · exact h
  · exfalso
    have h1 : opn (1 : Mat k r) ≤ opn g * opn g⁻¹ := by
      rw [← Matrix.mul_nonsing_inv _ (gr_isUnit hg)]; exact opn_mul _ _
    rw [← h, zero_mul] at h1
    have h2 : opn (1 : Mat k r) = 1 := by
      unfold opn; rw [map_one]; exact norm_one
    linarith

theorem nilradical_half_sum_nonneg : 0 ≤ N1H k r := by unfold N1H; positivity

def lmulH {y : Mat k r} (hy : y ∈ Gr k r) : Mt k r ≃ₜ Mt k r where
  toFun x := lmulM y x
  invFun x := lmulM y⁻¹ x
  left_inv x := by
    show y⁻¹ * (y * Matrix.of x) = Matrix.of x
    rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (gr_isUnit hy), Matrix.one_mul]
  right_inv x := by
    show y * (y⁻¹ * Matrix.of x) = Matrix.of x
    rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (gr_isUnit hy), Matrix.one_mul]
  continuous_toFun := by
    show Continuous fun x : Mat k r => y * x
    exact continuous_const.matrix_mul continuous_id
  continuous_invFun := by
    show Continuous fun x : Mat k r => y⁻¹ * x
    exact continuous_const.matrix_mul continuous_id

theorem lint_lmul {μ : Measure (Mt k r)} {y : Mat k r} (hy : y ∈ Gr k r)
    (hinv : μ.map (lmulM y) = μ) (F : Mt k r → ℝ≥0∞) :
    ∫⁻ t, F (lmulM y t) ∂μ = ∫⁻ t, F t ∂μ := by
  have h := lintegral_map_equiv F (lmulH hy).toMeasurableEquiv (μ := μ)
  have e : μ.map (lmulH hy).toMeasurableEquiv = μ.map (lmulM y) := rfl
  rw [e, hinv] at h
  exact h.symm

theorem ae_gr {μ : Measure (Mt k r)} (hconc : μ {x | Matrix.of x ∉ Gr k r} = 0) :
    ∀ᵐ x ∂μ, Matrix.of x ∈ Gr k r :=
  ae_iff.mpr hconc

section Decay

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {σ : Mat k r → (H →L[ℂ] H)}

theorem inner_iso (hσ : IsURepOn (Gr k r) σ) {x : Mat k r} (hx : x ∈ Gr k r) (u v : H) :
    ⟪σ x u, σ x v⟫_ℂ = ⟪u, v⟫_ℂ :=
  let L : H →ₗᵢ[ℂ] H := { toLinearMap := (σ x).toLinearMap, norm_map' := hσ.2.1 x hx }
  L.inner_map_map u v

theorem sigma_mul (hσ : IsURepOn (Gr k r) σ) {x y : Mat k r} (hx : x ∈ Gr k r) (hy : y ∈ Gr k r)
    (v : H) : σ (x * y) v = σ x (σ y v) := by
  rw [hσ.1.2 x hx y hy]; rfl

theorem coef_weighted_transl (hσ : IsURepOn (Gr k r) σ) {μ : Measure (Mt k r)}
    (hconc : μ {x | Matrix.of x ∉ Gr k r} = 0) (hinv : ∀ s ∈ Gr k r, μ.map (lmulM s) = μ)
    (w : H) {x₀ : Mat k r} (hx₀ : x₀ ∈ Gr k r) :
    ∫⁻ g, ‖⟪σ x₀ w, σ (Matrix.of g) w⟫_ℂ‖ₑ * ENNReal.ofReal (opn (Matrix.of g) ^ N1H k r) ∂μ ≤
      ENNReal.ofReal (opn x₀ ^ N1H k r) *
        ∫⁻ g, ‖⟪w, σ (Matrix.of g) w⟫_ℂ‖ₑ * ENNReal.ofReal (opn (Matrix.of g) ^ N1H k r) ∂μ := by
  rw [← lint_lmul hx₀ (hinv x₀ hx₀), ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_mono_ae
  filter_upwards [ae_gr hconc] with g hg
  show ‖⟪σ x₀ w, σ (x₀ * Matrix.of g) w⟫_ℂ‖ₑ * ENNReal.ofReal (opn (x₀ * Matrix.of g) ^ N1H k r) ≤
    ENNReal.ofReal (opn x₀ ^ N1H k r) *
      (‖⟪w, σ (Matrix.of g) w⟫_ℂ‖ₑ * ENNReal.ofReal (opn (Matrix.of g) ^ N1H k r))
  rw [sigma_mul hσ hx₀ hg, inner_iso hσ hx₀]
  have h1 : opn (x₀ * Matrix.of g) ^ N1H k r ≤ opn x₀ ^ N1H k r * opn (Matrix.of g) ^ N1H k r := by
    rw [← Real.mul_rpow (opn_nonneg _) (opn_nonneg _)]
    exact Real.rpow_le_rpow (opn_nonneg _) (opn_mul _ _) nilradical_half_sum_nonneg
  calc ‖⟪w, σ (Matrix.of g) w⟫_ℂ‖ₑ * ENNReal.ofReal (opn (x₀ * Matrix.of g) ^ N1H k r)
      ≤ ‖⟪w, σ (Matrix.of g) w⟫_ℂ‖ₑ *
          (ENNReal.ofReal (opn x₀ ^ N1H k r) * ENNReal.ofReal (opn (Matrix.of g) ^ N1H k r)) := by
        gcongr
        rw [← ENNReal.ofReal_mul (Real.rpow_nonneg (opn_nonneg _) _)]
        exact ENNReal.ofReal_le_ofReal h1
    _ = _ := by ring

theorem coef_reprod (hσ : IsURepOn (Gr k r) σ) {μ : Measure (Mt k r)} {w : H}
    {α : Mat k r → ℂ} {Ω : Set (Mat k r)} (hΩG : Ω ⊆ Gr k r) (hsupp : ∀ y, α y ≠ 0 → y ∈ Ω)
    (hint : Integrable (fun g : Mt k r => α (Matrix.of g) • σ (Matrix.of g) w) μ)
    (hrep : ∫ g, α (Matrix.of g) • σ (Matrix.of g) w ∂μ = w) (u : H) {y : Mat k r}
    (hy : y ∈ Gr k r) :
    ⟪u, σ y w⟫_ℂ = ∫ t, α (Matrix.of t) * ⟪u, σ (y * Matrix.of t) w⟫_ℂ ∂μ := by
  calc ⟪u, σ y w⟫_ℂ = ⟪u, σ y (∫ g, α (Matrix.of g) • σ (Matrix.of g) w ∂μ)⟫_ℂ := by rw [hrep]
    _ = ⟪u, ∫ g, σ y (α (Matrix.of g) • σ (Matrix.of g) w) ∂μ⟫_ℂ := by
        rw [(σ y).integral_comp_comm hint]
    _ = ∫ g, ⟪u, σ y (α (Matrix.of g) • σ (Matrix.of g) w)⟫_ℂ ∂μ :=
        (integral_inner ((σ y).integrable_comp hint) u).symm
    _ = _ := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
        by_cases hα : α (Matrix.of t) = 0
        · simp [hα]
        · have ht := hΩG (hsupp _ hα)
          show ⟪u, σ y (α (Matrix.of t) • σ (Matrix.of t) w)⟫_ℂ =
            α (Matrix.of t) * ⟪u, σ (y * Matrix.of t) w⟫_ℂ
          rw [map_smul, inner_smul_right, sigma_mul hσ hy ht]

theorem pt_decay_core (hσ : IsURepOn (Gr k r) σ) {μ : Measure (Mt k r)}
    (hinv : ∀ s ∈ Gr k r, μ.map (lmulM s) = μ) {w : H}
    {α : Mat k r → ℂ} {Ω : Set (Mat k r)} {a : ℝ} (hΩ : IsCompact Ω) (hΩG : Ω ⊆ Gr k r)
    (hsupp : ∀ y, α y ≠ 0 → y ∈ Ω) (hbd : ∀ y, ‖α y‖ ≤ a)
    (hint : Integrable (fun g : Mt k r => α (Matrix.of g) • σ (Matrix.of g) w) μ)
    (hrep : ∫ g, α (Matrix.of g) • σ (Matrix.of g) w ∂μ = w) (u : H) :
    ∃ K : ℝ≥0∞, K ≠ ⊤ ∧ ∀ y ∈ Gr k r,
      ‖⟪u, σ y w⟫_ℂ‖ₑ * ENNReal.ofReal (opn y ^ N1H k r) ≤
        K * ∫⁻ g, ‖⟪u, σ (Matrix.of g) w⟫_ℂ‖ₑ * ENNReal.ofReal (opn (Matrix.of g) ^ N1H k r) ∂μ := by
  obtain ⟨B, hB⟩ := hΩ.exists_bound_of_continuousOn (opn_continuous (k := k) (r := r)).continuousOn
  set M := opn (Hpk k r) * opn (Hpk k r) * max B 0 with hMdef
  have hM : 0 ≤ M := mul_nonneg (mul_nonneg (opn_nonneg _) (opn_nonneg _)) (le_max_right _ _)
  have hMt : ∀ t ∈ Ω, opn t⁻¹ ≤ M := by
    intro t ht
    refine (opn_inv_le (hΩG ht)).trans ?_
    have : opn t ≤ max B 0 := le_max_of_le_left ((Real.le_norm_self _).trans (hB t ht))
    rw [hMdef]
    exact mul_le_mul_of_nonneg_left this (mul_nonneg (opn_nonneg _) (opn_nonneg _))
  have ha : 0 ≤ a := (norm_nonneg _).trans (hbd 0)
  have hN := nilradical_half_sum_nonneg (k := k) (r := r)
  refine ⟨ENNReal.ofReal (a * M ^ N1H k r), ENNReal.ofReal_ne_top, fun y hy => ?_⟩
  rw [coef_reprod hσ hΩG hsupp hint hrep u hy]
  set F : Mt k r → ℝ≥0∞ := fun g =>
    ‖⟪u, σ (Matrix.of g) w⟫_ℂ‖ₑ * ENNReal.ofReal (opn (Matrix.of g) ^ N1H k r) with hF
  calc ‖∫ t, α (Matrix.of t) * ⟪u, σ (y * Matrix.of t) w⟫_ℂ ∂μ‖ₑ * ENNReal.ofReal (opn y ^ N1H k r)
      ≤ (∫⁻ t, ‖α (Matrix.of t) * ⟪u, σ (y * Matrix.of t) w⟫_ℂ‖ₑ ∂μ) *
          ENNReal.ofReal (opn y ^ N1H k r) := by
        gcongr
        exact enorm_integral_le_lintegral_enorm _
    _ = ∫⁻ t, ‖α (Matrix.of t) * ⟪u, σ (y * Matrix.of t) w⟫_ℂ‖ₑ *
          ENNReal.ofReal (opn y ^ N1H k r) ∂μ :=
        (lintegral_mul_const' _ _ ENNReal.ofReal_ne_top).symm
    _ ≤ ∫⁻ t, ENNReal.ofReal (a * M ^ N1H k r) * F (lmulM y t) ∂μ := by
        apply lintegral_mono
        intro t
        show ‖α (Matrix.of t) * ⟪u, σ (y * Matrix.of t) w⟫_ℂ‖ₑ * ENNReal.ofReal (opn y ^ N1H k r) ≤
          ENNReal.ofReal (a * M ^ N1H k r) * (‖⟪u, σ (y * Matrix.of t) w⟫_ℂ‖ₑ *
            ENNReal.ofReal (opn (y * Matrix.of t) ^ N1H k r))
        by_cases hα : α (Matrix.of t) = 0
        · simp [hα]
        · have htΩ := hsupp _ hα
          have ht := hΩG htΩ
          have h1 : opn y ^ N1H k r ≤ opn (y * Matrix.of t) ^ N1H k r * M ^ N1H k r := by
            rw [← Real.mul_rpow (opn_nonneg _) hM]
            refine Real.rpow_le_rpow (opn_nonneg _) ?_ hN
            exact (opn_le_mul_inv y ht).trans
              (mul_le_mul_of_nonneg_left (hMt _ htΩ) (opn_nonneg _))
          rw [← ofReal_norm, ← ofReal_norm,
            ← ENNReal.ofReal_mul (norm_nonneg _),
            ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
          apply ENNReal.ofReal_le_ofReal
          rw [norm_mul]
          calc ‖α (Matrix.of t)‖ * ‖⟪u, σ (y * Matrix.of t) w⟫_ℂ‖ * opn y ^ N1H k r
              ≤ a * ‖⟪u, σ (y * Matrix.of t) w⟫_ℂ‖ *
                  (opn (y * Matrix.of t) ^ N1H k r * M ^ N1H k r) := by
                exact mul_le_mul (mul_le_mul_of_nonneg_right (hbd _) (norm_nonneg _)) h1
                  (Real.rpow_nonneg (opn_nonneg _) _) (mul_nonneg ha (norm_nonneg _))
            _ = a * M ^ N1H k r * (‖⟪u, σ (y * Matrix.of t) w⟫_ℂ‖ *
                  opn (y * Matrix.of t) ^ N1H k r) := by ring
    _ = ENNReal.ofReal (a * M ^ N1H k r) * ∫⁻ t, F t ∂μ := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lint_lmul hy (hinv y hy)]

end Decay

def PtDecay : Prop :=
  ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (u : Fin k → ℝ) (v : Fin (k - 1) → ℝ)
    (b : Fin (2 * r + 2) → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : Mat k r → (H →L[ℂ] H)) (Vp : Type) [NormedAddCommGroup Vp] [InnerProductSpace ℂ Vp]
    [FiniteDimensional ℂ Vp] (π : Mat k r → (Vp →L[ℂ] Vp)) (w : H) (μG μS ν μW μN : Measure (Mt k r)),
    Hyp k r z c u v b σ π w μG μS ν μW μN →
    Formalism.L2.SG.HCReprodM.HCReprodDSm → CoefWeightedLoc → ∀ x₀ ∈ Gr k r,
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y ∈ Gr k r, ‖⟪σ x₀ w, σ y w⟫_ℂ‖ * opn y ^ N1H k r ≤ C

theorem ptDecay_of (hSG : SigmaG) (hD : Decay) (hRG : ReprodG) : PtDecay := by
  intro k r z c u v b H _ _ _ σ Vp _ _ _ π w μG μS ν μW μN hH hR hC x₀ hx₀
  have hdec := hD hC k r z c u v b H σ Vp π w μG μS ν μW μN hH
  obtain ⟨α, Ω, a, hΩ, hΩG, _, hsupp, hbd, hint, hrep⟩ :=
    hRG hR k r z c u v b H σ Vp π w μG μS ν μW μN hH
  obtain ⟨_, hDS, _, _, hμG, _⟩ := hH
  have hσ : IsURepOn (Gr k r) σ := hSG k r _ _ H σ hDS
  obtain ⟨_, _, hconc, hinv⟩ := hμG
  obtain ⟨K, hK, hbound⟩ := pt_decay_core hσ hinv hΩ hΩG hsupp hbd hint hrep (σ x₀ w)
  have htr := coef_weighted_transl hσ hconc hinv w hx₀
  set D := ∫⁻ g, ‖⟪w, σ (Matrix.of g) w⟫_ℂ‖ₑ * ENNReal.ofReal (opn (Matrix.of g) ^ N1H k r) ∂μG
  have hfin : K * (ENNReal.ofReal (opn x₀ ^ N1H k r) * D) ≠ ⊤ :=
    ENNReal.mul_ne_top hK (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hdec.ne)
  refine ⟨(K * (ENNReal.ofReal (opn x₀ ^ N1H k r) * D)).toReal, ENNReal.toReal_nonneg, fun y hy => ?_⟩
  have hE : ‖⟪σ x₀ w, σ y w⟫_ℂ‖ₑ * ENNReal.ofReal (opn y ^ N1H k r) ≤
      K * (ENNReal.ofReal (opn x₀ ^ N1H k r) * D) := (hbound y hy).trans (by gcongr)
  have hnn : 0 ≤ ‖⟪σ x₀ w, σ y w⟫_ℂ‖ * opn y ^ N1H k r :=
    mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (opn_nonneg _) _)
  rw [← ENNReal.toReal_ofReal hnn, ENNReal.ofReal_mul (norm_nonneg _), ofReal_norm]
  exact ENNReal.toReal_mono hfin hE

end WlocSk.PtD
