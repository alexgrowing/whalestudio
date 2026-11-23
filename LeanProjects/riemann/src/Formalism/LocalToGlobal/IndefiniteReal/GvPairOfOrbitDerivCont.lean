import Formalism.LocalToGlobal.IndefiniteReal.DKerHasCompactSupport

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory Matrix
open Formalism.L2.Theta Formalism.IndefR.Mult
open Filter Topology Set Metric
open scoped ContDiff TensorProduct

namespace Formalism.IndefR.SchurOrthogonalityAlt

section GenAdd

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

open PI.UpqRep PI.KFinSmoothW
open scoped InnerProductSpace

variable {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

theorem gp_lie_neg {Z : Matrix (Fin n) (Fin n) ℂ} (hZ : Zᴴ * Jm ε + Jm ε * Z = 0) :
    (-Z)ᴴ * Jm ε + Jm ε * (-Z) = 0 := by
  rw [Matrix.conjTranspose_neg, Matrix.neg_mul, Matrix.mul_neg, ← neg_add, hZ, neg_zero]

theorem gp_inner_inv {τ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hτ : IsURepOn (UJset ε) τ)
    {Z : Matrix (Fin n) (Fin n) ℂ} (hZ : Zᴴ * Jm ε + Jm ε * Z = 0) (t : ℝ) (u v : H) :
    ⟪u, τ (NormedSpace.exp (t • Z)) v⟫_ℂ = ⟪τ (NormedSpace.exp (t • -Z)) u, v⟫_ℂ := by
  have hm := expS_mem (-Z) (gp_lie_neg hZ) t
  have hp := expS_mem Z hZ t
  let Li : H →ₗᵢ[ℂ] H := { toLinearMap := (τ (NormedSpace.exp (t • -Z))).toLinearMap, norm_map' := hτ.2.1 _ hm }
  have h1 := Li.inner_map_map u (τ (NormedSpace.exp (t • Z)) v)
  have h2 : τ (NormedSpace.exp (t • -Z)) (τ (NormedSpace.exp (t • Z)) v) = v := by
    have h3 := hτ.1.2 _ hm _ hp
    rw [expS_neg_mul, hτ.1.1] at h3
    exact (congrArg (fun T : H →L[ℂ] H => T v) h3).symm
  rw [← h1]
  show ⟪τ (NormedSpace.exp (t • -Z)) u, τ (NormedSpace.exp (t • -Z)) (τ (NormedSpace.exp (t • Z)) v)⟫_ℂ = _
  rw [h2]

theorem gp_pair_deriv {τ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hτ : IsURepOn (UJset ε) τ)
    {Ψ : Matrix (Fin n) (Fin n) ℂ → ℂ} (hΨ : ContDiff ℝ ∞ Ψ) (hΨc : HasCompactSupport Ψ)
    {Z : Matrix (Fin n) (Fin n) ℂ} (hZ : Zᴴ * Jm ε + Jm ε * Z = 0) (x v d : H)
    (hd : HasDerivAt (fun t : ℝ => τ (NormedSpace.exp (t • Z)) v) d 0) :
    ⟪gv ε τ Ψ x, d⟫_ℂ = ⟪gv ε τ (dKer (-Z) Ψ) x, v⟫_ℂ := by
  have h1 : HasDerivAt (fun t : ℝ => ⟪gv ε τ Ψ x, τ (NormedSpace.exp (t • Z)) v⟫_ℂ) ⟪gv ε τ Ψ x, d⟫_ℂ 0 :=
    ((innerSL ℂ (gv ε τ Ψ x)).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0 hd
  have hf := hasDerivAt_tau_gv hτ hΨ hΨc (gp_lie_neg hZ) x
  have h2' := (((innerSL ℂ v).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0 hf).star
  have e2 : ∀ a : H, star ⟪v, a⟫_ℂ = ⟪a, v⟫_ℂ := fun a => by rw [← starRingEnd_apply, inner_conj_symm]
  have h2 : HasDerivAt (fun t : ℝ => ⟪τ (NormedSpace.exp (t • -Z)) (gv ε τ Ψ x), v⟫_ℂ)
      ⟪gv ε τ (dKer (-Z) Ψ) x, v⟫_ℂ 0 := by
    have h3 : HasDerivAt (fun t : ℝ => star ⟪v, τ (NormedSpace.exp (t • -Z)) (gv ε τ Ψ x)⟫_ℂ)
        (star ⟪v, gv ε τ (dKer (-Z) Ψ) x⟫_ℂ) 0 := h2'
    simpa only [e2] using h3
  have e : (fun t : ℝ => ⟪gv ε τ Ψ x, τ (NormedSpace.exp (t • Z)) v⟫_ℂ) =
      fun t : ℝ => ⟪τ (NormedSpace.exp (t • -Z)) (gv ε τ Ψ x), v⟫_ℂ :=
    funext fun t => gp_inner_inv hτ hZ t _ _
  rw [e] at h1
  exact h1.unique h2

theorem gp_gv_add {τ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hτ : IsURepOn (UJset ε) τ)
    {A B : Matrix (Fin n) (Fin n) ℂ → ℂ} (hA : Continuous A) (hAc : HasCompactSupport A)
    (hB : Continuous B) (hBc : HasCompactSupport B) (x : H) :
    gv ε τ (fun m => A m + B m) x = gv ε τ A x + gv ε τ B x := by
  unfold gv
  rw [← integral_add (gvS_integrable hτ hA hAc x) (gvS_integrable hτ hB hBc x)]
  congr 1
  funext h
  rw [add_smul]

theorem gp_deriv_add {τ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hτ : IsURepOn (UJset ε) τ)
    {Z₁ Z₂ : Matrix (Fin n) (Fin n) ℂ} (h₁ : Z₁ᴴ * Jm ε + Jm ε * Z₁ = 0) (h₂ : Z₂ᴴ * Jm ε + Jm ε * Z₂ = 0)
    {v d₁ d₂ d : H} (hd₁ : HasDerivAt (fun t : ℝ => τ (NormedSpace.exp (t • Z₁)) v) d₁ 0)
    (hd₂ : HasDerivAt (fun t : ℝ => τ (NormedSpace.exp (t • Z₂)) v) d₂ 0)
    (hd : HasDerivAt (fun t : ℝ => τ (NormedSpace.exp (t • (Z₁ + Z₂))) v) d 0) : d = d₁ + d₂ := by
  have h12 : (Z₁ + Z₂)ᴴ * Jm ε + Jm ε * (Z₁ + Z₂) = 0 := by
    rw [conjTranspose_add, Matrix.add_mul, Matrix.mul_add, add_add_add_comm, h₁, h₂, add_zero]
  have hker : ∀ {Ψ : Matrix (Fin n) (Fin n) ℂ → ℂ}, ContDiff ℝ ∞ Ψ → HasCompactSupport Ψ → ∀ x : H,
      ⟪gv ε τ Ψ x, d - (d₁ + d₂)⟫_ℂ = 0 := by
    intro Ψ hΨ hΨc x
    have e : dKer (-(Z₁ + Z₂)) Ψ = fun m => dKer (-Z₁) Ψ m + dKer (-Z₂) Ψ m := by
      funext m
      simp only [dKer, neg_neg, Matrix.add_mul, map_add]
    have hc1 := dKer_contDiff (Z := -Z₁) hΨ
    have hc2 := dKer_contDiff (Z := -Z₂) hΨ
    rw [inner_sub_right, inner_add_right, gp_pair_deriv hτ hΨ hΨc h12 x v d hd,
      gp_pair_deriv hτ hΨ hΨc h₁ x v d₁ hd₁, gp_pair_deriv hτ hΨ hΨc h₂ x v d₂ hd₂, e,
      gp_gv_add hτ hc1.continuous (dKer_hasCompactSupport hΨc) hc2.continuous (dKer_hasCompactSupport hΨc),
      inner_add_left, sub_self]
  set a := d - (d₁ + d₂) with ha
  obtain ⟨Φ, hΦ, hΦc, -, hle⟩ := PI.KFinSmoothW.dense_weak_vectors n ε H τ hτ (ℂ ∙ a) inferInstance
  have h0 := hker hΦ hΦc a
  have h1 := hle a (Submodule.mem_span_singleton_self a)
  have h2 : ‖gv ε τ Φ a - a‖ ^ 2 = ‖gv ε τ Φ a‖ ^ 2 + ‖a‖ ^ 2 := by
    rw [@norm_sub_sq ℂ, h0]; simp
  have h3 : ‖a‖ ^ 2 ≤ 0 := by
    nlinarith [norm_nonneg (gv ε τ Φ a - a), norm_nonneg a, sq_nonneg ‖gv ε τ Φ a‖]
  have h4 : a = 0 := norm_eq_zero.1 ((pow_eq_zero_iff two_ne_zero).1 (le_antisymm h3 (sq_nonneg _)))
  rw [ha] at h4
  exact (sub_eq_zero.1 h4)

end GenAdd

section GvPairSec

attribute [local instance] Formalism.BasicNotions.Host.cmStar Matrix.normedAddCommGroup Matrix.normedSpace

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar}

theorem gp_exp_mem (τ : D.what₂.Tau) {X : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hX : X ∈ lieAt V τ) (t : ℝ) :
    NormedSpace.exp (t • X) ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ) := by
  have hl : (t • X)ᴴ * gramAt D V τ + gramAt D V τ * (t • X) = 0 := by
    have h := CCRuleCW.lie_smul (gramAt D V τ) X hX t
    simpa only [Complex.coe_smul] using h
  exact CCRuleCW.exp_mem_UH (gramAt D V τ) (t • X) hl

theorem gp_rep_norm (M : DSModel V S) (τ : D.what₂.Tau) {a : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (ha : a ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) (x : M.H τ) : ‖M.rep τ a x‖ = ‖x‖ := by
  exact (M.ds τ).2.2.1.2.1 _ (conj_mem M τ ha) x

theorem gp_rep_one (M : DSModel V S) (τ : D.what₂.Tau) : M.rep τ 1 = 1 := by
  show M.σ τ (M.fr τ * 1 * (M.fr τ)⁻¹) = 1
  rw [Matrix.mul_one, fr_mul_inv]
  exact (M.ds τ).2.2.1.1.1

theorem gp_exp_split {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) (a b : ℝ) :
    NormedSpace.exp ((a + b) • X) = NormedSpace.exp (a • X) * NormedSpace.exp (b • X) := by
  rw [add_smul]
  exact Matrix.exp_add_of_commute _ _ (((Commute.refl X).smul_left a).smul_right b)

theorem gp_sv_contDiff1 {M : DSModel V S} {τ : D.what₂.Tau} {v : M.H τ}
    (hv : SmoothVec (lieAt V τ) (M.rep τ) v) {X : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hX : X ∈ lieAt V τ) :
    ContDiff ℝ ∞ (fun s : ℝ => M.rep τ (NormedSpace.exp (s • X)) v) := by
  have h := (hv 1 ![X] (fun i => by rw [Fin.fin_one_eq_zero i]; simpa using hX)).comp
    (contDiff_pi.2 fun _ : Fin 1 => contDiff_id : ContDiff ℝ ∞ fun s : ℝ => fun _ : Fin 1 => s)
  convert h using 1
  funext s
  simp

private theorem rep_mul_of_mem_UH (M : DSModel V S) (τ : D.what₂.Tau) {a b : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (ha : a ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) (hb : b ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) (x : M.H τ) :
    M.rep τ (a * b) x = M.rep τ a (M.rep τ b x) := by
  have h := (M.ds τ).2.2.1.1.2 _ (conj_mem M τ ha) _ (conj_mem M τ hb)
  have e : M.fr τ * (a * b) * (M.fr τ)⁻¹ = (M.fr τ * a * (M.fr τ)⁻¹) * (M.fr τ * b * (M.fr τ)⁻¹) := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (M.fr τ)⁻¹ (M.fr τ), fr_inv_mul, Matrix.one_mul]
  show M.σ τ (M.fr τ * (a * b) * (M.fr τ)⁻¹) x =
    M.σ τ (M.fr τ * a * (M.fr τ)⁻¹) (M.σ τ (M.fr τ * b * (M.fr τ)⁻¹) x)
  rw [e, h, ContinuousLinearMap.comp_apply]

theorem gp_sv_hasDerivAt {M : DSModel V S} {τ : D.what₂.Tau} {v : M.H τ}
    (hv : SmoothVec (lieAt V τ) (M.rep τ) v) {X : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hX : X ∈ lieAt V τ)
    (t0 : ℝ) :
    HasDerivAt (fun t : ℝ => M.rep τ (NormedSpace.exp (t • X)) v)
      (M.rep τ (NormedSpace.exp (t0 • X)) (dRep (M.rep τ) X v)) t0 := by
  have hd : HasDerivAt (fun s : ℝ => M.rep τ (NormedSpace.exp (s • X)) v) (dRep (M.rep τ) X v) 0 :=
    ((gp_sv_contDiff1 hv hX).differentiable (by simp) 0).hasDerivAt
  have hd2 : HasDerivAt (fun s : ℝ => M.rep τ (NormedSpace.exp ((s - t0) • X)) v) (dRep (M.rep τ) X v) t0 :=
    HasDerivAt.comp_sub_const (f := fun s : ℝ => M.rep τ (NormedSpace.exp (s • X)) v) t0 t0
      (by rw [sub_self]; exact hd)
  have hd3 := ((M.rep τ (NormedSpace.exp (t0 • X))).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t0 hd2
  refine hd3.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_)
  show M.rep τ (NormedSpace.exp (s • X)) v =
    M.rep τ (NormedSpace.exp (t0 • X)) (M.rep τ (NormedSpace.exp ((s - t0) • X)) v)
  rw [← rep_mul_of_mem_UH M τ (gp_exp_mem τ hX t0) (gp_exp_mem τ hX (s - t0)), ← gp_exp_split X t0 (s - t0),
    add_sub_cancel]

theorem gp_sv_diffAt {M : DSModel V S} {τ : D.what₂.Tau} {v : M.H τ}
    (hv : SmoothVec (lieAt V τ) (M.rep τ) v) {X : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hX : X ∈ lieAt V τ) :
    DifferentiableAt ℝ (fun s : ℝ => M.rep τ (NormedSpace.exp (s • X)) v) 0 := (gp_sv_contDiff1 hv hX).differentiable (by simp) 0

theorem gp_sv_add {M : DSModel V S} {τ : D.what₂.Tau} {v w : M.H τ}
    (hv : SmoothVec (lieAt V τ) (M.rep τ) v) (hw : SmoothVec (lieAt V τ) (M.rep τ) w) :
    SmoothVec (lieAt V τ) (M.rep τ) (v + w) := by
  intro k Xs hXs
  simpa only [map_add] using (hv k Xs hXs).add (hw k Xs hXs)

theorem gp_sv_smul {M : DSModel V S} {τ : D.what₂.Tau} (c : ℂ) {v : M.H τ}
    (hv : SmoothVec (lieAt V τ) (M.rep τ) v) : SmoothVec (lieAt V τ) (M.rep τ) (c • v) := by
  intro k Xs hXs
  simpa only [map_smul] using (hv k Xs hXs).const_smul c

theorem gp_sv_zero {M : DSModel V S} {τ : D.what₂.Tau} : SmoothVec (lieAt V τ) (M.rep τ) (0 : M.H τ) := by
  intro k Xs hXs
  simp only [map_zero]
  exact contDiff_const

theorem gp_sv_of_mem {M : DSModel V S} {τ : D.what₂.Tau} {w : M.H τ} (hw : w ∈ M.sm τ) :
    SmoothVec (lieAt V τ) (M.rep τ) w := by
  have hw' : w ∈ Submodule.span ℂ {w | SmoothVec (lieAt V τ) (M.rep τ) w} := hw
  clear hw
  induction hw' using Submodule.span_induction with
  | mem x hx => exact hx
  | zero => exact gp_sv_zero
  | add x y _ _ hx hy => exact gp_sv_add hx hy
  | smul c x _ hx => exact gp_sv_smul c hx

theorem gp_sv_sigma (M : DSModel V S) (τ : D.what₂.Tau) (h : PI.UpqRep.UJ (M.ε τ)) {w : M.H τ}
    (hw : SmoothVec (lieAt V τ) (M.rep τ) w) :
    SmoothVec (lieAt V τ) (M.rep τ) (M.σ τ (PI.UpqRep.umat h) w) := by
  obtain ⟨g, hg⟩ := exists_gt_of_UJ M τ (PI.KFinSmoothW.umat_mem_UJset h)
  have h1 := smoothVec_rep M τ g hw
  rwa [hg] at h1

theorem gp_prod_snoc {n k : ℕ} (Xs : Fin k → Matrix (Fin n) (Fin n) ℂ) (X : Matrix (Fin n) (Fin n) ℂ)
    (t : Fin k → ℝ) (s : ℝ) :
    (List.ofFn fun i : Fin (k + 1) => NormedSpace.exp ((Fin.snoc t s : Fin (k + 1) → ℝ) i •
        (Fin.snoc Xs X : Fin (k + 1) → Matrix (Fin n) (Fin n) ℂ) i)).prod =
      (List.ofFn fun i : Fin k => NormedSpace.exp (t i • Xs i)).prod * NormedSpace.exp (s • X) := by
  rw [List.ofFn_succ', List.prod_concat]
  simp only [Fin.snoc_castSucc, Fin.snoc_last]

theorem gp_snoc_hasDerivAt {k : ℕ} (t : Fin k → ℝ) (s : ℝ) :
    HasDerivAt (fun u : ℝ => (Fin.snoc t u : Fin (k + 1) → ℝ)) (Pi.single (Fin.last k) 1) s := by
  rw [hasDerivAt_pi]
  intro i
  induction i using Fin.lastCases with
  | last =>
    simp only [Fin.snoc_last, Pi.single_eq_same]
    exact hasDerivAt_id' s
  | cast j =>
    simp only [Fin.snoc_castSucc]
    rw [Pi.single_eq_of_ne (Fin.castSucc_lt_last j).ne]
    exact hasDerivAt_const s (t j)

theorem gp_snoc_contDiff {k : ℕ} : ContDiff ℝ ∞ (fun t : Fin k → ℝ => (Fin.snoc t 0 : Fin (k + 1) → ℝ)) := by
  refine contDiff_pi.2 fun i => ?_
  induction i using Fin.lastCases with
  | last =>
    simp only [Fin.snoc_last]
    exact contDiff_const
  | cast j =>
    simp only [Fin.snoc_castSucc]
    exact contDiff_pi.1 contDiff_id j

private theorem mul_mem_UH_indefinite_real {τ : D.what₂.Tau} {a b : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (ha : a ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) (hb : b ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) :
    a * b ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ) := by
  have ha' : aᴴ * gramAt D V τ * a = gramAt D V τ := ha
  have hb' : bᴴ * gramAt D V τ * b = gramAt D V τ := hb
  show (a * b)ᴴ * gramAt D V τ * (a * b) = gramAt D V τ
  calc (a * b)ᴴ * gramAt D V τ * (a * b) = bᴴ * (aᴴ * gramAt D V τ * a) * b := by
        simp only [conjTranspose_mul, Matrix.mul_assoc]
    _ = gramAt D V τ := by rw [ha', hb']

private theorem list_prod_mem_UH {τ : D.what₂.Tau} :
    ∀ l : List (Matrix (Fin V.rank) (Fin V.rank) ℂ), (∀ a ∈ l, a ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) →
      l.prod ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ) := by
  intro l
  induction l with
  | nil =>
    intro _
    show (1 : Matrix (Fin V.rank) (Fin V.rank) ℂ)ᴴ * gramAt D V τ * 1 = gramAt D V τ
    simp
  | cons a l ih =>
    intro h
    rw [List.prod_cons]
    exact mul_mem_UH_indefinite_real (h a (by simp)) (ih fun b hb => h b (by simp [hb]))

theorem gp_sv_dRep {M : DSModel V S} {τ : D.what₂.Tau} {v : M.H τ}
    (hv : SmoothVec (lieAt V τ) (M.rep τ) v) {X : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hX : X ∈ lieAt V τ) :
    SmoothVec (lieAt V τ) (M.rep τ) (dRep (M.rep τ) X v) := by
  intro k Xs hXs
  have hXs' : ∀ i, (Fin.snoc Xs X : Fin (k + 1) → Matrix (Fin V.rank) (Fin V.rank) ℂ) i ∈ lieAt V τ := by
    intro i
    induction i using Fin.lastCases with
    | last => simpa only [Fin.snoc_last] using hX
    | cast j => simpa only [Fin.snoc_castSucc] using hXs j
  have hF := hv (k + 1) (Fin.snoc Xs X) hXs'
  have hdF := (contDiff_infty_iff_fderiv.1 hF).2
  have key : ∀ t : Fin k → ℝ,
      M.rep τ ((List.ofFn fun i : Fin k => NormedSpace.exp (t i • Xs i)).prod) (dRep (M.rep τ) X v) =
        fderiv ℝ (fun u : Fin (k + 1) → ℝ => M.rep τ ((List.ofFn fun i : Fin (k + 1) =>
          NormedSpace.exp (u i • (Fin.snoc Xs X : Fin (k + 1) → Matrix (Fin V.rank) (Fin V.rank) ℂ) i)).prod) v)
          (Fin.snoc t 0) (Pi.single (Fin.last k) 1) := by
    intro t
    have hPm : (List.ofFn fun i : Fin k => NormedSpace.exp (t i • Xs i)).prod ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ) := by
      refine list_prod_mem_UH _ ?_
      intro a ha
      simp only [List.mem_ofFn] at ha
      obtain ⟨i, rfl⟩ := ha
      exact gp_exp_mem τ (hXs i) (t i)
    have h1 := ((hF.differentiable (by simp)) (Fin.snoc t 0)).hasFDerivAt.comp_hasDerivAt (0 : ℝ)
      (gp_snoc_hasDerivAt t 0)
    have h3 := ((M.rep τ ((List.ofFn fun i : Fin k => NormedSpace.exp (t i • Xs i)).prod)).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt
      (0 : ℝ) (gp_sv_diffAt hv hX).hasDerivAt
    have h2 := h3.congr_of_eventuallyEq (f₁ := fun s : ℝ => M.rep τ ((List.ofFn fun i : Fin (k + 1) =>
          NormedSpace.exp ((Fin.snoc t s : Fin (k + 1) → ℝ) i •
            (Fin.snoc Xs X : Fin (k + 1) → Matrix (Fin V.rank) (Fin V.rank) ℂ) i)).prod) v)
      (Filter.Eventually.of_forall fun s => by
        show _ = M.rep τ ((List.ofFn fun i : Fin k => NormedSpace.exp (t i • Xs i)).prod)
          (M.rep τ (NormedSpace.exp (s • X)) v)
        beta_reduce
        rw [gp_prod_snoc, ← rep_mul_of_mem_UH M τ hPm (gp_exp_mem τ hX s)])
    exact h2.unique h1
  convert (hdF.comp gp_snoc_contDiff).clm_apply (contDiff_const (c := (Pi.single (Fin.last k) 1 : Fin (k + 1) → ℝ))) using 1
  funext t
  exact key t

theorem gp_sv_foldr {M : DSModel V S} {τ : D.what₂.Tau} :
    ∀ (l : List (Matrix (Fin V.rank) (Fin V.rank) ℂ)), (∀ X ∈ l, X ∈ lieAt V τ) → ∀ {v : M.H τ},
      SmoothVec (lieAt V τ) (M.rep τ) v → SmoothVec (lieAt V τ) (M.rep τ) (l.foldr (dRep (M.rep τ)) v)
  | [], _, _, hv => hv
  | X :: l, hl, _, hv => by
    rw [List.foldr_cons]
    exact gp_sv_dRep (gp_sv_foldr l (fun Y hY => hl Y (List.mem_cons_of_mem _ hY)) hv) (hl X (by simp))

theorem gp_dRep_add {M : DSModel V S} {τ : D.what₂.Tau} {v w : M.H τ}
    (hv : SmoothVec (lieAt V τ) (M.rep τ) v) (hw : SmoothVec (lieAt V τ) (M.rep τ) w)
    {X : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hX : X ∈ lieAt V τ) :
    dRep (M.rep τ) X (v + w) = dRep (M.rep τ) X v + dRep (M.rep τ) X w := by
  show deriv (fun t : ℝ => M.rep τ (NormedSpace.exp (t • X)) (v + w)) 0 = _
  simp only [map_add]
  exact deriv_add (gp_sv_diffAt hv hX) (gp_sv_diffAt hw hX)

theorem gp_dRep_smul {M : DSModel V S} {τ : D.what₂.Tau} (c : ℂ) {v : M.H τ}
    (hv : SmoothVec (lieAt V τ) (M.rep τ) v) {X : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hX : X ∈ lieAt V τ) :
    dRep (M.rep τ) X (c • v) = c • dRep (M.rep τ) X v := by
  show deriv (fun t : ℝ => M.rep τ (NormedSpace.exp (t • X)) (c • v)) 0 = _
  simp only [map_smul]
  exact deriv_const_smul c (gp_sv_diffAt hv hX)

theorem gp_foldr_add {M : DSModel V S} {τ : D.what₂.Tau} :
    ∀ (l : List (Matrix (Fin V.rank) (Fin V.rank) ℂ)), (∀ X ∈ l, X ∈ lieAt V τ) → ∀ {v w : M.H τ},
      SmoothVec (lieAt V τ) (M.rep τ) v → SmoothVec (lieAt V τ) (M.rep τ) w →
        l.foldr (dRep (M.rep τ)) (v + w) = l.foldr (dRep (M.rep τ)) v + l.foldr (dRep (M.rep τ)) w
  | [], _, _, _, _, _ => rfl
  | X :: l, hl, _, _, hv, hw => by
    have hl' : ∀ Y ∈ l, Y ∈ lieAt V τ := fun Y hY => hl Y (List.mem_cons_of_mem _ hY)
    rw [List.foldr_cons, List.foldr_cons, List.foldr_cons, gp_foldr_add l hl' hv hw]
    exact gp_dRep_add (gp_sv_foldr l hl' hv) (gp_sv_foldr l hl' hw) (hl X (by simp))

theorem gp_foldr_smul {M : DSModel V S} {τ : D.what₂.Tau} (c : ℂ) :
    ∀ (l : List (Matrix (Fin V.rank) (Fin V.rank) ℂ)), (∀ X ∈ l, X ∈ lieAt V τ) → ∀ {v : M.H τ},
      SmoothVec (lieAt V τ) (M.rep τ) v → l.foldr (dRep (M.rep τ)) (c • v) = c • l.foldr (dRep (M.rep τ)) v
  | [], _, _, _ => rfl
  | X :: l, hl, _, hv => by
    have hl' : ∀ Y ∈ l, Y ∈ lieAt V τ := fun Y hY => hl Y (List.mem_cons_of_mem _ hY)
    rw [List.foldr_cons, List.foldr_cons, gp_foldr_smul c l hl' hv]
    exact gp_dRep_smul c (gp_sv_foldr l hl' hv) (hl X (by simp))

def gpSv (M : DSModel V S) (τ : D.what₂.Tau) : Submodule ℂ (M.H τ) where
  carrier := {w | SmoothVec (lieAt V τ) (M.rep τ) w}
  add_mem' hv hw := gp_sv_add hv hw
  zero_mem' := gp_sv_zero
  smul_mem' c _ hv := gp_sv_smul c hv

def gpWords (M : DSModel V S) (τ : D.what₂.Tau) (L : List (List (Matrix (Fin V.rank) (Fin V.rank) ℂ)))
    (hL : ∀ l ∈ L, ∀ X ∈ l, X ∈ lieAt V τ) : gpSv M τ →ₗ[ℂ] (Fin L.length → M.H τ) where
  toFun v := fun i => (L.get i).foldr (dRep (M.rep τ)) (v : M.H τ)
  map_add' v w := funext fun i => gp_foldr_add (L.get i) (hL _ (List.get_mem L i)) v.2 w.2
  map_smul' c v := funext fun i => gp_foldr_smul c (L.get i) (hL _ (List.get_mem L i)) v.2

theorem gp_sob_rep (M : DSModel V S) (τ : D.what₂.Tau) {ℓ : M.H τ →ₗ[ℂ] ℂ}
    (hℓ : Sobolev₂ (lieAt V τ) (M.rep τ) ℓ) :
    ∃ (L : List (List (Matrix (Fin V.rank) (Fin V.rank) ℂ))) (_ : ∀ l ∈ L, ∀ X ∈ l, X ∈ lieAt V τ)
      (g : (Fin L.length → M.H τ) →L[ℂ] ℂ), ∀ v, SmoothVec (lieAt V τ) (M.rep τ) v →
        ℓ v = g (fun i => (L.get i).foldr (dRep (M.rep τ)) v) := by
  obtain ⟨L, C, hL, hC⟩ := hℓ
  set T := gpWords M τ L hL with hT
  set ℓW : gpSv M τ →ₗ[ℂ] ℂ := ℓ.comp (gpSv M τ).subtype with hℓW
  have hbd : ∀ v : gpSv M τ, ‖ℓW v‖ ≤ (|C| * L.length) * ‖T v‖ := by
    intro v
    have h1 := hC (v : M.H τ) v.2
    have hs : (L.map fun l => ‖l.foldr (dRep (M.rep τ)) (v : M.H τ)‖).sum ≤ L.length * ‖T v‖ := by
      have h3 := List.sum_le_card_nsmul (L.map fun l => ‖l.foldr (dRep (M.rep τ)) (v : M.H τ)‖) ‖T v‖ (by
        intro x hx
        obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hx
        obtain ⟨i, rfl⟩ := List.mem_iff_get.1 hl
        exact norm_le_pi_norm (T v) i)
      simpa [nsmul_eq_mul] using h3
    have h0 := sum_map_norm_nonneg (σ := M.rep τ) L (v : M.H τ)
    calc ‖ℓW v‖ = ‖ℓ v‖ := rfl
      _ ≤ C * (L.map fun l => ‖l.foldr (dRep (M.rep τ)) (v : M.H τ)‖).sum := h1
      _ ≤ |C| * (L.map fun l => ‖l.foldr (dRep (M.rep τ)) (v : M.H τ)‖).sum :=
          mul_le_mul_of_nonneg_right (le_abs_self C) h0
      _ ≤ |C| * (L.length * ‖T v‖) := mul_le_mul_of_nonneg_left hs (abs_nonneg C)
      _ = (|C| * L.length) * ‖T v‖ := by ring
  have hker : LinearMap.ker T ≤ LinearMap.ker ℓW := by
    intro v hv
    rw [LinearMap.mem_ker] at hv ⊢
    have h1 := hbd v
    rw [hv, norm_zero, mul_zero] at h1
    exact norm_le_zero_iff.1 h1
  set f0 : LinearMap.range T →ₗ[ℂ] ℂ :=
    ((LinearMap.ker T).liftQ ℓW hker).comp T.quotKerEquivRange.symm.toLinearMap with hf0def
  have hf0 : ∀ v : gpSv M τ, f0 ⟨T v, LinearMap.mem_range_self T v⟩ = ℓW v := by
    intro v
    rw [hf0def, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.quotKerEquivRange_symm_apply_image]
    rfl
  have hf0b : ∀ y : LinearMap.range T, ‖f0 y‖ ≤ (|C| * L.length) * ‖y‖ := by
    intro y
    obtain ⟨v, hv⟩ := LinearMap.mem_range.1 y.2
    have ey : y = ⟨T v, LinearMap.mem_range_self T v⟩ := Subtype.ext hv.symm
    rw [ey, hf0 v]
    exact hbd v
  obtain ⟨g, hg, -⟩ := exists_extension_norm_eq (LinearMap.range T) (f0.mkContinuous _ hf0b)
  refine ⟨L, hL, g, fun v hv => ?_⟩
  have h1 := hg ⟨T ⟨v, hv⟩, LinearMap.mem_range_self T _⟩
  show ℓ v = g (T ⟨v, hv⟩)
  rw [h1, LinearMap.mkContinuous_apply, hf0]
  rfl

theorem gp_dRep_int (M : DSModel V S) (τ : D.what₂.Tau) {Φ : Matrix (Fin V.rank) (Fin V.rank) ℂ → ℂ}
    (hΦ : Continuous Φ) (hΦc : HasCompactSupport Φ) {X : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hX : X ∈ lieAt V τ) {G : PI.UpqRep.UJ (M.ε τ) → M.H τ} (hG : Continuous G)
    (hG' : Continuous fun h => dRep (M.rep τ) X (G h))
    (hsv : ∀ h, SmoothVec (lieAt V τ) (M.rep τ) (G h)) :
    dRep (M.rep τ) X (∫ h, Φ (PI.UpqRep.umat h) • G h ∂(PI.UpqRep.muG (M.ε τ))) =
      ∫ h, Φ (PI.UpqRep.umat h) • dRep (M.rep τ) X (G h) ∂(PI.UpqRep.muG (M.ε τ)) := by
  have : CompleteSpace (M.H τ) := (M.ds τ).1
  have hum : Continuous (PI.UpqRep.umat : PI.UpqRep.UJ (M.ε τ) → Matrix (Fin V.rank) (Fin V.rank) ℂ) :=
    (PI.KFinSmoothW.Gard.umat_closedEmb (M.ε τ)).continuous
  have hΦu : Continuous (fun h : PI.UpqRep.UJ (M.ε τ) => Φ (PI.UpqRep.umat h)) := hΦ.comp hum
  have hΦuc : HasCompactSupport (fun h : PI.UpqRep.UJ (M.ε τ) => Φ (PI.UpqRep.umat h)) :=
    hΦc.comp_isClosedEmbedding (PI.KFinSmoothW.Gard.umat_closedEmb (M.ε τ))
  have hint : Integrable (fun h => Φ (PI.UpqRep.umat h) • G h) (PI.UpqRep.muG (M.ε τ)) :=
    (hΦu.smul hG).integrable_of_hasCompactSupport (hΦuc.smul_right (f' := G))
  have e1 : (fun t : ℝ => M.rep τ (NormedSpace.exp (t • X))
        (∫ h, Φ (PI.UpqRep.umat h) • G h ∂(PI.UpqRep.muG (M.ε τ)))) =
      fun t => ∫ h, Φ (PI.UpqRep.umat h) • M.rep τ (NormedSpace.exp (t • X)) (G h) ∂(PI.UpqRep.muG (M.ε τ)) := by
    funext t
    rw [← (M.rep τ (NormedSpace.exp (t • X))).integral_comp_comm hint]
    congr 1
    funext h
    exact map_smul _ _ _
  have hbi : Integrable (fun h => ‖Φ (PI.UpqRep.umat h)‖ * ‖dRep (M.rep τ) X (G h)‖) (PI.UpqRep.muG (M.ε τ)) :=
    (hΦu.norm.mul hG'.norm).integrable_of_hasCompactSupport (hΦuc.norm.mul_right)
  have hFm : ∀ᶠ t in 𝓝 (0 : ℝ), AEStronglyMeasurable
      (fun h => Φ (PI.UpqRep.umat h) • M.rep τ (NormedSpace.exp (t • X)) (G h)) (PI.UpqRep.muG (M.ε τ)) :=
    Eventually.of_forall fun t =>
      (hΦu.smul ((M.rep τ (NormedSpace.exp (t • X))).continuous.comp hG)).aestronglyMeasurable
  have hFi : Integrable (fun h => Φ (PI.UpqRep.umat h) • M.rep τ (NormedSpace.exp ((0 : ℝ) • X)) (G h))
      (PI.UpqRep.muG (M.ε τ)) :=
    (hΦu.smul ((M.rep τ (NormedSpace.exp ((0 : ℝ) • X))).continuous.comp hG)).integrable_of_hasCompactSupport
      (hΦuc.smul_right (f' := fun h => M.rep τ (NormedSpace.exp ((0 : ℝ) • X)) (G h)))
  have hF'm : AEStronglyMeasurable (fun h => Φ (PI.UpqRep.umat h) •
      M.rep τ (NormedSpace.exp ((0 : ℝ) • X)) (dRep (M.rep τ) X (G h))) (PI.UpqRep.muG (M.ε τ)) :=
    (hΦu.smul ((M.rep τ (NormedSpace.exp ((0 : ℝ) • X))).continuous.comp hG')).aestronglyMeasurable
  have hbd : ∀ᵐ h ∂(PI.UpqRep.muG (M.ε τ)), ∀ t ∈ ball (0 : ℝ) 1,
      ‖Φ (PI.UpqRep.umat h) • M.rep τ (NormedSpace.exp (t • X)) (dRep (M.rep τ) X (G h))‖ ≤
        ‖Φ (PI.UpqRep.umat h)‖ * ‖dRep (M.rep τ) X (G h)‖ := by
    refine Eventually.of_forall fun h t _ => le_of_eq ?_
    rw [norm_smul, gp_rep_norm M τ (gp_exp_mem τ hX t)]
  have hdiff : ∀ᵐ h ∂(PI.UpqRep.muG (M.ε τ)), ∀ t ∈ ball (0 : ℝ) 1,
      HasDerivAt (fun u : ℝ => Φ (PI.UpqRep.umat h) • M.rep τ (NormedSpace.exp (u • X)) (G h))
        (Φ (PI.UpqRep.umat h) • M.rep τ (NormedSpace.exp (t • X)) (dRep (M.rep τ) X (G h))) t :=
    Eventually.of_forall fun h t _ => (gp_sv_hasDerivAt (hsv h) hX t).const_smul (Φ (PI.UpqRep.umat h))
  have hD := (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := PI.UpqRep.muG (M.ε τ))
    (F := fun (t : ℝ) h => Φ (PI.UpqRep.umat h) • M.rep τ (NormedSpace.exp (t • X)) (G h))
    (F' := fun (t : ℝ) h => Φ (PI.UpqRep.umat h) • M.rep τ (NormedSpace.exp (t • X)) (dRep (M.rep τ) X (G h)))
    (x₀ := 0) (bound := fun h => ‖Φ (PI.UpqRep.umat h)‖ * ‖dRep (M.rep τ) X (G h)‖)
    (ball_mem_nhds (0 : ℝ) one_pos) hFm hFi hF'm hbd hbi hdiff).2
  have e0 : M.rep τ (NormedSpace.exp ((0 : ℝ) • X)) = 1 := by
    rw [zero_smul, NormedSpace.exp_zero, gp_rep_one]
  show deriv (fun t : ℝ => M.rep τ (NormedSpace.exp (t • X))
      (∫ h, Φ (PI.UpqRep.umat h) • G h ∂(PI.UpqRep.muG (M.ε τ)))) 0 = _
  rw [e1, hD.deriv, e0]
  rfl

def OrbitDerivCont : Prop :=
  ∀ {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (τ : D.what₂.Tau) (w : M.H τ),
    SmoothVec (lieAt V τ) (M.rep τ) w → ∀ l : List (Matrix (Fin V.rank) (Fin V.rank) ℂ),
      (∀ X ∈ l, X ∈ lieAt V τ) →
        Continuous fun h : PI.UpqRep.UJ (M.ε τ) => l.foldr (dRep (M.rep τ)) (M.σ τ (PI.UpqRep.umat h) w)

theorem gp_foldr_gvT (hK : OrbitDerivCont) (M : DSModel V S) (τ : D.what₂.Tau)
    {Φ : Matrix (Fin V.rank) (Fin V.rank) ℂ → ℂ} (hΦ : Continuous Φ) (hΦc : HasCompactSupport Φ) {w : M.H τ}
    (hw : SmoothVec (lieAt V τ) (M.rep τ) w) :
    ∀ l : List (Matrix (Fin V.rank) (Fin V.rank) ℂ), (∀ X ∈ l, X ∈ lieAt V τ) →
      l.foldr (dRep (M.rep τ)) (gvT M τ Φ w) =
        ∫ h, Φ (PI.UpqRep.umat h) • l.foldr (dRep (M.rep τ)) (M.σ τ (PI.UpqRep.umat h) w)
          ∂(PI.UpqRep.muG (M.ε τ))
  | [], _ => rfl
  | X :: l, hl => by
    have hl' : ∀ Y ∈ l, Y ∈ lieAt V τ := fun Y hY => hl Y (List.mem_cons_of_mem _ hY)
    have hX : X ∈ lieAt V τ := hl X (by simp)
    rw [List.foldr_cons, gp_foldr_gvT hK M τ hΦ hΦc hw l hl']
    exact gp_dRep_int M τ hΦ hΦc hX (hK M τ w hw l hl') (hK M τ w hw (X :: l) hl)
      (fun h => gp_sv_foldr l hl' (gp_sv_sigma M τ h hw))

theorem gvPair_of_orbitDerivCont (hK : OrbitDerivCont) : GvPair := by
  unfold GvPair
  intro D V S M τ Φ hΦ hΦc ℓ hℓ w hw
  have : CompleteSpace (M.H τ) := (M.ds τ).1
  have hsw : SmoothVec (lieAt V τ) (M.rep τ) w := gp_sv_of_mem hw
  obtain ⟨L, hL, g, hg⟩ := gp_sob_rep M τ hℓ
  have hum : Continuous (PI.UpqRep.umat : PI.UpqRep.UJ (M.ε τ) → Matrix (Fin V.rank) (Fin V.rank) ℂ) :=
    (PI.KFinSmoothW.Gard.umat_closedEmb (M.ε τ)).continuous
  have hΦu : Continuous (fun h : PI.UpqRep.UJ (M.ε τ) => Φ (PI.UpqRep.umat h)) := hΦ.continuous.comp hum
  have hΦuc : HasCompactSupport (fun h : PI.UpqRep.UJ (M.ε τ) => Φ (PI.UpqRep.umat h)) :=
    hΦc.comp_isClosedEmbedding (PI.KFinSmoothW.Gard.umat_closedEmb (M.ε τ))
  set T : M.H τ → (Fin L.length → M.H τ) := fun v i => (L.get i).foldr (dRep (M.rep τ)) v with hT
  have hTc : Continuous fun h : PI.UpqRep.UJ (M.ε τ) => T (M.σ τ (PI.UpqRep.umat h) w) :=
    continuous_pi fun i => hK M τ w hsw (L.get i) (hL _ (List.get_mem L i))
  have hint : Integrable (fun h => Φ (PI.UpqRep.umat h) • T (M.σ τ (PI.UpqRep.umat h) w))
      (PI.UpqRep.muG (M.ε τ)) :=
    (hΦu.smul hTc).integrable_of_hasCompactSupport
      (hΦuc.smul_right (f' := fun h => T (M.σ τ (PI.UpqRep.umat h) w)))
  have e1 : T (gvT M τ Φ w) =
      ∫ h, Φ (PI.UpqRep.umat h) • T (M.σ τ (PI.UpqRep.umat h) w) ∂(PI.UpqRep.muG (M.ε τ)) := by
    funext i
    have h1 := (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin L.length => M.H τ) i).integral_comp_comm hint
    rw [hT]
    simp only
    rw [gp_foldr_gvT hK M τ hΦ.continuous hΦc hsw (L.get i) (hL _ (List.get_mem L i))]
    exact h1
  rw [hg _ (gvT_smooth M τ hΦ hΦc w)]
  show g (T (gvT M τ Φ w)) = _
  rw [e1, ← g.integral_comp_comm hint]
  congr 1
  funext h
  rw [map_smul, smul_eq_mul, hg _ (gp_sv_sigma M τ h hsw)]

def gpTan (V : HSp D) (τ : D.what₂.Tau) : Submodule ℝ (Matrix (Fin V.rank) (Fin V.rank) ℂ) where
  carrier := lieAt V τ
  add_mem' {X Y} hX hY := by
    have hX' : Xᴴ * gramAt D V τ + gramAt D V τ * X = 0 := hX
    have hY' : Yᴴ * gramAt D V τ + gramAt D V τ * Y = 0 := hY
    show (X + Y)ᴴ * gramAt D V τ + gramAt D V τ * (X + Y) = 0
    rw [conjTranspose_add, Matrix.add_mul, Matrix.mul_add, add_add_add_comm, hX', hY', add_zero]
  zero_mem' := by
    show (0 : Matrix (Fin V.rank) (Fin V.rank) ℂ)ᴴ * gramAt D V τ + gramAt D V τ * 0 = 0
    simp
  smul_mem' c X hX := by
    have h := CCRuleCW.lie_smul (gramAt D V τ) X hX c
    show (c • X)ᴴ * gramAt D V τ + gramAt D V τ * (c • X) = 0
    simpa only [Complex.coe_smul] using h

theorem gp_dRep_addX {M : DSModel V S} {τ : D.what₂.Tau} {v : M.H τ}
    (hv : SmoothVec (lieAt V τ) (M.rep τ) v) {X Y : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hX : X ∈ lieAt V τ) (hY : Y ∈ lieAt V τ) :
    dRep (M.rep τ) (X + Y) v = dRep (M.rep τ) X v + dRep (M.rep τ) Y v := by
  have : CompleteSpace (M.H τ) := (M.ds τ).1
  have hXY : X + Y ∈ lieAt V τ := (gpTan V τ).add_mem hX hY
  have hd : ∀ W, W ∈ lieAt V τ → HasDerivAt
      (fun t : ℝ => M.σ τ (NormedSpace.exp (t • (M.fr τ * W * (M.fr τ)⁻¹))) v) (dRep (M.rep τ) W v) 0 := by
    intro W hW
    have e : (fun t : ℝ => M.σ τ (NormedSpace.exp (t • (M.fr τ * W * (M.fr τ)⁻¹))) v) =
        fun t : ℝ => M.rep τ (NormedSpace.exp (t • W)) v := funext fun t => by rw [rep_exp]
    rw [e]
    exact (gp_sv_diffAt hv hW).hasDerivAt
  have hsum : M.fr τ * (X + Y) * (M.fr τ)⁻¹ = M.fr τ * X * (M.fr τ)⁻¹ + M.fr τ * Y * (M.fr τ)⁻¹ := by
    rw [Matrix.mul_add, Matrix.add_mul]
  have h3 := hd (X + Y) hXY
  rw [hsum] at h3
  exact gp_deriv_add (urep M τ) (conj_lie M τ hX) (conj_lie M τ hY) (hd X hX) (hd Y hY) h3

theorem gp_dRep_smulR {M : DSModel V S} {τ : D.what₂.Tau} {v : M.H τ}
    (hv : SmoothVec (lieAt V τ) (M.rep τ) v) (c : ℝ) {X : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hX : X ∈ lieAt V τ) : dRep (M.rep τ) (c • X) v = c • dRep (M.rep τ) X v := by
  show deriv (fun t : ℝ => M.rep τ (NormedSpace.exp (t • (c • X))) v) 0 =
    c • deriv (fun t : ℝ => M.rep τ (NormedSpace.exp (t • X)) v) 0
  have e : (fun t : ℝ => M.rep τ (NormedSpace.exp (t • (c • X))) v) =
      fun t : ℝ => (fun s : ℝ => M.rep τ (NormedSpace.exp (s • X)) v) (c * t) := by
    funext t
    rw [smul_smul, mul_comm t c]
  rw [e]
  exact (deriv_comp_mul_left c (fun s : ℝ => M.rep τ (NormedSpace.exp (s • X)) v) 0).trans (by rw [mul_zero])

def gpA (M : DSModel V S) (τ : D.what₂.Tau) (u : M.H τ) (hu : SmoothVec (lieAt V τ) (M.rep τ) u) :
    gpTan V τ →ₗ[ℝ] M.H τ where
  toFun Y := dRep (M.rep τ) (Y : Matrix (Fin V.rank) (Fin V.rank) ℂ) u
  map_add' X Y := gp_dRep_addX hu X.2 Y.2
  map_smul' c X := gp_dRep_smulR hu c X.2

theorem gp_dRep_expand {M : DSModel V S} {τ : D.what₂.Tau} {u : M.H τ}
    (hu : SmoothVec (lieAt V τ) (M.rep τ) u) {Y : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hY : Y ∈ lieAt V τ) :
    dRep (M.rep τ) Y u = ∑ j, (((Module.finBasis ℝ (gpTan V τ)).repr ⟨Y, hY⟩ j : ℝ) : ℂ) •
      dRep (M.rep τ) ((Module.finBasis ℝ (gpTan V τ)) j : Matrix (Fin V.rank) (Fin V.rank) ℂ) u := by
  have h1 : dRep (M.rep τ) Y u = gpA M τ u hu ⟨Y, hY⟩ := rfl
  rw [h1]
  conv_lhs => rw [← (Module.finBasis ℝ (gpTan V τ)).sum_repr ⟨Y, hY⟩]
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul, Complex.coe_smul]
  all_goals rfl

theorem gp_sv_sum {M : DSModel V S} {τ : D.what₂.Tau} {ι : Type*} (s : Finset ι) (c : ι → ℂ) (x : ι → M.H τ)
    (hx : ∀ i, SmoothVec (lieAt V τ) (M.rep τ) (x i)) :
    SmoothVec (lieAt V τ) (M.rep τ) (∑ i ∈ s, c i • x i) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · rw [Finset.sum_empty]
    exact gp_sv_zero
  · intro a s ha ih
    rw [Finset.sum_insert ha]
    exact gp_sv_add (gp_sv_smul _ (hx a)) ih

theorem gp_foldr_sum {M : DSModel V S} {τ : D.what₂.Tau} (l : List (Matrix (Fin V.rank) (Fin V.rank) ℂ))
    (hl : ∀ X ∈ l, X ∈ lieAt V τ) {ι : Type*} (s : Finset ι) (c : ι → ℂ) (x : ι → M.H τ)
    (hx : ∀ i, SmoothVec (lieAt V τ) (M.rep τ) (x i)) :
    l.foldr (dRep (M.rep τ)) (∑ i ∈ s, c i • x i) = ∑ i ∈ s, c i • l.foldr (dRep (M.rep τ)) (x i) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp only [Finset.sum_empty]
    have h0 := gp_foldr_smul (M := M) (τ := τ) (0 : ℂ) l hl (v := 0) gp_sv_zero
    simpa using h0
  · intro a s ha ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha,
      gp_foldr_add l hl (gp_sv_smul _ (hx a)) (gp_sv_sum s c x hx), gp_foldr_smul _ l hl (hx a), ih]

theorem gp_words_cont {Ω : Type*} [TopologicalSpace Ω] (M : DSModel V S) (τ : D.what₂.Tau)
    (ls : List (Ω → Matrix (Fin V.rank) (Fin V.rank) ℂ)) :
    (∀ Y ∈ ls, Continuous Y) → (∀ Y ∈ ls, ∀ p, Y p ∈ lieAt V τ) →
      ∀ u : M.H τ, SmoothVec (lieAt V τ) (M.rep τ) u →
        Continuous fun p => (ls.map fun Y => Y p).foldr (dRep (M.rep τ)) u := by
  induction ls using List.reverseRecOn with
  | nil => intro _ _ u _; exact continuous_const
  | append_singleton ls Y ih =>
    intro hc hm u hu
    have hcl : ∀ Z ∈ ls, Continuous Z := fun Z hZ => hc Z (List.mem_append_left _ hZ)
    have hml : ∀ Z ∈ ls, ∀ p, Z p ∈ lieAt V τ := fun Z hZ => hm Z (List.mem_append_left _ hZ)
    have hYc : Continuous Y := hc Y (by simp)
    have hYm : ∀ p, Y p ∈ lieAt V τ := hm Y (by simp)
    have hwl : ∀ p, ∀ Z ∈ ls.map (fun Y => Y p), Z ∈ lieAt V τ := by
      intro p Z hZ
      obtain ⟨Z', hZ', rfl⟩ := List.mem_map.1 hZ
      exact hml Z' hZ' p
    have e : (fun p => ((ls ++ [Y]).map fun Y => Y p).foldr (dRep (M.rep τ)) u) =
        fun p => ∑ j, (((Module.finBasis ℝ (gpTan V τ)).repr ⟨Y p, hYm p⟩ j : ℝ) : ℂ) •
          (ls.map fun Y => Y p).foldr (dRep (M.rep τ))
            (dRep (M.rep τ) ((Module.finBasis ℝ (gpTan V τ)) j : Matrix (Fin V.rank) (Fin V.rank) ℂ) u) := by
      funext p
      rw [List.map_append, List.foldr_append]
      simp only [List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
      rw [gp_dRep_expand hu (hYm p), gp_foldr_sum _ (hwl p) Finset.univ _ _
        (fun j => gp_sv_dRep hu ((Module.finBasis ℝ (gpTan V τ)) j).2)]
    rw [e]
    refine continuous_finsetSum _ fun j _ => ?_
    have hco : Continuous fun p => (((Module.finBasis ℝ (gpTan V τ)).repr ⟨Y p, hYm p⟩ j : ℝ) : ℂ) := by
      have hl : Continuous ((Module.finBasis ℝ (gpTan V τ)).coord j) :=
        LinearMap.continuous_of_finiteDimensional _
      exact Complex.continuous_ofReal.comp (hl.comp (hYc.subtype_mk hYm))
    exact hco.smul (ih hcl hml _ (gp_sv_dRep hu ((Module.finBasis ℝ (gpTan V τ)) j).2))

theorem gp_lie_conj {τ : D.what₂.Tau} {g g' : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hg : g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) (hgg' : g * g' = 1)
    {X : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hX : X ∈ lieAt V τ) : g' * X * g ∈ lieAt V τ := by
  have hX' : Xᴴ * gramAt D V τ + gramAt D V τ * X = 0 := hX
  have hg0 : gᴴ * gramAt D V τ * g = gramAt D V τ := hg
  have h1 : gramAt D V τ * g' = gᴴ * gramAt D V τ := by
    calc gramAt D V τ * g' = gᴴ * gramAt D V τ * g * g' := by rw [hg0]
      _ = gᴴ * gramAt D V τ := by rw [Matrix.mul_assoc (gᴴ * gramAt D V τ), hgg', Matrix.mul_one]
  have h2 : g'ᴴ * gramAt D V τ = gramAt D V τ * g := by
    calc g'ᴴ * gramAt D V τ = g'ᴴ * (gᴴ * gramAt D V τ * g) := by rw [hg0]
      _ = (g * g')ᴴ * gramAt D V τ * g := by rw [conjTranspose_mul]; simp only [Matrix.mul_assoc]
      _ = gramAt D V τ * g := by rw [hgg', conjTranspose_one, Matrix.one_mul]
  show (g' * X * g)ᴴ * gramAt D V τ + gramAt D V τ * (g' * X * g) = 0
  calc (g' * X * g)ᴴ * gramAt D V τ + gramAt D V τ * (g' * X * g)
      = gᴴ * (Xᴴ * (g'ᴴ * gramAt D V τ)) + gramAt D V τ * g' * X * g := by
        rw [conjTranspose_mul, conjTranspose_mul]; simp only [Matrix.mul_assoc]
    _ = gᴴ * (Xᴴ * gramAt D V τ + gramAt D V τ * X) * g := by
        rw [h2, h1]; simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
    _ = 0 := by rw [hX', Matrix.mul_zero, Matrix.zero_mul]

theorem gp_dRep_conj (M : DSModel V S) (τ : D.what₂.Tau) {g g' : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hg : g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) (hgg' : g * g' = 1)
    {X : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hX : X ∈ lieAt V τ) {x : M.H τ}
    (hx : SmoothVec (lieAt V τ) (M.rep τ) x) :
    dRep (M.rep τ) X (M.rep τ g x) = M.rep τ g (dRep (M.rep τ) (g' * X * g) x) := by
  have hY := gp_lie_conj hg hgg' hX
  have hu : IsUnit g' := (Matrix.isUnit_iff_isUnit_det _).2 (Matrix.isUnit_det_of_left_inverse hgg')
  have hinv : g'⁻¹ = g := Matrix.inv_eq_left_inv hgg'
  have hexp : ∀ t : ℝ, NormedSpace.exp (t • X) * g = g * NormedSpace.exp (t • (g' * X * g)) := by
    intro t
    have h1 := Matrix.exp_conj g' (t • X) hu
    rw [hinv] at h1
    have h2 : g' * (t • X) * g = t • (g' * X * g) := by rw [Matrix.mul_smul, Matrix.smul_mul]
    rw [h2] at h1
    rw [h1, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hgg', Matrix.one_mul]
  have e : (fun t : ℝ => M.rep τ (NormedSpace.exp (t • X)) (M.rep τ g x)) =
      fun t : ℝ => M.rep τ g (M.rep τ (NormedSpace.exp (t • (g' * X * g))) x) := by
    funext t
    rw [← ContinuousLinearMap.comp_apply, ← rep_mul M τ (gp_exp_mem τ hX t) hg, hexp t,
      rep_mul M τ hg (gp_exp_mem τ hY t), ContinuousLinearMap.comp_apply]
  unfold dRep
  rw [e]
  exact (((M.rep τ g).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0 (gp_sv_diffAt hx hY).hasDerivAt).deriv

theorem gp_foldr_conj (M : DSModel V S) (τ : D.what₂.Tau) {g g' : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hg : g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) (hgg' : g * g' = 1) :
    ∀ l : List (Matrix (Fin V.rank) (Fin V.rank) ℂ), (∀ X ∈ l, X ∈ lieAt V τ) → ∀ {x : M.H τ},
      SmoothVec (lieAt V τ) (M.rep τ) x →
        l.foldr (dRep (M.rep τ)) (M.rep τ g x) =
          M.rep τ g ((l.map fun X => g' * X * g).foldr (dRep (M.rep τ)) x)
  | [], _, _, _ => rfl
  | X :: l, hl, x, hx => by
    have hl' : ∀ Y ∈ l, Y ∈ lieAt V τ := fun Y hY => hl Y (List.mem_cons_of_mem _ hY)
    have hlm : ∀ Y ∈ l.map (fun X => g' * X * g), Y ∈ lieAt V τ := by
      intro Y hY
      obtain ⟨Z, hZ, rfl⟩ := List.mem_map.1 hY
      exact gp_lie_conj hg hgg' (hl' Z hZ)
    rw [List.foldr_cons, List.map_cons, List.foldr_cons, gp_foldr_conj M τ hg hgg' l hl' hx]
    exact gp_dRep_conj M τ hg hgg' (hl X (by simp)) (gp_sv_foldr _ hlm hx)

theorem gp_cont_apply (M : DSModel V S) (τ : D.what₂.Tau) {F : PI.UpqRep.UJ (M.ε τ) → M.H τ}
    (hF : Continuous F) : Continuous fun h => M.σ τ (PI.UpqRep.umat h) (F h) := by
  have : CompleteSpace (M.H τ) := (M.ds τ).1
  rw [continuous_iff_continuousAt]
  intro h0
  have h1 : Tendsto (fun h => M.σ τ (PI.UpqRep.umat h) (F h0)) (𝓝 h0) (𝓝 (M.σ τ (PI.UpqRep.umat h0) (F h0))) :=
    (PI.KFinSmoothW.Gard.cont_orbit (urep M τ) (F h0)).continuousAt
  have h2 : Tendsto (fun h => M.σ τ (PI.UpqRep.umat h) (F h) - M.σ τ (PI.UpqRep.umat h) (F h0)) (𝓝 h0) (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have e : ∀ h : PI.UpqRep.UJ (M.ε τ),
        ‖M.σ τ (PI.UpqRep.umat h) (F h) - M.σ τ (PI.UpqRep.umat h) (F h0)‖ = ‖F h - F h0‖ := fun h => by
      rw [← map_sub, (urep M τ).2.1 _ h.2]
    simp only [e]
    have h3 := (hF.tendsto h0).sub_const (F h0)
    rw [sub_self] at h3
    exact tendsto_norm_zero.comp h3
  have h4 := h2.add h1
  simp only [sub_add_cancel, zero_add] at h4
  exact h4

theorem orbitDerivCont_holds : OrbitDerivCont := by
  unfold OrbitDerivCont
  intro D V S M τ w hw l hl
  have : CompleteSpace (M.H τ) := (M.ds τ).1
  have hum : Continuous (PI.UpqRep.umat : PI.UpqRep.UJ (M.ε τ) → Matrix (Fin V.rank) (Fin V.rank) ℂ) :=
    (PI.KFinSmoothW.Gard.umat_closedEmb (M.ε τ)).continuous
  have hmul : ∀ h : PI.UpqRep.UJ (M.ε τ), ((M.fr τ)⁻¹ * PI.UpqRep.umat h * M.fr τ) *
      ((M.fr τ)⁻¹ * PI.UpqRep.umat h⁻¹ * M.fr τ) = 1 := by
    intro h
    calc ((M.fr τ)⁻¹ * PI.UpqRep.umat h * M.fr τ) * ((M.fr τ)⁻¹ * PI.UpqRep.umat h⁻¹ * M.fr τ)
        = (M.fr τ)⁻¹ * PI.UpqRep.umat h * (M.fr τ * (M.fr τ)⁻¹) * PI.UpqRep.umat h⁻¹ * M.fr τ := by
          simp only [Matrix.mul_assoc]
      _ = (M.fr τ)⁻¹ * (PI.UpqRep.umat h * PI.UpqRep.umat h⁻¹) * M.fr τ := by
          rw [fr_mul_inv]; simp only [Matrix.mul_one, Matrix.mul_assoc]
      _ = 1 := by rw [PI.KFinSmoothW.Gard.umat_mul_inv, Matrix.mul_one, fr_inv_mul]
  have e : (fun h : PI.UpqRep.UJ (M.ε τ) => l.foldr (dRep (M.rep τ)) (M.σ τ (PI.UpqRep.umat h) w)) =
      fun h => M.σ τ (PI.UpqRep.umat h)
        (((l.map fun X (h : PI.UpqRep.UJ (M.ε τ)) => ((M.fr τ)⁻¹ * PI.UpqRep.umat h⁻¹ * M.fr τ) * X *
          ((M.fr τ)⁻¹ * PI.UpqRep.umat h * M.fr τ)).map fun Y => Y h).foldr (dRep (M.rep τ)) w) := by
    funext h
    rw [← rep_conj_back M τ h, gp_foldr_conj M τ (conj_back_mem M τ h) (hmul h) l hl hw, List.map_map]
    rfl
  rw [e]
  refine gp_cont_apply M τ (gp_words_cont M τ _ ?_ ?_ w hw)
  · intro Y hY
    obtain ⟨X, -, rfl⟩ := List.mem_map.1 hY
    exact (((continuous_const.mul (hum.comp continuous_inv)).mul continuous_const).mul continuous_const).mul
      ((continuous_const.mul hum).mul continuous_const)
  · intro Y hY h
    obtain ⟨X, hX, rfl⟩ := List.mem_map.1 hY
    exact gp_lie_conj (conj_back_mem M τ h) (hmul h) (hl X hX)

theorem gvPair_holds : GvPair := gvPair_of_orbitDerivCont orbitDerivCont_holds

end GvPairSec

end Formalism.IndefR.SchurOrthogonalityAlt

end
