import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LocalWeightCharts.StarOfInv

noncomputable section

open MeasureTheory Matrix Formalism.MainNotions.S Formalism.MainNotions.CayleySignature Formalism.L2.SG.SplitPrimeNormLemmas Formalism.L2.SG.WuDecay
open scoped InnerProductSpace ENNReal Classical

namespace WlocSk

namespace AQ

variable {k r : ℕ}

theorem opn_nonneg (M : Mat k r) : 0 ≤ opn M := norm_nonneg _

theorem opn_mul (A B : Mat k r) : opn (A * B) ≤ opn A * opn B := by
  unfold opn
  rw [map_mul]
  exact norm_mul_le _ _

theorem opn_conjTranspose (A : Mat k r) : opn Aᴴ = opn A := by
  unfold opn
  rw [← Matrix.star_eq_conjTranspose, map_star, norm_star]

theorem opn_one : opn (1 : Mat k r) = 1 := by
  unfold opn; rw [map_one]; exact norm_one

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

theorem nilradical_half_sum_nonneg : 0 ≤ N1H k r := by unfold N1H; positivity

theorem one_le_opn {g : Mat k r} (hg : g ∈ Gr k r) : 1 ≤ opn (Formalism.QuantumDeterminants.Hpk k r) * opn g := by
  have h1 : opn (1 : Mat k r) ≤ opn g⁻¹ * opn g := by rw [← Grp.inv_mul hg]; exact opn_mul _ _
  have h2 : opn g⁻¹ ≤ opn (Formalism.QuantumDeterminants.Hpk k r) * opn g * opn (Formalism.QuantumDeterminants.Hpk k r) := by
    rw [Grp.inv_eq hg]
    calc opn (Formalism.QuantumDeterminants.Hpk k r * gᴴ * Formalism.QuantumDeterminants.Hpk k r)
        ≤ opn (Formalism.QuantumDeterminants.Hpk k r * gᴴ) * opn (Formalism.QuantumDeterminants.Hpk k r) := opn_mul _ _
      _ ≤ opn (Formalism.QuantumDeterminants.Hpk k r) * opn gᴴ * opn (Formalism.QuantumDeterminants.Hpk k r) :=
          mul_le_mul_of_nonneg_right (opn_mul _ _) (opn_nonneg _)
      _ = _ := by rw [opn_conjTranspose]
  rw [opn_one] at h1
  have h0 := opn_nonneg g
  have hH := opn_nonneg (Formalism.QuantumDeterminants.Hpk k r)
  have h3 : 1 ≤ (opn (Formalism.QuantumDeterminants.Hpk k r) * opn g) ^ 2 := by nlinarith
  by_contra hlt
  push_neg at hlt
  have := pow_lt_one₀ (mul_nonneg hH h0) hlt two_ne_zero
  linarith

theorem one_le_opn_Hpk_rpow_mul_opn_rpow {g : Mat k r} (hg : g ∈ Gr k r) :
    1 ≤ opn (Formalism.QuantumDeterminants.Hpk k r) ^ N1H k r * opn g ^ N1H k r := by
  rw [← Real.mul_rpow (opn_nonneg _) (opn_nonneg _)]
  exact Real.one_le_rpow (one_le_opn hg) nilradical_half_sum_nonneg

theorem opn_rpow_mul (a b : Mat k r) : opn (a * b) ^ N1H k r ≤ opn a ^ N1H k r * opn b ^ N1H k r := by
  rw [← Real.mul_rpow (opn_nonneg _) (opn_nonneg _)]
  exact Real.rpow_le_rpow (opn_nonneg _) (opn_mul _ _) nilradical_half_sum_nonneg

theorem ae_fst {μW μN : Measure (Formalism.QuantumDeterminants.Mt k r)} [SFinite μN] {U : Set (Mat k r)}
    (hU : μW {x | Matrix.of x ∉ U} = 0) : ∀ᵐ p ∂(μW.prod μN), Matrix.of p.1 ∈ U := by
  rw [ae_iff]
  have : {p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r | ¬ Matrix.of p.1 ∈ U} =
      {x | Matrix.of x ∉ U} ×ˢ Set.univ := by ext p; simp
  rw [this, Measure.prod_prod, hU, zero_mul]

theorem ae_snd {μW μN : Measure (Formalism.QuantumDeterminants.Mt k r)} [SFinite μN] {U : Set (Mat k r)}
    (hU : μN {x | Matrix.of x ∉ U} = 0) : ∀ᵐ p ∂(μW.prod μN), Matrix.of p.2 ∈ U := by
  rw [ae_iff]
  have : {p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r | ¬ Matrix.of p.2 ∈ U} =
      Set.univ ×ˢ {x | Matrix.of x ∉ U} := by ext p; simp
  rw [this, Measure.prod_prod, hU, mul_zero]

section Int

variable {z : Fin (2 * r + k + 1) → ℂ} {c : Fin r → ℂ} {H : Type} [NormedAddCommGroup H]
  [InnerProductSpace ℂ H] {σ : Mat k r → (H →L[ℂ] H)} {Vp : Type} [NormedAddCommGroup Vp]
  [InnerProductSpace ℂ Vp] {π : Mat k r → (Vp →L[ℂ] Vp)}

theorem inner_iso {T : H →L[ℂ] H} (hT : ∀ v, ‖T v‖ = ‖v‖) (u v : H) : ⟪T u, T v⟫_ℂ = ⟪u, v⟫_ℂ := by
  let L : H →ₗᵢ[ℂ] H := { toLinearMap := (T : H →ₗ[ℂ] H), norm_map' := hT }
  exact L.inner_map_map u v

theorem bInt_enorm (hσ : IsURepOn (Gr k r) σ) {x : Mat k r} (hx : x ∈ Gr k r) (w' w : H) (ξ : Vp)
    (p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r) (hpG : Matrix.of p.1 * Matrix.of p.2 ∈ Gr k r)
    (hψ : ‖psiGen k r z c (Matrix.of p.2)‖ = 1) (hπ : ‖π (Matrix.of p.1)⁻¹ ξ‖ = ‖ξ‖) :
    ‖bInt z c σ π w' ξ (σ x w) p‖ₑ = ‖ξ‖ₑ * ‖⟪w', σ (Matrix.of (mulP p) * x) w⟫_ℂ‖ₑ := by
  have hm : σ (Matrix.of p.1 * Matrix.of p.2 * x) = (σ (Matrix.of p.1 * Matrix.of p.2)).comp (σ x) :=
    hσ.1.2 _ hpG _ hx
  have hmP : Matrix.of (mulP p) = Matrix.of p.1 * Matrix.of p.2 := rfl
  have hr : ‖bInt z c σ π w' ξ (σ x w) p‖ = ‖ξ‖ * ‖⟪w', σ (Matrix.of (mulP p) * x) w⟫_ℂ‖ := by
    unfold bInt
    rw [norm_smul, norm_mul, norm_star, hψ, hπ, hmP, hm, ContinuousLinearMap.comp_apply]
    ring
  rw [← ofReal_norm, hr, ENNReal.ofReal_mul (norm_nonneg _), ofReal_norm,
    ofReal_norm]

end Int

section Main

variable {z : Fin (2 * r + k + 1) → ℂ} {c : Fin r → ℂ} {u : Fin k → ℝ} {v : Fin (k - 1) → ℝ}
  {b : Fin (2 * r + 2) → ℝ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {σ : Mat k r → (H →L[ℂ] H)} {Vp : Type} [NormedAddCommGroup Vp] [InnerProductSpace ℂ Vp]
  [FiniteDimensional ℂ Vp] {π : Mat k r → (Vp →L[ℂ] Vp)} {w : H}
  {μG μS ν μW μN : Measure (Formalism.QuantumDeterminants.Mt k r)}

theorem facts (hSG : SGrp) (hPU : PiUnit) (hSig : SigmaG) (hyp : Hyp k r z c u v b σ π w μG μS ν μW μN) :
    IsURepOn (Gr k r) σ ∧ Formalism.QuantumDeterminants.UWset k r z ⊆ Gr k r ∧ Formalism.QuantumDeterminants.Nset k r ⊆ Gr k r ∧
      (∀ h ∈ Formalism.QuantumDeterminants.UWset k r z, h⁻¹ ∈ Formalism.QuantumDeterminants.UWset k r z) ∧
      (∀ m ∈ Formalism.QuantumDeterminants.Nset k r, ‖psiGen k r z c m‖ = 1) ∧
      (∀ h ∈ Formalism.QuantumDeterminants.UWset k r z, ∀ ξ : Vp, ‖π h ξ‖ = ‖ξ‖) := by
  obtain ⟨hset, hDS, hHC, -⟩ := hyp
  obtain ⟨-, -, hz, hT, -⟩ := hset
  obtain ⟨hW, hN, hWg, hNg, -⟩ := hSG k r z c hz hT
  refine ⟨hSig k r _ _ H σ hDS, hW, hN, fun h hh => (hWg h hh h hh).2.1,
    fun m hm => (hNg m hm m hm).2.2.2.2, (hPU k r z u Vp π hz hT hHC).2⟩

def wcoef (σ : Mat k r → (H →L[ℂ] H)) (w' w : H) (e : ℝ) (y : Formalism.QuantumDeterminants.Mt k r) : ℝ≥0∞ :=
  {y : Formalism.QuantumDeterminants.Mt k r | Matrix.of y ∈ Gr k r}.indicator
    (fun y => ENNReal.ofReal (‖⟪w', σ (Matrix.of y) w⟫_ℂ‖ * opn (Matrix.of y) ^ e)) y

theorem wcoef_meas (hσ : IsURepOn (Gr k r) σ) (w' w : H) {e : ℝ} (he : 0 ≤ e) :
    Measurable (wcoef σ w' w e) := by
  have h1 : ContinuousOn (fun y : Formalism.QuantumDeterminants.Mt k r => σ (Matrix.of y) w) {y | Matrix.of y ∈ Gr k r} :=
    (hσ.2.2 w).comp Grp.continuous_of.continuousOn (fun y hy => hy)
  have h2 := ContinuousOn.inner (𝕜 := ℂ) (continuousOn_const (c := w')) h1
  have h3 : ContinuousOn (fun y : Formalism.QuantumDeterminants.Mt k r => opn (Matrix.of y) ^ e) {y | Matrix.of y ∈ Gr k r} :=
    ((opn_continuous.comp Grp.continuous_of).continuousOn).rpow_const (fun _ _ => Or.inr he)
  have hc := ENNReal.continuous_ofReal.comp_continuousOn (h2.norm.mul h3)
  have hm := ContinuousOn.measurable_piecewise hc (continuous_const (y := (0 : ℝ≥0∞))).continuousOn
    Grp.measurableSet_Gr
  have heq : wcoef σ w' w e = {y : Formalism.QuantumDeterminants.Mt k r | Matrix.of y ∈ Gr k r}.piecewise
      (ENNReal.ofReal ∘ ((fun x => ‖⟪w', σ (Matrix.of x) w⟫_ℂ‖) * fun y => opn (Matrix.of y) ^ e))
      (fun _ => 0) := by
    funext y
    by_cases hy : y ∈ {y : Formalism.QuantumDeterminants.Mt k r | Matrix.of y ∈ Gr k r}
    · rw [Set.piecewise_eq_of_mem _ _ _ hy]; unfold wcoef; rw [Set.indicator_of_mem hy]; rfl
    · rw [Set.piecewise_eq_of_notMem _ _ _ hy]; unfold wcoef; rw [Set.indicator_of_notMem hy]
  rw [heq]
  exact hm

theorem G_int (hDec : Decay) (hCW : CoefWeightedLoc) (hσ : IsURepOn (Gr k r) σ)
    (hyp : Hyp k r z c u v b σ π w μG μS ν μW μN) {x₀ : Mat k r} (hx₀ : x₀ ∈ Gr k r) :
    ∫⁻ y, wcoef σ (σ x₀ w) w (N1H k r) y ∂μG < ⊤ := by
  have hDecI := hDec hCW k r z c u v b H σ Vp π w μG μS ν μW μN hyp
  obtain ⟨-, -, -, -, hG, -⟩ := hyp
  have hGinv := hG.2.2.2 x₀ hx₀
  have hlm : Measurable (Formalism.QuantumDeterminants.lmulM (k := k) (r := r) x₀) := by
    have : Continuous (Formalism.QuantumDeterminants.lmulM (k := k) (r := r) x₀) :=
      continuous_const.matrix_mul Grp.continuous_of
    exact this.measurable
  have hmeas := wcoef_meas hσ (σ x₀ w) w (nilradical_half_sum_nonneg (k := k) (r := r))
  rw [← hGinv, lintegral_map hmeas hlm]
  have hae : ∀ᵐ y ∂μG, Matrix.of y ∈ Gr k r := ae_iff.mpr hG.2.2.1
  have hbound : ∀ᵐ y ∂μG, wcoef σ (σ x₀ w) w (N1H k r) (Formalism.QuantumDeterminants.lmulM x₀ y) ≤
      ENNReal.ofReal (opn x₀ ^ N1H k r) *
        (‖⟪w, σ (Matrix.of y) w⟫_ℂ‖ₑ * ENNReal.ofReal (opn (Matrix.of y) ^ N1H k r)) := by
    filter_upwards [hae] with y hy
    have hxy : Matrix.of (Formalism.QuantumDeterminants.lmulM x₀ y) ∈ Gr k r := Grp.mul_mem hx₀ hy
    unfold wcoef
    rw [Set.indicator_of_mem (show Formalism.QuantumDeterminants.lmulM x₀ y ∈ {y : Formalism.QuantumDeterminants.Mt k r | Matrix.of y ∈ Gr k r} from hxy)]
    show ENNReal.ofReal (‖⟪σ x₀ w, σ (x₀ * Matrix.of y) w⟫_ℂ‖ * opn (x₀ * Matrix.of y) ^ N1H k r) ≤ _
    have hm : σ (x₀ * Matrix.of y) w = σ x₀ (σ (Matrix.of y) w) := by
      rw [hσ.1.2 x₀ hx₀ _ hy]; rfl
    rw [hm, inner_iso (hσ.2.1 x₀ hx₀), ← ofReal_norm,
      ← ENNReal.ofReal_mul (norm_nonneg _),
      ← ENNReal.ofReal_mul (Real.rpow_nonneg (opn_nonneg _) _)]
    apply ENNReal.ofReal_le_ofReal
    have := opn_rpow_mul x₀ (Matrix.of y)
    calc ‖⟪w, σ (Matrix.of y) w⟫_ℂ‖ * opn (x₀ * Matrix.of y) ^ N1H k r
        ≤ ‖⟪w, σ (Matrix.of y) w⟫_ℂ‖ * (opn x₀ ^ N1H k r * opn (Matrix.of y) ^ N1H k r) :=
          mul_le_mul_of_nonneg_left this (norm_nonneg _)
      _ = _ := by ring
  calc ∫⁻ y, wcoef σ (σ x₀ w) w (N1H k r) (Formalism.QuantumDeterminants.lmulM x₀ y) ∂μG
      ≤ ∫⁻ y, ENNReal.ofReal (opn x₀ ^ N1H k r) *
        (‖⟪w, σ (Matrix.of y) w⟫_ℂ‖ₑ * ENNReal.ofReal (opn (Matrix.of y) ^ N1H k r)) ∂μG :=
        lintegral_mono_ae hbound
    _ = ENNReal.ofReal (opn x₀ ^ N1H k r) * ∫⁻ y, ‖⟪w, σ (Matrix.of y) w⟫_ℂ‖ₑ *
        ENNReal.ofReal (opn (Matrix.of y) ^ N1H k r) ∂μG :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hDecI

theorem wcoef_zero_le (w' w : H) (y : Formalism.QuantumDeterminants.Mt k r) :
    wcoef σ w' w 0 y ≤ ENNReal.ofReal (opn (Formalism.QuantumDeterminants.Hpk k r) ^ N1H k r) * wcoef σ w' w (N1H k r) y := by
  unfold wcoef
  by_cases hy : Matrix.of y ∈ Gr k r
  · have hy' : y ∈ {y : Formalism.QuantumDeterminants.Mt k r | Matrix.of y ∈ Gr k r} := hy
    rw [Set.indicator_of_mem hy', Set.indicator_of_mem hy', Real.rpow_zero, mul_one,
      ← ENNReal.ofReal_mul (Real.rpow_nonneg (opn_nonneg _) _)]
    apply ENNReal.ofReal_le_ofReal
    have h1 := one_le_opn_Hpk_rpow_mul_opn_rpow hy
    have h0 := norm_nonneg (⟪w', σ (Matrix.of y) w⟫_ℂ)
    nlinarith
  · have hy' : y ∉ {y : Formalism.QuantumDeterminants.Mt k r | Matrix.of y ∈ Gr k r} := hy
    rw [Set.indicator_of_notMem hy']
    exact zero_le

theorem A_bound (hSG : SGrp) (hPU : PiUnit) (hSig : SigmaG) (hyp : Hyp k r z c u v b σ π w μG μS ν μW μN)
    (x₀ : Mat k r) (ξ : Vp) (x : Formalism.QuantumDeterminants.Mt k r) (hx : Matrix.of x ∈ Gr k r) (e q : ℝ)
    (hqle : ∀ s ∈ Formalism.QuantumDeterminants.Sset k r z, q ≤ opn (s * Matrix.of x) ^ e) :
    ‖Af z c σ π μW μN w x₀ ξ (Matrix.of x)‖ₑ * ENNReal.ofReal q ≤
      ‖ξ‖ₑ * ∫⁻ p, wcoef σ (σ x₀ w) w e (fun i j => (Matrix.of (mulP p) * Matrix.of x) i j) ∂(μW.prod μN) := by
  obtain ⟨hσ, hWG, hNG, hWinv, hψ, hπ⟩ := facts hSG hPU hSig hyp
  obtain ⟨-, -, -, -, -, -, -, hW, hN, -⟩ := hyp
  have := hN.1
  have hWc := ae_fst (μN := μN) hW.2.2.1
  have hNc := ae_snd (μW := μW) hN.2.2.1
  show ‖∫ p, bInt z c σ π (σ x₀ w) ξ (σ (Matrix.of x) w) p ∂(μW.prod μN)‖ₑ * ENNReal.ofReal q ≤ _
  calc ‖∫ p, bInt z c σ π (σ x₀ w) ξ (σ (Matrix.of x) w) p ∂(μW.prod μN)‖ₑ * ENNReal.ofReal q
      ≤ (∫⁻ p, ‖bInt z c σ π (σ x₀ w) ξ (σ (Matrix.of x) w) p‖ₑ ∂(μW.prod μN)) * ENNReal.ofReal q := by
        gcongr; exact enorm_integral_le_lintegral_enorm _
    _ = ∫⁻ p, ‖bInt z c σ π (σ x₀ w) ξ (σ (Matrix.of x) w) p‖ₑ * ENNReal.ofReal q ∂(μW.prod μN) :=
        (lintegral_mul_const' _ _ ENNReal.ofReal_ne_top).symm
    _ ≤ ∫⁻ p, ‖ξ‖ₑ * wcoef σ (σ x₀ w) w e (fun i j => (Matrix.of (mulP p) * Matrix.of x) i j)
        ∂(μW.prod μN) := by
        apply lintegral_mono_ae
        filter_upwards [hWc, hNc] with p h1 h2
        have hpG : Matrix.of p.1 * Matrix.of p.2 ∈ Gr k r := Grp.mul_mem (hWG h1) (hNG h2)
        rw [bInt_enorm hσ hx (σ x₀ w) w ξ p hpG (hψ _ h2) (hπ _ (hWinv _ h1) ξ)]
        have hyG : Matrix.of (fun i j => (Matrix.of (mulP p) * Matrix.of x) i j) ∈ Gr k r :=
          Grp.mul_mem hpG hx
        unfold wcoef
        rw [Set.indicator_of_mem (show (fun i j => (Matrix.of (mulP p) * Matrix.of x) i j) ∈
          {y : Formalism.QuantumDeterminants.Mt k r | Matrix.of y ∈ Gr k r} from hyG),
          ENNReal.ofReal_mul (norm_nonneg _), ofReal_norm, mul_assoc]
        gcongr
        · exact le_rfl
        · exact hqle _ ⟨_, h1, _, h2, rfl⟩
    _ = ‖ξ‖ₑ * ∫⁻ p, wcoef σ (σ x₀ w) w e (fun i j => (Matrix.of (mulP p) * Matrix.of x) i j)
        ∂(μW.prod μN) := lintegral_const_mul' _ _ enorm_ne_top

theorem nu_bound (hSG : SGrp) (hPU : PiUnit) (hSig : SigmaG) (hSP : SProd)
    (hyp : Hyp k r z c u v b σ π w μG μS ν μW μN) (x₀ : Mat k r) (ξ : Vp) (e : ℝ) (he : 0 ≤ e)
    (hfin : ∫⁻ y, wcoef σ (σ x₀ w) w e y ∂μG < ⊤) (q : Formalism.QuantumDeterminants.Mt k r → ℝ)
    (hqle : ∀ x, Matrix.of x ∈ Gr k r → ∀ s ∈ Formalism.QuantumDeterminants.Sset k r z, q x ≤ opn (s * Matrix.of x) ^ e) :
    ∫⁻ x, ‖Af z c σ π μW μN w x₀ ξ (Matrix.of x)‖ₑ * ENNReal.ofReal (q x) ∂ν < ⊤ := by
  obtain ⟨cS, -, hcS, hU⟩ := unfold_of hSP hyp
  have hnu := nu_conc_of hSG hyp
  have hσ := (facts hSG hPU hSig hyp).1
  have hae : ∀ᵐ x ∂ν, Matrix.of x ∈ Gr k r := ae_iff.mpr hnu
  calc ∫⁻ x, ‖Af z c σ π μW μN w x₀ ξ (Matrix.of x)‖ₑ * ENNReal.ofReal (q x) ∂ν
      ≤ ∫⁻ x, ‖ξ‖ₑ * ∫⁻ p, wcoef σ (σ x₀ w) w e (fun i j => (Matrix.of (mulP p) * Matrix.of x) i j)
        ∂(μW.prod μN) ∂ν := by
        apply lintegral_mono_ae
        filter_upwards [hae] with x hx
        exact A_bound hSG hPU hSig hyp x₀ ξ x hx e (q x) (hqle x hx)
    _ = ‖ξ‖ₑ * (cS * ∫⁻ y, wcoef σ (σ x₀ w) w e y ∂μG) := by
        rw [lintegral_const_mul' _ _ enorm_ne_top, hU _ (wcoef_meas hσ _ _ he)]
    _ < ⊤ := ENNReal.mul_lt_top enorm_lt_top (ENNReal.mul_lt_top (lt_top_iff_ne_top.mpr hcS) hfin)

theorem wave_packet_l1_finite (hSG : SGrp) (hPU : PiUnit) (hSig : SigmaG) (hSP : SProd) (hDec : Decay)
    (hCW : CoefWeightedLoc) (hyp : Hyp k r z c u v b σ π w μG μS ν μW μN)
    {x₀ : Mat k r} (hx₀ : x₀ ∈ Gr k r) (ξ : Vp) :
    ∫⁻ x, ‖Af z c σ π μW μN w x₀ ξ (Matrix.of x)‖ₑ ∂ν < ⊤ := by
  have hσ := (facts hSG hPU hSig hyp).1
  have hfin : ∫⁻ y, wcoef σ (σ x₀ w) w 0 y ∂μG < ⊤ := by
    calc ∫⁻ y, wcoef σ (σ x₀ w) w 0 y ∂μG
        ≤ ∫⁻ y, ENNReal.ofReal (opn (Formalism.QuantumDeterminants.Hpk k r) ^ N1H k r) * wcoef σ (σ x₀ w) w (N1H k r) y ∂μG :=
          lintegral_mono (fun y => wcoef_zero_le _ _ y)
      _ = ENNReal.ofReal (opn (Formalism.QuantumDeterminants.Hpk k r) ^ N1H k r) * ∫⁻ y, wcoef σ (σ x₀ w) w (N1H k r) y ∂μG :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top (G_int hDec hCW hσ hyp hx₀)
  have h := nu_bound hSG hPU hSig hSP hyp x₀ ξ 0 le_rfl hfin (fun _ => 1)
    (fun x _ s _ => by rw [Real.rpow_zero])
  simpa only [ENNReal.ofReal_one, mul_one] using h

theorem aWeighted_of (hSG : SGrp) (hPU : PiUnit) (hSig : SigmaG) (hSP : SProd) (hDec : Decay) :
    AWeighted := by
  intro k r z c u v b H _ _ _ σ Vp _ _ _ π w μG μS ν μW μN hyp _ hCW x₀ hx₀ ξ
  have hσ := (facts hSG hPU hSig hyp).1
  refine nu_bound hSG hPU hSig hSP hyp x₀ ξ (N1H k r) nilradical_half_sum_nonneg (G_int hDec hCW hσ hyp hx₀)
    (fun x => nuH k r z (Matrix.of x) ^ N1H k r) ?_
  intro x _ s hs
  have hbdd : BddBelow (Set.range fun t : Formalism.QuantumDeterminants.Sset k r z => opn ((t : Mat k r) * Matrix.of x)) :=
    ⟨0, by rintro _ ⟨t, rfl⟩; exact opn_nonneg _⟩
  have h1 : nuH k r z (Matrix.of x) ≤ opn (s * Matrix.of x) :=
    ciInf_le hbdd (⟨s, hs⟩ : Formalism.QuantumDeterminants.Sset k r z)
  have h0 : 0 ≤ nuH k r z (Matrix.of x) := Real.iInf_nonneg (fun t => opn_nonneg _)
  exact Real.rpow_le_rpow h0 h1 nilradical_half_sum_nonneg

theorem substE (hSG : SGrp) (hWR : WRightInv) (hNU : NUnimod) (hyp : Hyp k r z c u v b σ π w μG μS ν μW μN)
    {h m : Mat k r} (hh : h ∈ Formalism.QuantumDeterminants.UWset k r z) (hm : m ∈ Formalism.QuantumDeterminants.Nset k r) :
    ∃ E : (Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r) ≃ᵐ (Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r),
      (μW.prod μN).map E = μW.prod μN ∧
      ∀ p, Matrix.of (E p).1 * Matrix.of (E p).2 * (h * m) = Matrix.of p.1 * Matrix.of p.2 := by
  obtain ⟨hset, -, -, -, -, -, -, hW, hN, hWfin, hNK⟩ := hyp
  obtain ⟨-, -, hz, hT, -⟩ := hset
  obtain ⟨hWG, hNG, hWg, hNg, hconj⟩ := hSG k r z c hz hT
  have hhG := hWG hh
  have hmG := hNG hm
  have hhi : h⁻¹ ∈ Formalism.QuantumDeterminants.UWset k r z := (hWg h hh h hh).2.1
  have hih : h⁻¹ * h = 1 := Grp.inv_mul hhG
  have hhi' : h * h⁻¹ = 1 := Grp.mul_inv hhG
  have hinv2 : (h⁻¹)⁻¹ = h :=
    Matrix.nonsing_inv_nonsing_inv h (Matrix.isUnit_det_of_right_inverse hhi')
  have hmi : m⁻¹ ∈ Formalism.QuantumDeterminants.Nset k r := (hNg m hm m hm).2.1
  have hmim : m⁻¹ * m = 1 := Grp.inv_mul hmG
  obtain ⟨hm₀, -⟩ := hconj h⁻¹ hhi m⁻¹ hmi
  rw [hinv2] at hm₀
  obtain ⟨m₀, hm₀def⟩ : ∃ m₀ : Mat k r, m₀ = h * m⁻¹ * h⁻¹ := ⟨_, rfl⟩
  rw [← hm₀def] at hm₀
  have hm₀G := hNG hm₀
  have hW1 := hWR k r z μW hz hT hW hWfin h⁻¹ hhi
  have hN1 := hNU k r z μN hz hT hN hNK h⁻¹ hhi m₀ hm₀
  rw [hinv2] at hN1
  have h3 : h⁻¹ * m₀ * (m₀⁻¹ * h) = 1 := by
    rw [Matrix.mul_assoc, AE.cancel (Grp.mul_inv hm₀G), hih]
  have h4 : m₀⁻¹ * h * (h⁻¹ * m₀) = 1 := by
    rw [Matrix.mul_assoc, AE.cancel hhi', Grp.inv_mul hm₀G]
  let e₁ := AE.affE (k := k) (r := r) 1 1 h⁻¹ h (Matrix.one_mul 1) (Matrix.one_mul 1) hih hhi'
  let e₂ := AE.affE (k := k) (r := r) h h⁻¹ (h⁻¹ * m₀) (m₀⁻¹ * h) hih hhi' h3 h4
  have he₁ : μW.map e₁ = μW := by
    have : (e₁ : Formalism.QuantumDeterminants.Mt k r → Formalism.QuantumDeterminants.Mt k r) = fun x => fun i j => (Matrix.of x * h⁻¹) i j := by
      funext x i j
      show ((1 : Mat k r) * Matrix.of x * h⁻¹) i j = _
      rw [Matrix.one_mul]
    rw [this, hW1]
  have he₂ : μN.map e₂ = μN := by
    have : (e₂ : Formalism.QuantumDeterminants.Mt k r → Formalism.QuantumDeterminants.Mt k r) =
        fun x => fun i j => (h * Matrix.of x * h⁻¹ * m₀) i j := by
      funext x i j
      show (h * Matrix.of x * (h⁻¹ * m₀)) i j = _
      rw [← Matrix.mul_assoc (h * Matrix.of x)]
    rw [this, hN1]
  refine ⟨e₁.prodCongr e₂, ?_, ?_⟩
  · have := hW.1
    have := hN.1
    show (μW.prod μN).map (Prod.map e₁ e₂) = _
    rw [← Measure.map_prod_map μW μN e₁.measurable e₂.measurable, he₁, he₂]
  · intro p
    show (1 * Matrix.of p.1 * h⁻¹) * (h * Matrix.of p.2 * (h⁻¹ * m₀)) * (h * m) = _
    rw [hm₀def]
    simp only [Matrix.one_mul, Matrix.mul_assoc]
    rw [AE.cancel hih, AE.cancel hih, AE.cancel hih, hmim, Matrix.mul_one]

def aF (σ : Mat k r → (H →L[ℂ] H)) (w' w : H) (μW μN : Measure (Formalism.QuantumDeterminants.Mt k r)) (x : Mat k r) : ℝ≥0∞ :=
  ∫⁻ p, wcoef σ w' w 0 (fun i j => (Matrix.of (mulP p) * x) i j) ∂(μW.prod μN)

theorem aF_inv (hSG : SGrp) (hWR : WRightInv) (hNU : NUnimod) (hyp : Hyp k r z c u v b σ π w μG μS ν μW μN)
    (w' : H) {h m : Mat k r} (hh : h ∈ Formalism.QuantumDeterminants.UWset k r z) (hm : m ∈ Formalism.QuantumDeterminants.Nset k r) (x : Mat k r) :
    aF σ w' w μW μN (h * m * x) = aF σ w' w μW μN x := by
  obtain ⟨E, hE, hEp⟩ := substE hSG hWR hNU hyp hh hm
  unfold aF
  conv_lhs => rw [← hE]
  rw [lintegral_map_equiv]
  refine lintegral_congr (fun p => ?_)
  show wcoef σ w' w 0 (fun i j => (Matrix.of (E p).1 * Matrix.of (E p).2 * (h * m * x)) i j) =
    wcoef σ w' w 0 (fun i j => (Matrix.of p.1 * Matrix.of p.2 * x) i j)
  rw [show Matrix.of (E p).1 * Matrix.of (E p).2 * (h * m * x) = Matrix.of p.1 * Matrix.of p.2 * x by
    rw [← hEp p]; simp only [Matrix.mul_assoc]]

theorem aF_meas (hσ : IsURepOn (Gr k r) σ) (w' w : H) (μW μN : Measure (Formalism.QuantumDeterminants.Mt k r)) [SFinite μW]
    [SFinite μN] : Measurable (fun y : Formalism.QuantumDeterminants.Mt k r => aF σ w' w μW μN (Matrix.of y)) := by
  have hc : Continuous (fun q : Formalism.QuantumDeterminants.Mt k r × (Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r) =>
      (fun i j => (Matrix.of (mulP q.2) * Matrix.of q.1) i j : Formalism.QuantumDeterminants.Mt k r)) := by
    have h1 : Continuous fun q : Formalism.QuantumDeterminants.Mt k r × (Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r) =>
        (Matrix.of (mulP q.2) : Mat k r) := continuous_mulP.comp continuous_snd
    have h2 : Continuous fun q : Formalism.QuantumDeterminants.Mt k r × (Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r) =>
        (Matrix.of q.1 : Mat k r) := continuous_fst
    exact h1.matrix_mul h2
  exact ((wcoef_meas hσ w' w le_rfl).comp hc.measurable).lintegral_prod_right'

theorem aF_eq (hSG : SGrp) (hPU : PiUnit) (hSig : SigmaG) (hyp : Hyp k r z c u v b σ π w μG μS ν μW μN)
    (x₀ : Mat k r) (ξ : Vp) {y : Mat k r} (hy : y ∈ Gr k r) :
    ∫⁻ p, ‖bInt z c σ π (σ x₀ w) ξ (σ y w) p‖ₑ ∂(μW.prod μN) = ‖ξ‖ₑ * aF σ (σ x₀ w) w μW μN y := by
  obtain ⟨hσ, hWG, hNG, hWinv, hψ, hπ⟩ := facts hSG hPU hSig hyp
  obtain ⟨-, -, -, -, -, -, -, hW, hN, -⟩ := hyp
  have := hN.1
  have hWc := ae_fst (μN := μN) hW.2.2.1
  have hNc := ae_snd (μW := μW) hN.2.2.1
  unfold aF
  rw [← lintegral_const_mul' _ _ enorm_ne_top]
  apply lintegral_congr_ae
  filter_upwards [hWc, hNc] with p h1 h2
  have hpG : Matrix.of p.1 * Matrix.of p.2 ∈ Gr k r := Grp.mul_mem (hWG h1) (hNG h2)
  rw [bInt_enorm hσ hy (σ x₀ w) w ξ p hpG (hψ _ h2) (hπ _ (hWinv _ h1) ξ)]
  have hyG : (fun i j => (Matrix.of (mulP p) * y) i j : Formalism.QuantumDeterminants.Mt k r) ∈
      {y : Formalism.QuantumDeterminants.Mt k r | Matrix.of y ∈ Gr k r} := Grp.mul_mem hpG hy
  unfold wcoef
  rw [Set.indicator_of_mem hyG, Real.rpow_zero, mul_one, ofReal_norm]
  rfl

def Fq (σ : Mat k r → (H →L[ℂ] H)) (w' w : H) (μW μN : Measure (Formalism.QuantumDeterminants.Mt k r)) (ξ : Vp)
    (y : Formalism.QuantumDeterminants.Mt k r) : ℝ≥0∞ :=
  wcoef σ w' w 0 y * (‖ξ‖ₑ * aF σ w' w μW μN (Matrix.of y))

theorem wave_packet_l2_finite (hSG : SGrp) (hPU : PiUnit) (hSig : SigmaG) (hSP : SProd) (hDec : Decay) (hWR : WRightInv)
    (hNU : NUnimod) (hAB : ABound) (hR : Formalism.L2.SG.HCReprodM.HCReprodDSm) (hCW : CoefWeightedLoc)
    (hyp : Hyp k r z c u v b σ π w μG μS ν μW μN) {x₀ : Mat k r} (hx₀ : x₀ ∈ Gr k r) (ξ : Vp) :
    l2SG ν (Af z c σ π μW μN w x₀ ξ) < ⊤ := by
  obtain ⟨C, hC0, hC⟩ := hAB k r z c u v b H σ Vp π w μG μS ν μW μN hyp hR hCW x₀ hx₀ ξ
  obtain ⟨cS, -, hcS, hU⟩ := unfold_of hSP hyp
  have hnu := nu_conc_of hSG hyp
  have hσ := (facts hSG hPU hSig hyp).1
  have hGfin := G_int hDec hCW hσ hyp hx₀
  have hG := hyp.2.2.2.2.1
  have hW := hyp.2.2.2.2.2.2.2.1
  have hN := hyp.2.2.2.2.2.2.2.2.1
  have := hW.1
  have := hN.1
  have hWc := ae_fst (μN := μN) hW.2.2.1
  have hNc := ae_snd (μW := μW) hN.2.2.1
  have hf₀m : Measurable (wcoef σ (σ x₀ w) w 0) := wcoef_meas hσ _ _ le_rfl
  have hFm : Measurable (Fq σ (σ x₀ w) w μW μN ξ) :=
    hf₀m.mul ((aF_meas hσ _ _ μW μN).const_mul _)
  have hae : ∀ᵐ x ∂ν, Matrix.of x ∈ Gr k r := ae_iff.mpr hnu
  have hpt : ∀ x : Formalism.QuantumDeterminants.Mt k r, Matrix.of x ∈ Gr k r →
      (‖Af z c σ π μW μN w x₀ ξ (Matrix.of x)‖₊ : ℝ≥0∞) ^ 2 ≤
        ‖ξ‖ₑ * ∫⁻ p, Fq σ (σ x₀ w) w μW μN ξ (fun i j => (Matrix.of (mulP p) * Matrix.of x) i j)
          ∂(μW.prod μN) := by
    intro x hx
    have h1 := A_bound hSG hPU hSig hyp x₀ ξ x hx 0 1 (fun s _ => by rw [Real.rpow_zero])
    rw [ENNReal.ofReal_one, mul_one] at h1
    have h1' : ‖Af z c σ π μW μN w x₀ ξ (Matrix.of x)‖ₑ ≤ ‖ξ‖ₑ * aF σ (σ x₀ w) w μW μN (Matrix.of x) := h1
    have hmeasp : Measurable (fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r =>
        wcoef σ (σ x₀ w) w 0 (fun i j => (Matrix.of (mulP p) * Matrix.of x) i j)) := by
      have : Continuous (fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r =>
          (fun i j => (Matrix.of (mulP p) * Matrix.of x) i j : Formalism.QuantumDeterminants.Mt k r)) :=
        continuous_mulP.matrix_mul continuous_const
      exact hf₀m.comp this.measurable
    calc (‖Af z c σ π μW μN w x₀ ξ (Matrix.of x)‖₊ : ℝ≥0∞) ^ 2
        = ‖Af z c σ π μW μN w x₀ ξ (Matrix.of x)‖ₑ * ‖Af z c σ π μW μN w x₀ ξ (Matrix.of x)‖ₑ := by
          rw [sq, enorm_eq_nnnorm]
      _ ≤ (‖ξ‖ₑ * aF σ (σ x₀ w) w μW μN (Matrix.of x)) * (‖ξ‖ₑ * aF σ (σ x₀ w) w μW μN (Matrix.of x)) :=
          mul_le_mul' h1' h1'
      _ = ‖ξ‖ₑ * ∫⁻ p, wcoef σ (σ x₀ w) w 0 (fun i j => (Matrix.of (mulP p) * Matrix.of x) i j) *
            (‖ξ‖ₑ * aF σ (σ x₀ w) w μW μN (Matrix.of x)) ∂(μW.prod μN) := by
          rw [lintegral_mul_const _ hmeasp, mul_assoc]
          rfl
      _ = ‖ξ‖ₑ * ∫⁻ p, Fq σ (σ x₀ w) w μW μN ξ (fun i j => (Matrix.of (mulP p) * Matrix.of x) i j)
            ∂(μW.prod μN) := by
          refine congrArg (HMul.hMul ‖ξ‖ₑ) ?_
          apply lintegral_congr_ae
          filter_upwards [hWc, hNc] with p hp1 hp2
          show _ = wcoef σ (σ x₀ w) w 0 (fun i j => (Matrix.of (mulP p) * Matrix.of x) i j) *
            (‖ξ‖ₑ * aF σ (σ x₀ w) w μW μN (Matrix.of p.1 * Matrix.of p.2 * Matrix.of x))
          rw [aF_inv hSG hWR hNU hyp _ hp1 hp2]
  have hFb : ∀ᵐ y ∂μG, Fq σ (σ x₀ w) w μW μN ξ y ≤
      ENNReal.ofReal C * wcoef σ (σ x₀ w) w (N1H k r) y := by
    filter_upwards [ae_iff.mpr hG.2.2.1] with y hy
    have hb := hC (Matrix.of y) hy
    rw [aF_eq hSG hPU hSig hyp x₀ ξ hy] at hb
    have hy' : y ∈ {y : Formalism.QuantumDeterminants.Mt k r | Matrix.of y ∈ Gr k r} := hy
    unfold Fq
    calc wcoef σ (σ x₀ w) w 0 y * (‖ξ‖ₑ * aF σ (σ x₀ w) w μW μN (Matrix.of y))
        ≤ wcoef σ (σ x₀ w) w 0 y * ENNReal.ofReal (C * opn (Matrix.of y) ^ N1H k r) := by gcongr
      _ = ENNReal.ofReal C * wcoef σ (σ x₀ w) w (N1H k r) y := by
        unfold wcoef
        rw [Set.indicator_of_mem hy', Set.indicator_of_mem hy', Real.rpow_zero, mul_one,
          ← ENNReal.ofReal_mul (norm_nonneg _), ← ENNReal.ofReal_mul hC0]
        congr 1
        ring
  calc l2SG ν (Af z c σ π μW μN w x₀ ξ)
      = ∫⁻ x, (‖Af z c σ π μW μN w x₀ ξ (Matrix.of x)‖₊ : ℝ≥0∞) ^ 2 ∂ν := rfl
    _ ≤ ∫⁻ x, ‖ξ‖ₑ * ∫⁻ p, Fq σ (σ x₀ w) w μW μN ξ (fun i j => (Matrix.of (mulP p) * Matrix.of x) i j)
          ∂(μW.prod μN) ∂ν := by
        apply lintegral_mono_ae
        filter_upwards [hae] with x hx
        exact hpt x hx
    _ = ‖ξ‖ₑ * (cS * ∫⁻ y, Fq σ (σ x₀ w) w μW μN ξ y ∂μG) := by
        rw [lintegral_const_mul' _ _ enorm_ne_top, hU _ hFm]
    _ ≤ ‖ξ‖ₑ * (cS * ∫⁻ y, ENNReal.ofReal C * wcoef σ (σ x₀ w) w (N1H k r) y ∂μG) := by
        gcongr ‖ξ‖ₑ * (cS * ?_)
        exact lintegral_mono_ae hFb
    _ < ⊤ := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        exact ENNReal.mul_lt_top enorm_lt_top (ENNReal.mul_lt_top (lt_top_iff_ne_top.mpr hcS)
          (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hGfin))

theorem wave_packet_l1_l2_of_hypotheses (hSG : SGrp) (hPU : PiUnit) (hSig : SigmaG) (hSP : SProd) (hDec : Decay)
    (hWR : WRightInv) (hNU : NUnimod) (hAB : ABound) : WavePacketL1L2 := by
  intro k r z c u v b H _ _ _ σ Vp _ _ _ π w μG μS ν μW μN hyp hR hCW x₀ hx₀ ξ
  exact ⟨wave_packet_l1_finite hSG hPU hSig hSP hDec hCW hyp hx₀ ξ,
    wave_packet_l2_finite hSG hPU hSig hSP hDec hWR hNU hAB hR hCW hyp hx₀ ξ⟩

end Main

end AQ

end WlocSk
