import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.GLMatrixDerivatives.FrameDer

noncomputable section

open MeasureTheory Matrix Finset Filter
open scoped ContDiff ComplexConjugate Topology

namespace PositivityTheory.RgBcC.LfSt

open PositivityTheory.RgBcC
open PositivityTheory.RgTw (Mat G th tw hb)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

theorem isBump_zero_of_neg {g : ℝ → ℝ} {T : ℝ} (h : IsBump g T) (hT : T < 0) : IsBump g 0 := by
  refine ⟨h.1, h.2.1, fun t ht => h.2.2 t (lt_trans hT ht)⟩

theorem isMult_nonneg [MeasurableSpace (G n)] {μ : Measure (G n)} {E : KMod n} {k : Mat n → (E.V →L[ℂ] E.V)}
    {val : Inf n → ℂ} {T : ℝ} (h : IsMult μ E k val T) : IsMult μ E k val (max T 0) := by
  obtain ⟨m, c, w, g, ks, hks, hk, hv⟩ := h
  refine ⟨m, c, w, g, ks, fun i => ⟨?_, (hks i).2⟩, hk, hv⟩
  rcases le_or_gt 0 T with hT | hT
  · rw [max_eq_left hT]; exact (hks i).1
  · rw [max_eq_right hT.le]; exact isBump_zero_of_neg (hks i).1 hT

theorem mem_GLs_mul {x y : Mat n} (hx : x ∈ GLs n) (hy : y ∈ GLs n) : x * y ∈ GLs n := by
  simp only [GLs, Set.mem_setOf_eq, Matrix.det_mul] at *
  exact mul_ne_zero hx hy

theorem unitary_mem_GLs (k : Matrix.unitaryGroup (Fin n) ℂ) : k.1 ∈ GLs n := by
  have h := Matrix.UnitaryGroup.det_isUnit k
  exact h.ne_zero

theorem isMult_props [MeasurableSpace (G n)] {μ : Measure (G n)} {E : KMod n} {k : Mat n → (E.V →L[ℂ] E.V)}
    {val : Inf n → ℂ} {T : ℝ} (h : IsMult μ E k val T) :
    ContDiffOn ℝ ∞ k (GLs n) ∧
      ∀ y ∈ GLs n, ∀ k₁ k₂ : Matrix.unitaryGroup (Fin n) ℂ, k (k₁.1 * y * k₂.1) = E.ρ k₁ * k y * E.ρ k₂ := by
  obtain ⟨m, c, w, g, ks, hks, hk, -⟩ := h
  refine ⟨?_, fun y hy k₁ k₂ => ?_⟩
  · have hs : ContDiffOn ℝ ∞ (fun y => ∑ i, c i • ks i y) (GLs n) :=
      ContDiffOn.sum fun i _ => ((hks i).2.1).const_smul (c i)
    exact hs.congr fun y hy => hk y hy
  · have hy' : k₁.1 * y * k₂.1 ∈ GLs n := mem_GLs_mul (mem_GLs_mul (unitary_mem_GLs k₁) hy) (unitary_mem_GLs k₂)
    rw [hk _ hy', hk y hy, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [(hks i).2.2.2.1 y hy k₁ k₂, mul_smul_comm, smul_mul_assoc]

theorem inv_mem_GLs {x : Mat n} (hx : x ∈ GLs n) : x⁻¹ ∈ GLs n := by
  have hu : IsUnit x.det := isUnit_iff_ne_zero.2 hx
  exact (Matrix.isUnit_nonsing_inv_det x hu).ne_zero

theorem conjTranspose_mem_GLs {x : Mat n} (hx : x ∈ GLs n) : xᴴ ∈ GLs n := by
  simp only [GLs, Set.mem_setOf_eq, Matrix.det_conjTranspose, star_ne_zero] at *
  exact hx

theorem tw_mem_GLs {x d : Mat n} (hx : x ∈ GLs n) (hd : d ∈ GLs n) : x⁻¹ * d * xᴴ⁻¹ ∈ GLs n :=
  mem_GLs_mul (mem_GLs_mul (inv_mem_GLs hx) hd) (inv_mem_GLs (conjTranspose_mem_GLs hx))

theorem lAsm : LAsm := by
  classical
  intro hHb _hFD hKC hKS hE1 hE0 _hHom hCone0 _hWE _hWS hKE hMA hCh hCone hHom hSupp
  intro n lam E Fr ε ι S Γ T hCx _ _ μ _ k val τ hk d z hd hz hz2
  obtain ⟨hopen, hconv, σ, hσ, hσ2, hmeas⟩ := hCone n
  obtain ⟨c, -, hform⟩ := hmeas μ
  obtain ⟨hksm, hkeq⟩ := isMult_props hk
  have hdG : d.val ∈ GLs n := ((Matrix.isUnit_iff_isUnit_det _).mp (Units.isUnit d)).ne_zero
  have hch := hCh n lam E Fr ε ι S Γ T hCx μ k val τ hk
  have hkΓ : ∀ y ∈ GLs n, Γ * k y = k y * Γ := fun y hy => (hch y hy).1
  obtain ⟨c0, hc0⟩ := hKE n
  have hsuppk : ∀ y ∈ GLs n, c0 * (1 + max τ 0) < lg y → k y = 0 :=
    (hc0 μ E).2 k val (max τ 0) (le_max_right _ _) (isMult_nonneg hk)
  set R := c0 * (1 + max τ 0) with hRdef
  obtain ⟨hKsm, hKΓ, hKch⟩ := hKC n lam E Fr ε ι S Γ T hCx σ hσ hσ2 k hksm hkeq (fun y hy => hch y hy) d.val hdG c
  obtain ⟨C, hCU, hCc, hCsupp⟩ := hKS hSupp n E.V σ hσ hσ2 Fr k Γ T R hsuppk z hz hz2 c
  have hK : Kc σ c Fr k Γ T d.val = Kc σ c Fr k Γ T (diagonal z) := by rw [hd]
  set K' : (Fin n × Fin n → ℝ) × (Fin n × Fin n → ℝ) → (E.V →L[ℂ] E.V) := fun y =>
    if y ∈ cone n ×ˢ cone n then Kc σ c Fr k Γ T d.val y else 0 with hK'def
  have hUU : IsOpen (cone n ×ˢ cone n) := hopen.prod hopen
  have hKK' : ∀ y ∈ cone n ×ˢ cone n, K' =ᶠ[𝓝 y] Kc σ c Fr k Γ T d.val := fun y hy =>
    Filter.eventually_of_mem (hUU.mem_nhds hy) fun y' hy' => by simp only [hK'def, if_pos hy']
  obtain ⟨hherm, htr, -, -, -, -, -, hoPt⟩ := hHb n
  have hH := hHom (Fin n × Fin n) E.V (fun i => ε (hb i)) (fun i => ι (hb i)) S Γ (cone n) (oPt n) K' hopen hconv hoPt
    (fun i j => by
      rw [hCx.car (hb i) (hb j) (hherm i) (hherm j), htr i j]
      split_ifs <;> simp)
    (fun i => hCx.Γε _) (fun i => hCx.Γι _) hCx.SΓ hCx.Ssmooth (fun s i => hCx.Sε s _) hCx.Sder
    (hKsm.congr fun y hy => by simp only [hK'def, if_pos hy])
    (fun y => by
      by_cases hy : y ∈ cone n ×ˢ cone n
      · simp only [hK'def, if_pos hy]; exact hKΓ y hy
      · simp only [hK'def, if_neg hy, mul_zero, zero_mul])
    (fun y hy => by
      rw [(hKK' y hy).fderiv_eq]
      exact hKch y hy)
    ⟨C, hCU, hCc, fun s hs v hv hvC => by
      have h1 := hCsupp s hs v hv hvC
      have hmem : (s • v + (1 - s) • oPt n, v) ∈ cone n ×ˢ cone n :=
        ⟨hconv hv hoPt hs.1 (by linarith [hs.2]) (by ring), hv⟩
      filter_upwards [h1, hKK' _ hmem] with y h1y h2y
      rw [h2y, hK]
      exact h1y⟩
  obtain ⟨R', hR'⟩ := hSupp n z hz hz2 R
  have hR1 : ∀ x ∈ GLs n, R' < lg x → k (x⁻¹ * d.val * xᴴ⁻¹) = 0 := by
    intro x hx hlt
    by_contra hne
    have hle : lg (x⁻¹ * diagonal z * xᴴ⁻¹) ≤ R := by
      by_contra hgt
      push_neg at hgt
      exact hne (hd ▸ hsuppk _ (hd ▸ tw_mem_GLs hx hdG) hgt)
    have := hR' 1 ⟨zero_le_one, le_refl _⟩ x hx x hx (by simp) hle
    linarith
  obtain ⟨hint, heq1⟩ := hE1 n lam E Fr ε ι S Γ T hCx μ σ c hσ hσ2 hform k hksm.continuousOn hkeq hkΓ d R' hR1
  have heig := (hMA n μ E k k val val τ τ hk hk).2.2.2
  have heq0 := hE0 n lam E Fr ε ι S Γ T hCx μ σ c hσ hσ2 hform k val hksm.continuousOn hkeq hkΓ ⟨R, hsuppk⟩ heig
    d z hd hz hz2
  refine ⟨hint, ?_⟩
  rw [← heq1, ← heq0]
  have e1 : ∫ v in cone n, LinearMap.trace ℂ E.V ((Γ * S 1 * K' (v, v) : E.V →L[ℂ] E.V) : E.V →ₗ[ℂ] E.V) =
      ∫ v in cone n, LinearMap.trace ℂ E.V ((Γ * S 1 * Kc σ c Fr k Γ T d.val (v, v) : E.V →L[ℂ] E.V) : E.V →ₗ[ℂ] E.V) :=
    setIntegral_congr_fun hopen.measurableSet fun v hv => by simp only [hK'def, if_pos (show (v, v) ∈ cone n ×ˢ cone n from ⟨hv, hv⟩)]
  have e0 : ∫ v in cone n, LinearMap.trace ℂ E.V ((Γ * S 0 * K' (oPt n, v) : E.V →L[ℂ] E.V) : E.V →ₗ[ℂ] E.V) =
      ∫ v in cone n, LinearMap.trace ℂ E.V ((Γ * S 0 * Kc σ c Fr k Γ T d.val (oPt n, v) : E.V →L[ℂ] E.V) : E.V →ₗ[ℂ] E.V) :=
    setIntegral_congr_fun hopen.measurableSet fun v hv => by
      simp only [hK'def, if_pos (show (oPt n, v) ∈ cone n ×ˢ cone n from ⟨hoPt, hv⟩)]
  rw [← e1, ← e0]
  exact hH

end PositivityTheory.RgBcC.LfSt
