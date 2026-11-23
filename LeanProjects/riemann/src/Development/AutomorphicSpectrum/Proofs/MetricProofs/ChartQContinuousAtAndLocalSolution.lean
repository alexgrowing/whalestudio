import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsEigFrames
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.IsPshLocallyIntegrableStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LogPeriodLimit
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsIsChart
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsotropicSublatticeCovolumePositiveStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.RiemannLatticeEigenProjectionStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsIntPreimageOfOrthogonalKernelStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RiemannFormHermitianLatticeStatement
open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular
open GlobalTheory.CompanionTheory.Ar.RiemannLimit GlobalTheory.CompanionTheory.Ar.Cusp.BoundaryLimit

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.BoundaryLimit.QuotientForm

local notation "κ[" R "]" => Matrix.map R (fun x : ℝ => (x : ℂ))

section Real

variable {g : ℕ} {Pr : Matrix (Fin g) (Fin g) ℝ}

theorem pr_mul_M (h2 : Pr * Pr = Pr) (Y : Matrix (Fin g) (Fin g) ℝ) :
    Pr * (Pr * Y * Pr + (1 - Pr)) = Pr * Y * Pr := by
  rw [mul_add, mul_sub, mul_one, h2, sub_self, add_zero, ← mul_assoc, ← mul_assoc, h2]

theorem one_sub_mul_M (h2 : Pr * Pr = Pr) (Y : Matrix (Fin g) (Fin g) ℝ) :
    (1 - Pr) * (Pr * Y * Pr + (1 - Pr)) = 1 - Pr := by
  have h : (1 - Pr) * Pr = 0 := by rw [sub_mul, one_mul, h2, sub_self]
  rw [mul_add, ← mul_assoc, ← mul_assoc, h, zero_mul, zero_mul, zero_add, mul_sub, mul_one, h,
    sub_zero]

theorem M_det {Y : Matrix (Fin g) (Fin g) ℝ} (h2 : Pr * Pr = Pr) (hT : Prᵀ = Pr)
    (h : ∀ v, Pr *ᵥ v = v → v ⬝ᵥ Y *ᵥ v = 0 → v = 0) : (Pr * Y * Pr + (1 - Pr)).det ≠ 0 := by
  intro h0
  obtain ⟨v, hv, hMv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
  have h1 : (1 - Pr) *ᵥ v = 0 := by
    rw [← one_sub_mul_M h2 Y, ← Matrix.mulVec_mulVec, hMv, mulVec_zero]
  have hPv : Pr *ᵥ v = v := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero] at h1
    exact h1.symm
  have h3 : (Pr * Y * Pr) *ᵥ v = 0 := by
    rw [← pr_mul_M h2 Y, ← Matrix.mulVec_mulVec, hMv, mulVec_zero]
  refine hv (h v hPv ?_)
  have h4 : v ⬝ᵥ (Pr * Y * Pr) *ᵥ v = v ⬝ᵥ Y *ᵥ v := by
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hPv, Matrix.dotProduct_mulVec,
      ← Matrix.mulVec_transpose, hT, hPv]
  rw [← h4, h3, dotProduct_zero]

theorem pr_Y_compInv {Y : Matrix (Fin g) (Fin g) ℝ} (h2 : Pr * Pr = Pr)
    (hd : (Pr * Y * Pr + (1 - Pr)).det ≠ 0) : Pr * Y * compInv Pr Y = Pr := by
  unfold compInv
  have hu := Ne.isUnit hd
  calc Pr * Y * (Pr * (Pr * Y * Pr + (1 - Pr))⁻¹ * Pr)
      = (Pr * Y * Pr) * (Pr * Y * Pr + (1 - Pr))⁻¹ * Pr := by simp only [mul_assoc]
    _ = Pr * (Pr * Y * Pr + (1 - Pr)) * (Pr * Y * Pr + (1 - Pr))⁻¹ * Pr := by rw [pr_mul_M h2]
    _ = Pr * Pr := by rw [mul_assoc Pr (Pr * Y * Pr + (1 - Pr)), Matrix.mul_nonsing_inv _ hu, mul_one]
    _ = Pr := h2

theorem compInv_symm {Y : Matrix (Fin g) (Fin g) ℝ} (hT : Prᵀ = Pr) (hY : Yᵀ = Y) :
    (compInv Pr Y)ᵀ = compInv Pr Y := by
  unfold compInv
  have hM : (Pr * Y * Pr + (1 - Pr))ᵀ = Pr * Y * Pr + (1 - Pr) := by
    simp [Matrix.transpose_add, Matrix.transpose_mul, Matrix.transpose_sub, hT, hY, mul_assoc]
  rw [Matrix.transpose_mul, Matrix.transpose_mul, hT, Matrix.transpose_nonsing_inv, hM]
  exact (mul_assoc _ _ _).symm

theorem compInv_kill (Y : Matrix (Fin g) (Fin g) ℝ) {u : Fin g → ℝ} (hu : Pr *ᵥ u = 0) :
    compInv Pr Y *ᵥ u = 0 := by
  unfold compInv
  rw [← Matrix.mulVec_mulVec, hu, mulVec_zero]

theorem exists_right_inv {S : Matrix (Fin g) (Fin g) ℝ} (h2 : Pr * Pr = Pr) (hPS : Pr * S = 0)
    (hk : ∀ v : Fin g → ℝ, S *ᵥ v = 0 ↔ Pr *ᵥ v = v) : ∃ C, 1 - Pr = S * C := by
  have hd : (S + Pr).det ≠ 0 := by
    intro h0
    obtain ⟨v, hv, hN⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
    have h1 : Pr *ᵥ v = 0 := by
      have h := congrArg (fun x => Pr *ᵥ x) hN
      simpa only [Matrix.mulVec_mulVec, mulVec_zero, mul_add, hPS, h2, zero_add] using h
    have h3 : S *ᵥ v = 0 := by
      rw [Matrix.add_mulVec, h1, add_zero] at hN
      exact hN
    exact hv (((hk v).1 h3).symm.trans h1)
  refine ⟨(S + Pr)⁻¹, ?_⟩
  have h4 : (1 - Pr) * (S + Pr) = S := by
    rw [sub_mul, one_mul, mul_add, hPS, h2, zero_add, add_sub_cancel_right]
  calc 1 - Pr = (1 - Pr) * ((S + Pr) * (S + Pr)⁻¹) := by
        rw [Matrix.mul_nonsing_inv _ (Ne.isUnit hd), mul_one]
    _ = S * (S + Pr)⁻¹ := by rw [← mul_assoc, h4]

theorem tendsto_minv {𝕜 : Type*} [NormedField 𝕜] {X : Type*} {f : Filter X}
    {M : X → Matrix (Fin g) (Fin g) 𝕜} {M₀ : Matrix (Fin g) (Fin g) 𝕜} (h : Tendsto M f (𝓝 M₀))
    (h0 : M₀.det ≠ 0) : Tendsto (fun x => (M x)⁻¹) f (𝓝 M₀⁻¹) := by
  have hd : Tendsto (fun x => (M x).det) f (𝓝 M₀.det) :=
    ((continuous_id.matrix_det).tendsto _).comp h
  have ha : Tendsto (fun x => (M x).adjugate) f (𝓝 M₀.adjugate) :=
    ((continuous_id.matrix_adjugate).tendsto _).comp h
  have := (hd.inv₀ h0).smul ha
  simpa [Matrix.inv_def, Ring.inverse_eq_inv'] using this

theorem kappa_mul (R R' : Matrix (Fin g) (Fin g) ℝ) : κ[R * R'] = κ[R] * κ[R'] := by
  ext i j
  simp [Matrix.mul_apply]

theorem kappa_one : κ[(1 : Matrix (Fin g) (Fin g) ℝ)] = 1 := by
  ext i j
  by_cases h : i = j <;> simp [Matrix.one_apply, h]

theorem kappa_sub (R R' : Matrix (Fin g) (Fin g) ℝ) : κ[R - R'] = κ[R] - κ[R'] := by
  ext i j
  simp

theorem kappa_transpose (R : Matrix (Fin g) (Fin g) ℝ) : κ[R]ᵀ = κ[Rᵀ] := by
  ext i j
  simp

theorem star_kappa_mulVec (R : Matrix (Fin g) (Fin g) ℝ) (v : Fin g → ℂ) :
    star (κ[R] *ᵥ v) = κ[R] *ᵥ star v := by
  funext i
  simp [mulVec, dotProduct, map_sum]

theorem kappa_mulVec_ofReal (R : Matrix (Fin g) (Fin g) ℝ) (r : Fin g → ℝ) :
    κ[R] *ᵥ (fun k => (r k : ℂ)) = fun k => ((R *ᵥ r) k : ℂ) := by
  funext i
  simp [mulVec, dotProduct]

theorem dot_adj (M : Matrix (Fin g) (Fin g) ℂ) (a b : Fin g → ℂ) :
    (M *ᵥ a) ⬝ᵥ b = a ⬝ᵥ (Mᵀ *ᵥ b) := by
  rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]

theorem conj_form (Am Hb : Matrix (Fin g) (Fin g) ℂ) (y y' : Fin g → ℂ) :
    (Amᵀ *ᵥ y) ⬝ᵥ Hb *ᵥ star (Amᵀ *ᵥ y') = y ⬝ᵥ (Am * Hb * Amᴴ) *ᵥ star y' := by
  rw [Matrix.mulVec_transpose, Matrix.mulVec_transpose, Matrix.star_vecMul,
    ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]

end Real

section Kernel

variable {g a : ℕ} {B : Fin a → Matrix (Fin g) (Fin g) ℤ} {Pr : Matrix (Fin g) (Fin g) ℝ}

theorem sum_map_real (B : Fin a → Matrix (Fin g) (Fin g) ℤ) :
    (∑ j, B j).map (fun x : ℤ => (x : ℝ)) = ∑ j, (B j).map (fun x : ℤ => (x : ℝ)) := by
  ext p q
  simp [Matrix.sum_apply]

theorem S_psd (hB : ∀ j, ((B j).map (fun x : ℤ => (x : ℝ))).PosSemidef) :
    ((∑ j, B j).map (fun x : ℤ => (x : ℝ))).PosSemidef := by
  rw [sum_map_real]
  exact posSemidef_sum _ fun j _ => hB j

theorem S_symm (hB : ∀ j, ((B j).map (fun x : ℤ => (x : ℝ))).PosSemidef) :
    (∑ j, B j)ᵀ = ∑ j, B j :=
  GlobalTheory.CompanionTheory.ToricBasis.symm_of_posSemidef (S_psd hB)

theorem B_kill (hB : ∀ j, ((B j).map (fun x : ℤ => (x : ℝ))).PosSemidef)
    (hK : IsKerProj (∑ j, B j) Pr) (j : Fin a) : (B j).map (fun x : ℤ => (x : ℝ)) * Pr = 0 := by
  have key : ∀ v : Fin g → ℝ, ((B j).map (fun x : ℤ => (x : ℝ)) * Pr) *ᵥ v = 0 := by
    intro v
    have hx : (∑ j, B j).map (fun x : ℤ => (x : ℝ)) *ᵥ (Pr *ᵥ v) = 0 :=
      (hK.2.2 _).2 (by rw [Matrix.mulVec_mulVec, hK.1])
    have h0 : (Pr *ᵥ v) ⬝ᵥ ((∑ j, B j).map (fun x : ℤ => (x : ℝ)) *ᵥ (Pr *ᵥ v)) = 0 := by
      rw [hx]; simp
    rw [sum_map_real, Matrix.sum_mulVec, dotProduct_sum] at h0
    have hnn : ∀ i ∈ Finset.univ, 0 ≤ (Pr *ᵥ v) ⬝ᵥ ((B i).map (fun x : ℤ => (x : ℝ)) *ᵥ (Pr *ᵥ v)) :=
      fun i _ => by simpa using (hB i).dotProduct_mulVec_nonneg (Pr *ᵥ v)
    have h1 := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 h0 j (Finset.mem_univ j)
    rw [← Matrix.mulVec_mulVec]
    exact ((hB j).dotProduct_mulVec_zero_iff _).1 (by simpa using h1)
  ext p q
  simpa using congrFun (key (Pi.single q 1)) p

theorem S_pr (hB : ∀ j, ((B j).map (fun x : ℤ => (x : ℝ))).PosSemidef)
    (hK : IsKerProj (∑ j, B j) Pr) : (∑ j, B j).map (fun x : ℤ => (x : ℝ)) * Pr = 0 := by
  rw [sum_map_real, Finset.sum_mul]
  exact Finset.sum_eq_zero fun j _ => B_kill hB hK j

theorem pr_S (hB : ∀ j, ((B j).map (fun x : ℤ => (x : ℝ))).PosSemidef)
    (hK : IsKerProj (∑ j, B j) Pr) : Pr * (∑ j, B j).map (fun x : ℤ => (x : ℝ)) = 0 := by
  have h := congrArg Matrix.transpose (S_pr hB hK)
  rw [Matrix.transpose_mul, hK.2.1, ← Matrix.transpose_map, S_symm hB] at h
  simpa using h

theorem compress (hB : ∀ j, ((B j).map (fun x : ℤ => (x : ℝ))).PosSemidef)
    (hK : IsKerProj (∑ j, B j) Pr) (T : Matrix (Fin g) (Fin g) ℂ) (s : Fin a → ℂ) :
    Pr * (T + ∑ j, s j • (B j).map (fun x : ℤ => (x : ℂ))).map Complex.im * Pr =
      Pr * T.map Complex.im * Pr := by
  have h : (T + ∑ j, s j • (B j).map (fun x : ℤ => (x : ℂ))).map Complex.im
      = T.map Complex.im + ∑ j, (s j).im • (B j).map (fun x : ℤ => (x : ℝ)) := by
    ext p q
    simp [Matrix.sum_apply, Complex.im_sum]
  have h0 : (∑ j, (s j).im • (B j).map (fun x : ℤ => (x : ℝ))) * Pr = 0 := by
    rw [Finset.sum_mul]
    exact Finset.sum_eq_zero fun j _ => by rw [Matrix.smul_mul, B_kill hB hK j, smul_zero]
  rw [h, mul_add, add_mul, mul_assoc Pr (∑ j, _), h0, mul_zero, add_zero]

theorem compInv_congr {Y Y' : Matrix (Fin g) (Fin g) ℝ} (h : Pr * Y * Pr = Pr * Y' * Pr) :
    compInv Pr Y = compInv Pr Y' := by
  unfold compInv
  rw [h]

theorem pr_kills (hB : ∀ j, ((B j).map (fun x : ℤ => (x : ℝ))).PosSemidef)
    (hK : IsKerProj (∑ j, B j) Pr) (u : Fin g → ℤ)
    (hu : ∀ v : Fin g → ℤ, (∑ j, B j) *ᵥ v = 0 → u ⬝ᵥ v = 0) :
    Pr *ᵥ (fun k => (u k : ℝ)) = 0 := by
  obtain ⟨N, c, hN, h⟩ := GlobalTheory.T.exists_int_preimage_of_orthogonal_kernel g _ (S_symm hB) u hu
  have h1 : (N : ℝ) • (fun k => (u k : ℝ)) =
      (∑ j, B j).map (fun x : ℤ => (x : ℝ)) *ᵥ (fun k => (c k : ℝ)) := by
    funext k
    have := congrFun h k
    simp only [Pi.smul_apply, smul_eq_mul, mulVec, dotProduct, Matrix.map_apply] at this ⊢
    exact_mod_cast this
  have h2 : (N : ℝ) • (Pr *ᵥ (fun k => (u k : ℝ))) = 0 := by
    rw [← Matrix.mulVec_smul, h1, Matrix.mulVec_mulVec, pr_S hB hK, Matrix.zero_mulVec]
  exact (smul_eq_zero.1 h2).resolve_left (by exact_mod_cast hN)

end Kernel

section Riemann

variable {g : ℕ}

theorem cst_single (i : Fin g) : cst (Pi.single i 1 : Fin g → ℤ) = Pi.single i 1 := by
  funext k
  by_cases h : k = i
  · subst h; simp [cst]
  · simp [cst, h]

theorem riemann_real (τ G : Matrix (Fin g) (Fin g) ℂ)
    (hrel : ∀ u u' v v' : Fin g → ℤ, ((cst u + τ *ᵥ cst v) ⬝ᵥ G *ᵥ star (cst u' + τ *ᵥ cst v')).im =
      ((v ⬝ᵥ u' - u ⬝ᵥ v' : ℤ) : ℝ)) :
    ∃ R : Matrix (Fin g) (Fin g) ℝ, G = κ[R] ∧ R * τ.map Complex.im = 1 := by
  have h1 : ∀ i j, (G i j).im = 0 := by
    intro i j
    have h := hrel (Pi.single i 1) (Pi.single j 1) 0 0
    simpa [cst_single, cst_zero] using h
  have h2 : ∀ i j, ∑ k, (G i k).re * (τ k j).im = if i = j then 1 else 0 := by
    intro i j
    have h := hrel (Pi.single i 1) 0 0 (Pi.single j 1)
    simp only [cst_single, cst_zero, mulVec_zero, add_zero, zero_add] at h
    have e : star (τ *ᵥ (Pi.single j 1 : Fin g → ℂ)) = fun k => star (τ k j) := by
      funext k
      simp
    have e2 : ((Pi.single i 1 : Fin g → ℤ) ⬝ᵥ (Pi.single j 1 : Fin g → ℤ)) = if i = j then 1 else 0 := by
      by_cases hij : i = j
      · subst hij; simp
      · simp [hij, Pi.single_apply, Ne.symm hij]
    have e3 : ∀ k, (G i k * star (τ k j)).im = -((G i k).re * (τ k j).im) := by
      intro k
      simp [Complex.mul_im, h1]
    rw [e, e2, zero_dotProduct, zero_sub, single_one_dotProduct] at h
    simp only [mulVec, dotProduct, Complex.im_sum, e3, Finset.sum_neg_distrib] at h
    split_ifs at h ⊢ with hij
    · simpa using h
    · simpa using h
  refine ⟨G.map Complex.re, ?_, ?_⟩
  · ext i j
    apply Complex.ext <;> simp [h1]
  · ext i j
    simp [Matrix.mul_apply, h2, Matrix.one_apply]

end Riemann

section Chart

variable {n a g : ℕ} {Λ : Type} [AddCommGroup Λ] {L : Flat.LogPeriods n a g Λ}
  {bas : Module.Basis (Fin g ⊕ Fin g) ℤ Λ} {A T0 : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ}
  {B : Fin a → Matrix (Fin g) (Fin g) ℤ} {c ρ : ℝ} {Pr : Matrix (Fin g) (Fin g) ℝ}

theorem mem_chartW (x : Λ) : x ∈ chartW bas B ↔ (∑ j, B j) *ᵥ vCo bas x = 0 := by
  rw [chartW, LinearMap.mem_ker]
  rfl

theorem mk_mem (u : Fin g → ℤ) : mk bas u 0 ∈ chartW bas B := by
  rw [mem_chartW, vCo_mk]
  simp

theorem rad_coords (hC : IsChart L bas A T0 B c ρ) (x : chartW bas B)
    (hx : ∀ x' : chartW bas B, L.E x x' = 0) :
    vCo bas (x : Λ) = 0 ∧ ∀ v : Fin g → ℤ, (∑ j, B j) *ᵥ v = 0 → uCo bas (x : Λ) ⬝ᵥ v = 0 := by
  have hform := form_coords bas L.E hC.form L.alt
  constructor
  · funext i
    have h := hx ⟨mk bas (Pi.single i 1) 0, mk_mem _⟩
    rw [hform] at h
    simpa [vCo_mk, uCo_mk] using h
  · intro v hv
    have h := hx ⟨mk bas 0 v, (mem_chartW _).2 (by rw [vCo_mk]; exact hv)⟩
    rw [hform] at h
    simpa [vCo_mk, uCo_mk] using h

theorem span_mem (hC : IsChart L bas A T0 B c ρ) (hK : IsKerProj (∑ j, B j) Pr) {w : Fin n → ℂ}
    (hw : w ∈ logCover L.a_le) (d : Fin g → ℂ) (hd : κ[Pr] *ᵥ d = 0) :
    (A (expCover a w))ᵀ *ᵥ d ∈ Submodule.span ℂ {u | ∃ x : chartW bas B,
      (∀ x' : chartW bas B, L.E x x' = 0) ∧ u = L.P w x} := by
  have hB := hC.B_psd
  have hform := form_coords bas L.E hC.form L.alt
  obtain ⟨C, hCm⟩ := exists_right_inv hK.1 (pr_S hB hK) hK.2.2
  set S := ∑ j, B j with hS
  have hST : Sᵀ = S := S_symm hB
  have h1 : d = κ[S.map (fun x : ℤ => (x : ℝ))] *ᵥ (κ[C] *ᵥ d) := by
    rw [Matrix.mulVec_mulVec, ← kappa_mul, ← hCm, kappa_sub, kappa_one, Matrix.sub_mulVec,
      Matrix.one_mulVec, hd, sub_zero]
  have h2 : ∀ q : Fin g → ℂ, κ[S.map (fun x : ℤ => (x : ℝ))] *ᵥ q =
      ∑ i, q i • cst (fun k => S k i) := by
    intro q
    funext k
    simp [mulVec, dotProduct, cst, Finset.sum_apply, mul_comm]
  rw [h1, h2]
  have h3 : ∀ f : Fin g → Fin g → ℂ, (A (expCover a w))ᵀ *ᵥ (∑ i, f i) =
      ∑ i, (A (expCover a w))ᵀ *ᵥ f i := fun f =>
    map_sum ((A (expCover a w))ᵀ).mulVecLin f Finset.univ
  rw [h3]
  refine Submodule.sum_mem _ fun i _ => ?_
  rw [Matrix.mulVec_smul]
  refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨mk bas (fun k => S k i) 0, mk_mem _⟩,
    fun x' => ?_, ?_⟩)
  · have hx' := (mem_chartW (x' : Λ)).1 x'.2
    rw [hform]
    simp only [vCo_mk, uCo_mk, zero_dotProduct, zero_sub, neg_eq_zero]
    have h4 := congrFun hx' i
    simp only [mulVec, Pi.zero_apply] at h4
    rw [← h4]
    simp only [dotProduct]
    refine Finset.sum_congr rfl fun k _ => ?_
    have := congrFun (congrFun hST k) i
    simp only [transpose_apply] at this
    show S k i * _ = S i k * _
    rw [this]
  · rw [hC.per w hw]
    simp [uCo_mk, vCo_mk, cst_zero]

end Chart

section Main

variable {n a g : ℕ} {Λ : Type} [AddCommGroup Λ] {L : Flat.LogPeriods n a g Λ}
  {bas : Module.Basis (Fin g ⊕ Fin g) ℤ Λ} {A T0 : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ}
  {B : Fin a → Matrix (Fin g) (Fin g) ℤ} {c ρ : ℝ} {Pr : Matrix (Fin g) (Fin g) ℝ}

theorem M_det_centre (hC : IsChart L bas A T0 B c ρ) (hK : IsKerProj (∑ j, B j) Pr) :
    (Pr * (T0 0).map Complex.im * Pr + (1 - Pr)).det ≠ 0 := by
  have hB := hC.B_psd
  refine M_det hK.1 hK.2.1 fun v hv h => ?_
  have hl := GlobalTheory.CompanionTheory.ChartBlockLower.im_lower_on_kernel n a g L.a_le (Metric.ball 0 ρ) T0 B c
    Metric.isOpen_ball (hC.T_cont.mono (Metric.ball_subset_ball hC.ρ_le)) hB hC.c_pos hC.im_lower 0
    (Metric.mem_ball_self hC.ρ_pos) 0 (fun j hj => absurd rfl hj) (fun _ _ => rfl) v
    (fun j _ => by rw [← hv, Matrix.mulVec_mulVec, B_kill hB hK j, Matrix.zero_mulVec])
  have e : T0 0 + ∑ j, (((0 : Fin a → ℂ) j) / (2 * Real.pi * Complex.I)) •
      (B j).map (fun x : ℤ => (x : ℂ)) = T0 0 := by simp
  rw [e, h] at hl
  have h5 : 0 ≤ v ⬝ᵥ v := Finset.sum_nonneg fun i _ => mul_self_nonneg _
  have h6 : v ⬝ᵥ v ≤ 0 := by
    by_contra hh
    have := mul_pos hC.c_pos (not_le.1 hh)
    linarith
  exact dotProduct_self_eq_zero.1 (le_antisymm h6 h5)

theorem chartQ_cont (hC : IsChart L bas A T0 B c ρ) (hK : IsKerProj (∑ j, B j) Pr) :
    ContinuousAt (chartQ Pr A T0) 0 := by
  have h0 : (0 : Fin n → ℂ) ∈ Metric.ball (0 : Fin n → ℂ) 1 := Metric.mem_ball_self one_pos
  have hA : Tendsto A (𝓝 0) (𝓝 (A 0)) :=
    (hC.A_cont.continuousAt (Metric.isOpen_ball.mem_nhds h0)).tendsto
  have hT : Tendsto T0 (𝓝 0) (𝓝 (T0 0)) :=
    (hC.T_cont.continuousAt (Metric.isOpen_ball.mem_nhds h0)).tendsto
  have hY : Tendsto (fun z => (T0 z).map Complex.im) (𝓝 0) (𝓝 ((T0 0).map Complex.im)) :=
    ((continuous_id.matrix_map Complex.continuous_im).tendsto _).comp hT
  have hMt : Tendsto (fun z => Pr * (T0 z).map Complex.im * Pr + (1 - Pr)) (𝓝 0)
      (𝓝 (Pr * (T0 0).map Complex.im * Pr + (1 - Pr))) :=
    ((tendsto_const_nhds.mul hY).mul tendsto_const_nhds).add tendsto_const_nhds
  have hG : Tendsto (fun z => compInv Pr ((T0 z).map Complex.im)) (𝓝 0)
      (𝓝 (compInv Pr ((T0 0).map Complex.im))) :=
    (tendsto_const_nhds.mul (tendsto_minv hMt (M_det_centre hC hK))).mul tendsto_const_nhds
  have hGc : Tendsto (fun z => κ[compInv Pr ((T0 z).map Complex.im)]) (𝓝 0)
      (𝓝 κ[compInv Pr ((T0 0).map Complex.im)]) :=
    ((continuous_id.matrix_map Complex.continuous_ofReal).tendsto _).comp hG
  have hA1 := tendsto_minv hA hC.A_det
  have hAH : Tendsto (fun z => (A z)ᴴ) (𝓝 0) (𝓝 (A 0)ᴴ) :=
    ((continuous_id.matrix_conjTranspose).tendsto _).comp hA
  have hA2 := tendsto_minv hAH (by rw [det_conjTranspose]; exact star_ne_zero.2 hC.A_det)
  exact (hA1.mul hGc).mul hA2

theorem rep_at (hC : IsChart L bas A T0 B c ρ) (hK : IsKerProj (∑ j, B j) Pr) {w : Fin n → ℂ}
    (hw : w ∈ logCover L.a_le) (hd : (A (expCover a w)).det ≠ 0) (y : Fin g → ℂ) :
    ∃ p : Fin g → ℂ, p - y ∈ Submodule.span ℂ {u | ∃ x : chartW bas B,
        (∀ x' : chartW bas B, L.E x x' = 0) ∧ u = L.P w x} ∧
      (∀ x : chartW bas B, (∀ x' : chartW bas B, L.E x x' = 0) →
        p ⬝ᵥ L.H (expCover a w) *ᵥ star (L.P w x) = 0) ∧
      ∀ y' : Fin g → ℂ, y' ⬝ᵥ L.H (expCover a w) *ᵥ star p =
        y' ⬝ᵥ chartQ Pr A T0 (expCover a w) *ᵥ star y := by
  have hB := hC.B_psd
  have hform := form_coords bas L.E hC.form L.alt
  set Am := A (expCover a w) with hAm
  set Hm := L.H (expCover a w) with hHm
  set τ := tauAt L.a_le T0 B w with hτ
  set Y := τ.map Complex.im with hYdef
  have hYpd : Y.PosDef := hC.im_pos w hw
  have hunit : IsUnit (Amᵀ).det := Ne.isUnit (by rwa [det_transpose])
  have hunit' : IsUnit Am.det := Ne.isUnit hd
  have hunitH : IsUnit (Amᴴ).det := Ne.isUnit (by rw [det_conjTranspose]; exact star_ne_zero.2 hd)
  have hrel : ∀ u u' v v' : Fin g → ℤ, ((cst u + τ *ᵥ cst v) ⬝ᵥ (Am * Hm * Amᴴ) *ᵥ
      star (cst u' + τ *ᵥ cst v')).im = ((v ⬝ᵥ u' - u ⬝ᵥ v' : ℤ) : ℝ) := by
    intro u u' v v'
    have h1 := L.im w hw (mk bas u v) (mk bas u' v')
    rw [hC.per w hw, hC.per w hw, conj_form, hform] at h1
    simp only [uCo_mk, vCo_mk] at h1
    exact h1
  obtain ⟨R, hGR, hRY⟩ := riemann_real τ _ hrel
  have hYR : Y * R = 1 := mul_eq_one_comm.1 hRY
  have hYT : Yᵀ = Y := by
    rw [hYdef, ← Matrix.transpose_map, hC.sym w hw]
  have hMd : (Pr * Y * Pr + (1 - Pr)).det ≠ 0 := M_det hK.1 hK.2.1 fun v _ h => by
    by_contra hv
    have h1 := hYpd.dotProduct_mulVec_pos hv
    rw [star_trivial, h] at h1
    exact lt_irrefl _ h1
  set G' := compInv Pr Y with hG'
  have hPYG : Pr * Y * G' = Pr := pr_Y_compInv hK.1 hMd
  have hG'T : G'ᵀ = G' := compInv_symm hK.2.1 hYT
  have hcomp : G' = compInv Pr ((T0 (expCover a w)).map Complex.im) :=
    compInv_congr (compress hB hK (T0 (expCover a w))
      (fun j => w (Fin.castLE L.a_le j) / (2 * Real.pi * Complex.I)))
  have hQ : chartQ Pr A T0 (expCover a w) = Am⁻¹ * κ[G'] * (Amᴴ)⁻¹ := by
    rw [hcomp]
    rfl
  have hAQ : Am * (Am⁻¹ * κ[G'] * (Amᴴ)⁻¹) * Amᴴ = κ[G'] := by
    calc Am * (Am⁻¹ * κ[G'] * (Amᴴ)⁻¹) * Amᴴ = (Am * Am⁻¹) * κ[G'] * ((Amᴴ)⁻¹ * Amᴴ) := by
          simp only [mul_assoc]
      _ = κ[G'] := by
          rw [Matrix.mul_nonsing_inv _ hunit', Matrix.nonsing_inv_mul _ hunitH, one_mul, mul_one]
  have hRYv : ∀ v : Fin g → ℂ, κ[R] *ᵥ (κ[Y] *ᵥ v) = v := fun v => by
    rw [Matrix.mulVec_mulVec, ← kappa_mul, hRY, kappa_one, Matrix.one_mulVec]
  have hYRv : ∀ v : Fin g → ℂ, κ[Y] *ᵥ (κ[R] *ᵥ v) = v := fun v => by
    rw [Matrix.mulVec_mulVec, ← kappa_mul, hYR, kappa_one, Matrix.one_mulVec]
  have hback : ∀ v : Fin g → ℂ, Amᵀ *ᵥ ((Amᵀ)⁻¹ *ᵥ v) = v := fun v => by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hunit, Matrix.one_mulVec]
  obtain ⟨y₁, hy₁⟩ : ∃ y₁, Amᵀ *ᵥ y₁ = y := ⟨_, hback y⟩
  obtain ⟨p₁, hp₁⟩ : ∃ p₁, p₁ = κ[Y] *ᵥ (κ[G'] *ᵥ y₁) := ⟨_, rfl⟩
  refine ⟨Amᵀ *ᵥ p₁, ?_, ?_, ?_⟩
  · have e : Amᵀ *ᵥ p₁ - y = Amᵀ *ᵥ (p₁ - y₁) := by rw [Matrix.mulVec_sub, hy₁]
    rw [e]
    refine span_mem hC hK hw _ ?_
    rw [Matrix.mulVec_sub, sub_eq_zero, hp₁, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
      ← kappa_mul, ← kappa_mul, hPYG]
  · intro x hx
    obtain ⟨hv, hu⟩ := rad_coords hC x hx
    have hP : L.P w x = Amᵀ *ᵥ cst (uCo bas (x : Λ)) := by
      rw [hC.per w hw, hv, cst_zero, mulVec_zero, add_zero]
    have hPu := pr_kills hB hK _ hu
    have hc : cst (uCo bas (x : Λ)) = fun k => (((uCo bas (x : Λ) k : ℤ) : ℝ) : ℂ) := by
      funext k
      simp [cst]
    have hGu : κ[G'] *ᵥ cst (uCo bas (x : Λ)) = 0 := by
      rw [hc, kappa_mulVec_ofReal, compInv_kill Y hPu]
      funext k
      simp
    have hstar : star (cst (uCo bas (x : Λ))) = cst (uCo bas (x : Λ)) := by
      funext k
      simp [cst]
    rw [hP, conj_form, hstar, hGR, hp₁, dot_adj, dot_adj, kappa_transpose Y, hYT, hYRv,
      kappa_transpose, hG'T, hGu, dotProduct_zero]
  · intro y'
    obtain ⟨y'₁, hy'₁⟩ : ∃ y'₁, Amᵀ *ᵥ y'₁ = y' := ⟨_, hback y'⟩
    have h5 := conj_form Am Hm y'₁ p₁
    have h6 := conj_form Am (Am⁻¹ * κ[G'] * (Amᴴ)⁻¹) y'₁ y₁
    rw [hy'₁] at h5
    rw [hy'₁, hy₁, hAQ] at h6
    rw [h5, hQ, h6, hGR, hp₁, star_kappa_mulVec, star_kappa_mulVec, hRYv]

end Main

theorem quotient_form_rep : ∀ (n a g : ℕ) (Λ : Type) [AddCommGroup Λ] (L : Flat.LogPeriods n a g Λ) (bas : Module.Basis (Fin g ⊕ Fin g) ℤ Λ) (A T0 : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ) (B : Fin a → Matrix (Fin g) (Fin g) ℤ) (c ρ : ℝ) (Pr : Matrix (Fin g) (Fin g) ℝ), IsChart L bas A T0 B c ρ → IsKerProj (∑ j, B j) Pr → ContinuousAt (chartQ Pr A T0) 0 ∧ ∃ ρ' : ℝ, 0 < ρ' ∧ ∀ w ∈ logCover L.a_le, ‖expCover a w‖ < ρ' → ∀ y : Fin g → ℂ, ∃ p : Fin g → ℂ, p - y ∈ Submodule.span ℂ {u | ∃ x : chartW bas B, (∀ x' : chartW bas B, L.E x x' = 0) ∧ u = L.P w x} ∧ (∀ x : chartW bas B, (∀ x' : chartW bas B, L.E x x' = 0) → p ⬝ᵥ L.H (expCover a w) *ᵥ star (L.P w x) = 0) ∧ ∀ y' : Fin g → ℂ, y' ⬝ᵥ L.H (expCover a w) *ᵥ star p = y' ⬝ᵥ chartQ Pr A T0 (expCover a w) *ᵥ star y := by
  intro n a g Λ _ L bas A T0 B c ρ Pr hC hK
  refine ⟨chartQ_cont hC hK, ?_⟩
  have h0 : (0 : Fin n → ℂ) ∈ Metric.ball (0 : Fin n → ℂ) 1 := Metric.mem_ball_self one_pos
  obtain ⟨ρ', K, hρ', _, hinv⟩ := GlobalTheory.CompanionTheory.Ar.RiemannLimit.inv n g A
    (hC.A_cont.continuousAt (Metric.isOpen_ball.mem_nhds h0)) hC.A_det
  refine ⟨ρ', hρ', fun w hw hwn y => rep_at hC hK hw (hinv _ ?_).1 y⟩
  simpa [dist_zero_right] using hwn

end GlobalTheory.CompanionTheory.Ar.Cusp.BoundaryLimit.QuotientForm
