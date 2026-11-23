import Formalism.LocalToGlobal.IndefiniteReal.SchurOrthogonality

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory Matrix
open Formalism.L2.Theta Formalism.IndefR.Mult
open Filter Topology Set Metric
open scoped ContDiff TensorProduct

namespace Formalism.IndefR.SchurOrthogonalityAlt

section Gen

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

open PI.UpqRep PI.KFinSmoothW

variable {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

theorem gvS_integrable {τ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hτ : IsURepOn (UJset ε) τ)
    {Φ : Matrix (Fin n) (Fin n) ℂ → ℂ} (hΦ : Continuous Φ) (hΦc : HasCompactSupport Φ) (x : H) :
    Integrable (fun h => Φ (umat h) • τ (umat h) x) (muG ε) :=
  Gard.integrable_orbit hτ (Φ ∘ umat) (hΦ.comp (Gard.umat_closedEmb ε).continuous)
    (hΦc.comp_isClosedEmbedding (Gard.umat_closedEmb ε)) x

theorem gvS_add {τ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hτ : IsURepOn (UJset ε) τ)
    {Φ : Matrix (Fin n) (Fin n) ℂ → ℂ} (hΦ : Continuous Φ) (hΦc : HasCompactSupport Φ) (x y : H) :
    gv ε τ Φ (x + y) = gv ε τ Φ x + gv ε τ Φ y := by
  unfold gv
  rw [← integral_add (gvS_integrable hτ hΦ hΦc x) (gvS_integrable hτ hΦ hΦc y)]
  congr 1
  funext h
  rw [map_add, smul_add]

theorem gvS_smul {τ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}
    {Φ : Matrix (Fin n) (Fin n) ℂ → ℂ} (c : ℂ) (x : H) :
    gv ε τ Φ (c • x) = c • gv ε τ Φ x := by
  unfold gv
  rw [← integral_smul]
  congr 1
  funext h
  rw [map_smul, smul_comm]

theorem gvS_norm_le {τ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hτ : IsURepOn (UJset ε) τ)
    (Φ : Matrix (Fin n) (Fin n) ℂ → ℂ) (x : H) :
    ‖gv ε τ Φ x‖ ≤ (∫ h, ‖Φ (umat h)‖ ∂(muG ε)) * ‖x‖ := by
  unfold gv
  calc ‖∫ h, Φ (umat h) • τ (umat h) x ∂(muG ε)‖ ≤ ∫ h, ‖Φ (umat h) • τ (umat h) x‖ ∂(muG ε) :=
        norm_integral_le_integral_norm _
    _ = ∫ h, ‖Φ (umat h)‖ * ‖x‖ ∂(muG ε) := by
        congr 1
        funext h
        rw [norm_smul, hτ.2.1 _ h.2 x]
    _ = _ := integral_mul_const _ _

open scoped Matrix.Norms.Operator in
theorem expS_entry_hasDerivAt (Z : Matrix (Fin n) (Fin n) ℂ) (t : ℝ) (i j : Fin n) :
    HasDerivAt (fun u : ℝ => (NormedSpace.exp (u • Z)) i j) ((NormedSpace.exp (t • Z) * Z) i j) t := by
  have h := hasDerivAt_exp_smul_const (𝕂 := ℝ) Z t
  let L : Matrix (Fin n) (Fin n) ℂ →L[ℝ] ℂ :=
    LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℝ ℂ i j)
  exact L.hasFDerivAt.comp_hasDerivAt t h

theorem expS_hasDerivAt (Z : Matrix (Fin n) (Fin n) ℂ) (t : ℝ) :
    HasDerivAt (fun u : ℝ => NormedSpace.exp (u • Z)) (NormedSpace.exp (t • Z) * Z) t := by
  have : HasDerivAt (fun u : ℝ => (fun i j => (NormedSpace.exp (u • Z)) i j : Fin n → Fin n → ℂ))
      (fun i j => (NormedSpace.exp (t • Z) * Z) i j) t := by
    rw [hasDerivAt_pi]
    intro i
    rw [hasDerivAt_pi]
    intro j
    exact expS_entry_hasDerivAt Z t i j
  exact this

theorem expS_continuous (Z : Matrix (Fin n) (Fin n) ℂ) :
    Continuous (fun u : ℝ => NormedSpace.exp (u • Z)) :=
  continuous_iff_continuousAt.2 fun t => (expS_hasDerivAt Z t).continuousAt

theorem expS_mul_neg (Z : Matrix (Fin n) (Fin n) ℂ) (t : ℝ) :
    NormedSpace.exp (t • Z) * NormedSpace.exp (t • -Z) = 1 := by
  rw [← Matrix.exp_add_of_commute _ _ (((Commute.refl Z).neg_right.smul_left t).smul_right t)]
  simp [smul_neg]

theorem expS_neg_mul (Z : Matrix (Fin n) (Fin n) ℂ) (t : ℝ) :
    NormedSpace.exp (t • -Z) * NormedSpace.exp (t • Z) = 1 := by
  have h := expS_mul_neg (-Z) t
  rwa [neg_neg] at h

def expU (Z : Matrix (Fin n) (Fin n) ℂ) (t : ℝ) : (Matrix (Fin n) (Fin n) ℂ)ˣ :=
  ⟨NormedSpace.exp (t • Z), NormedSpace.exp (t • -Z), expS_mul_neg Z t, expS_neg_mul Z t⟩

theorem expS_mem (Z : Matrix (Fin n) (Fin n) ℂ) (hZ : Zᴴ * Jm ε + Jm ε * Z = 0) (t : ℝ) :
    inUJ ε (NormedSpace.exp (t • Z)) := by
  have h := CCRuleCW.lie_smul (Jm ε) Z hZ t
  rw [Complex.coe_smul] at h
  exact CCRuleCW.exp_mem_UH (Jm ε) (t • Z) h

theorem tau_expS_gv {τ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hτ : IsURepOn (UJset ε) τ)
    {Φ : Matrix (Fin n) (Fin n) ℂ → ℂ} (hΦ : Continuous Φ) (hΦc : HasCompactSupport Φ)
    {Z : Matrix (Fin n) (Fin n) ℂ} (hZ : Zᴴ * Jm ε + Jm ε * Z = 0) (t : ℝ) (x : H) :
    τ (NormedSpace.exp (t • Z)) (gv ε τ Φ x) =
      ∫ h, Φ (NormedSpace.exp (t • -Z) * umat h) • τ (umat h) x ∂(muG ε) := by
  have e := Gard.tau_gv hτ Φ hΦ hΦc x (⟨expU Z t, expS_mem Z hZ t⟩ : UJ ε)
  have e2 : Jm ε * (umat (⟨expU Z t, expS_mem Z hZ t⟩ : UJ ε))ᴴ * Jm ε = NormedSpace.exp (t • -Z) := by
    rw [← Gard.umat_inv]
    rfl
  rw [e2] at e
  exact e

def dKer (Z : Matrix (Fin n) (Fin n) ℂ) (Φ : Matrix (Fin n) (Fin n) ℂ → ℂ) : Matrix (Fin n) (Fin n) ℂ → ℂ :=
  fun m => fderiv ℝ Φ m (-Z * m)

theorem dKer_contDiff {Z : Matrix (Fin n) (Fin n) ℂ} {Φ : Matrix (Fin n) (Fin n) ℂ → ℂ}
    (hΦ : ContDiff ℝ ∞ Φ) : ContDiff ℝ ∞ (dKer Z Φ) := by
  exact ContDiff.fderiv_apply (f := fun _ m => Φ m) (hΦ.comp contDiff_snd) contDiff_id
    (PI.BesselDerivW.mulLc (-Z)).contDiff (by simp)

theorem dKer_hasCompactSupport {Z : Matrix (Fin n) (Fin n) ℂ} {Φ : Matrix (Fin n) (Fin n) ℂ → ℂ}
    (hΦc : HasCompactSupport Φ) : HasCompactSupport (dKer Z Φ) := by
  refine (hΦc.fderiv ℝ).mono ?_
  intro m hm h0
  apply hm
  show fderiv ℝ Φ m (-Z * m) = 0
  rw [h0]
  rfl

theorem kerDeriv_continuous {Φ : Matrix (Fin n) (Fin n) ℂ → ℂ} (hΦ : ContDiff ℝ ∞ Φ)
    (Z : Matrix (Fin n) (Fin n) ℂ) {X : Type*} [TopologicalSpace X] {a : X → ℝ}
    {m : X → Matrix (Fin n) (Fin n) ℂ} (ha : Continuous a) (hm : Continuous m) :
    Continuous fun x =>
      fderiv ℝ Φ (NormedSpace.exp (a x • -Z) * m x) (NormedSpace.exp (a x • -Z) * -Z * m x) := by
  have hb := expS_continuous (n := n) (-Z)
  exact ((hΦ.continuous_fderiv (by simp)).comp ((hb.comp ha).mul hm)).clm_apply
    (((hb.comp ha).mul continuous_const).mul hm)

theorem hasDerivAt_ker {Φ : Matrix (Fin n) (Fin n) ℂ → ℂ} (hΦ : ContDiff ℝ ∞ Φ)
    (Z m : Matrix (Fin n) (Fin n) ℂ) (t : ℝ) :
    HasDerivAt (fun u : ℝ => Φ (NormedSpace.exp (u • -Z) * m))
      (fderiv ℝ Φ (NormedSpace.exp (t • -Z) * m) (NormedSpace.exp (t • -Z) * -Z * m)) t := by
  have h1 : HasDerivAt (fun u : ℝ => NormedSpace.exp (u • -Z) * m) (NormedSpace.exp (t • -Z) * -Z * m) t :=
    (PI.BesselDerivW.mulRc m).hasFDerivAt.comp_hasDerivAt t (expS_hasDerivAt (-Z) t)
  exact ((hΦ.differentiable (by simp)).differentiableAt.hasFDerivAt).comp_hasDerivAt t h1

theorem ker_vanish {Φ : Matrix (Fin n) (Fin n) ℂ → ℂ} (Z m : Matrix (Fin n) (Fin n) ℂ) (t : ℝ)
    (hne : fderiv ℝ Φ (NormedSpace.exp (t • -Z) * m) (NormedSpace.exp (t • -Z) * -Z * m) ≠ 0) :
    NormedSpace.exp (t • -Z) * m ∈ tsupport Φ := by
  apply tsupport_fderiv_subset ℝ
  apply subset_tsupport
  intro h0
  apply hne
  rw [h0]
  rfl

theorem kerBound {Φ : Matrix (Fin n) (Fin n) ℂ → ℂ} (hΦ : ContDiff ℝ ∞ Φ) (hΦc : HasCompactSupport Φ)
    (Z : Matrix (Fin n) (Fin n) ℂ) :
    ∃ bnd : UJ ε → ℝ, Continuous bnd ∧ HasCompactSupport bnd ∧ ∀ (h : UJ ε), ∀ t ∈ Icc (-1 : ℝ) 1,
      ‖fderiv ℝ Φ (NormedSpace.exp (t • -Z) * umat h) (NormedSpace.exp (t • -Z) * -Z * umat h)‖ ≤ bnd h := by
  have hum : Continuous (umat : UJ ε → Matrix (Fin n) (Fin n) ℂ) := (Gard.umat_closedEmb ε).continuous
  have hf : Continuous (fun p : UJ ε × ℝ =>
      ‖fderiv ℝ Φ (NormedSpace.exp (p.2 • -Z) * umat p.1) (NormedSpace.exp (p.2 • -Z) * -Z * umat p.1)‖) :=
    (kerDeriv_continuous hΦ Z continuous_snd (hum.comp continuous_fst)).norm
  have hfc : ∀ h : UJ ε, Continuous (fun t : ℝ =>
      ‖fderiv ℝ Φ (NormedSpace.exp (t • -Z) * umat h) (NormedSpace.exp (t • -Z) * -Z * umat h)‖) :=
    fun h => (kerDeriv_continuous hΦ Z continuous_id continuous_const).norm
  have hKc : IsCompact ((fun q : ℝ × Matrix (Fin n) (Fin n) ℂ => NormedSpace.exp (q.1 • Z) * q.2) ''
      (Icc (-1 : ℝ) 1 ×ˢ tsupport Φ)) :=
    (isCompact_Icc.prod hΦc).image (((expS_continuous Z).comp continuous_fst).mul continuous_snd)
  have hvan : ∀ h : UJ ε, umat h ∉ ((fun q : ℝ × Matrix (Fin n) (Fin n) ℂ => NormedSpace.exp (q.1 • Z) * q.2) ''
      (Icc (-1 : ℝ) 1 ×ˢ tsupport Φ)) → ∀ t ∈ Icc (-1 : ℝ) 1,
      ‖fderiv ℝ Φ (NormedSpace.exp (t • -Z) * umat h) (NormedSpace.exp (t • -Z) * -Z * umat h)‖ = 0 := by
    intro h hh t ht
    rw [norm_eq_zero]
    by_contra hne
    apply hh
    refine ⟨(t, NormedSpace.exp (t • -Z) * umat h), ⟨ht, ker_vanish Z (umat h) t hne⟩, ?_⟩
    show NormedSpace.exp (t • Z) * (NormedSpace.exp (t • -Z) * umat h) = umat h
    rw [← Matrix.mul_assoc, expS_mul_neg, Matrix.one_mul]
  refine ⟨fun h => sSup ((fun t : ℝ =>
      ‖fderiv ℝ Φ (NormedSpace.exp (t • -Z) * umat h) (NormedSpace.exp (t • -Z) * -Z * umat h)‖) ''
        Icc (-1 : ℝ) 1), isCompact_Icc.continuous_sSup hf, ?_, ?_⟩
  · refine HasCompactSupport.intro ((Gard.umat_closedEmb ε).isCompact_preimage hKc) ?_
    intro h hh
    have him : (fun t : ℝ =>
        ‖fderiv ℝ Φ (NormedSpace.exp (t • -Z) * umat h) (NormedSpace.exp (t • -Z) * -Z * umat h)‖) ''
          Icc (-1 : ℝ) 1 = {0} := by
      apply Set.eq_singleton_iff_unique_mem.2
      refine ⟨⟨0, ⟨by norm_num, by norm_num⟩, hvan h hh 0 ⟨by norm_num, by norm_num⟩⟩, ?_⟩
      rintro _ ⟨t, ht, rfl⟩
      exact hvan h hh t ht
    simp only [him, csSup_singleton]
  · intro h t ht
    exact le_csSup (isCompact_Icc.image (hfc h)).bddAbove (mem_image_of_mem _ ht)

theorem hasDerivAt_tau_gv {τ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hτ : IsURepOn (UJset ε) τ)
    {Φ : Matrix (Fin n) (Fin n) ℂ → ℂ} (hΦ : ContDiff ℝ ∞ Φ) (hΦc : HasCompactSupport Φ)
    {Z : Matrix (Fin n) (Fin n) ℂ} (hZ : Zᴴ * Jm ε + Jm ε * Z = 0) (x : H) :
    HasDerivAt (fun t : ℝ => τ (NormedSpace.exp (t • Z)) (gv ε τ Φ x)) (gv ε τ (dKer Z Φ) x) 0 := by
  have hum : Continuous (umat : UJ ε → Matrix (Fin n) (Fin n) ℂ) := (Gard.umat_closedEmb ε).continuous
  obtain ⟨bnd, hbc, hbs, hle⟩ := kerBound (ε := ε) hΦ hΦc Z
  have hbi : Integrable (fun h => ‖x‖ * bnd h) (muG ε) := (hbc.integrable_of_hasCompactSupport hbs).const_mul _
  have e0 : NormedSpace.exp ((0 : ℝ) • -Z) = 1 := by simp
  have hFm : ∀ᶠ t in 𝓝 (0 : ℝ), AEStronglyMeasurable
      (fun h : UJ ε => Φ (NormedSpace.exp (t • -Z) * umat h) • τ (umat h) x) (muG ε) :=
    Eventually.of_forall fun t =>
      ((hΦ.continuous.comp ((PI.BesselDerivW.mulLc (NormedSpace.exp (t • -Z))).continuous.comp hum)).smul
        (Gard.cont_orbit hτ x)).aestronglyMeasurable
  have hFi : Integrable (fun h : UJ ε => Φ (NormedSpace.exp ((0 : ℝ) • -Z) * umat h) • τ (umat h) x)
      (muG ε) := by
    rw [e0]
    simp only [Matrix.one_mul]
    exact gvS_integrable hτ hΦ.continuous hΦc x
  have hF'm : AEStronglyMeasurable (fun h : UJ ε =>
      fderiv ℝ Φ (NormedSpace.exp ((0 : ℝ) • -Z) * umat h) (NormedSpace.exp ((0 : ℝ) • -Z) * -Z * umat h) •
        τ (umat h) x) (muG ε) :=
    ((kerDeriv_continuous hΦ Z continuous_const hum).smul (Gard.cont_orbit hτ x)).aestronglyMeasurable
  have hbd : ∀ᵐ h ∂(muG ε), ∀ t ∈ ball (0 : ℝ) 1,
      ‖fderiv ℝ Φ (NormedSpace.exp (t • -Z) * umat h) (NormedSpace.exp (t • -Z) * -Z * umat h) •
        τ (umat h) x‖ ≤ ‖x‖ * bnd h := by
    refine Eventually.of_forall fun h t ht => ?_
    rw [Real.ball_eq_Ioo, zero_sub, zero_add] at ht
    rw [norm_smul, hτ.2.1 _ h.2 x, mul_comm]
    exact mul_le_mul_of_nonneg_left (hle h t ⟨ht.1.le, ht.2.le⟩) (norm_nonneg x)
  have hdiff : ∀ᵐ h ∂(muG ε), ∀ t ∈ ball (0 : ℝ) 1,
      HasDerivAt (fun u : ℝ => Φ (NormedSpace.exp (u • -Z) * umat h) • τ (umat h) x)
        (fderiv ℝ Φ (NormedSpace.exp (t • -Z) * umat h) (NormedSpace.exp (t • -Z) * -Z * umat h) •
          τ (umat h) x) t :=
    Eventually.of_forall fun h t _ => (hasDerivAt_ker hΦ Z (umat h) t).smul_const (τ (umat h) x)
  have hD := (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := muG ε)
    (F := fun (t : ℝ) (h : UJ ε) => Φ (NormedSpace.exp (t • -Z) * umat h) • τ (umat h) x)
    (F' := fun (t : ℝ) (h : UJ ε) =>
      fderiv ℝ Φ (NormedSpace.exp (t • -Z) * umat h) (NormedSpace.exp (t • -Z) * -Z * umat h) • τ (umat h) x)
    (x₀ := 0) (bound := fun h => ‖x‖ * bnd h) (ball_mem_nhds (0 : ℝ) one_pos) hFm hFi hF'm hbd hbi hdiff).2
  have e1 : (fun t : ℝ => τ (NormedSpace.exp (t • Z)) (gv ε τ Φ x)) =
      fun t : ℝ => ∫ h, Φ (NormedSpace.exp (t • -Z) * umat h) • τ (umat h) x ∂(muG ε) :=
    funext fun t => tau_expS_gv hτ hΦ.continuous hΦc hZ t x
  have e2 : ∫ h, fderiv ℝ Φ (NormedSpace.exp ((0 : ℝ) • -Z) * umat h)
      (NormedSpace.exp ((0 : ℝ) • -Z) * -Z * umat h) • τ (umat h) x ∂(muG ε) = gv ε τ (dKer Z Φ) x := by
    rw [e0]
    simp only [Matrix.one_mul]
    rfl
  rw [e1, ← e2]
  exact hD

end Gen

section Model

attribute [local instance] Formalism.BasicNotions.Host.cmStar Matrix.normedAddCommGroup Matrix.normedSpace

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar}

def gvT (M : DSModel V S) (τ : D.what₂.Tau) (Φ : Matrix (Fin V.rank) (Fin V.rank) ℂ → ℂ) (w : M.H τ) : M.H τ :=
  PI.KFinSmoothW.gv (M.ε τ) (M.σ τ) Φ w

theorem urep (M : DSModel V S) (τ : D.what₂.Tau) :
    PI.UpqRep.IsURepOn (PI.UpqRep.UJset (M.ε τ)) (M.σ τ) :=
  Formalism.IndefR.PeterssonHilbertSpace.sm_isURepOn_bridge (M.ε τ) (M.σ τ) (M.ds τ).2.2.1

theorem gvT_smooth (M : DSModel V S) (τ : D.what₂.Tau) {Φ : Matrix (Fin V.rank) (Fin V.rank) ℂ → ℂ}
    (hΦ : ContDiff ℝ ∞ Φ) (hΦc : HasCompactSupport Φ) (w : M.H τ) :
    SmoothVec (lieAt V τ) (M.rep τ) (gvT M τ Φ w) := by
  have : CompleteSpace (M.H τ) := (M.ds τ).1
  exact Formalism.IndefR.PeterssonHilbertSpace.sm_transfer (M.ε τ) (M.σ τ) (M.fr τ) _ (M.fr_unit τ) (M.fr_gram τ) (lieAt V τ)
    (fun X hX => hX) _ (PI.KFinSmoothW.garding_vectors_smooth _ (M.ε τ) (M.H τ) (M.σ τ) (urep M τ) Φ hΦ hΦc w)

def gvTL (M : DSModel V S) (τ : D.what₂.Tau) (Φ : Matrix (Fin V.rank) (Fin V.rank) ℂ → ℂ)
    (hΦ : Continuous Φ) (hΦc : HasCompactSupport Φ) : M.H τ →ₗ[ℂ] M.H τ where
  toFun := gvT M τ Φ
  map_add' x y := by
    have : CompleteSpace (M.H τ) := (M.ds τ).1
    exact gvS_add (urep M τ) hΦ hΦc x y
  map_smul' c x := by
    have : CompleteSpace (M.H τ) := (M.ds τ).1
    exact gvS_smul c x

theorem gvT_norm_le (M : DSModel V S) (τ : D.what₂.Tau) (Φ : Matrix (Fin V.rank) (Fin V.rank) ℂ → ℂ)
    (w : M.H τ) :
    ‖gvT M τ Φ w‖ ≤ (∫ h, ‖Φ (PI.UpqRep.umat h)‖ ∂(PI.UpqRep.muG (M.ε τ))) * ‖w‖ := by
  have : CompleteSpace (M.H τ) := (M.ds τ).1
  exact gvS_norm_le (urep M τ) Φ w

def gvTC (M : DSModel V S) (τ : D.what₂.Tau) (Φ : Matrix (Fin V.rank) (Fin V.rank) ℂ → ℂ)
    (hΦ : Continuous Φ) (hΦc : HasCompactSupport Φ) : M.H τ →L[ℂ] M.H τ :=
  (gvTL M τ Φ hΦ hΦc).mkContinuous _ (gvT_norm_le M τ Φ)

theorem conj_lie (M : DSModel V S) (τ : D.what₂.Tau) {X : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hX : X ∈ lieAt V τ) :
    (M.fr τ * X * (M.fr τ)⁻¹)ᴴ * PI.UpqRep.Jm (M.ε τ) +
      PI.UpqRep.Jm (M.ε τ) * (M.fr τ * X * (M.fr τ)⁻¹) = 0 := by
  have hX' : Xᴴ * gramAt D V τ + gramAt D V τ * X = 0 := hX
  have h1 := fr_mul_inv M τ
  have h2 : ((M.fr τ)⁻¹)ᴴ * (M.fr τ)ᴴ = 1 := by rw [← conjTranspose_mul, h1, conjTranspose_one]
  rw [← M.fr_gram τ] at hX'
  change (M.fr τ * X * (M.fr τ)⁻¹)ᴴ * Formalism.REAL.Jm (M.ε τ) +
      Formalism.REAL.Jm (M.ε τ) * (M.fr τ * X * (M.fr τ)⁻¹) = 0
  calc (M.fr τ * X * (M.fr τ)⁻¹)ᴴ * Formalism.REAL.Jm (M.ε τ) + Formalism.REAL.Jm (M.ε τ) * (M.fr τ * X * (M.fr τ)⁻¹)
      = ((M.fr τ)⁻¹)ᴴ * (Xᴴ * ((M.fr τ)ᴴ * Formalism.REAL.Jm (M.ε τ) * M.fr τ) +
          ((M.fr τ)ᴴ * Formalism.REAL.Jm (M.ε τ) * M.fr τ) * X) * (M.fr τ)⁻¹ := by
        simp only [conjTranspose_mul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
        rw [h1, Matrix.mul_one, ← Matrix.mul_assoc ((M.fr τ)⁻¹)ᴴ (M.fr τ)ᴴ, h2, Matrix.one_mul]
    _ = 0 := by rw [hX']; simp

theorem rep_exp (M : DSModel V S) (τ : D.what₂.Tau) (X : Matrix (Fin V.rank) (Fin V.rank) ℂ) (t : ℝ) :
    M.rep τ (NormedSpace.exp (t • X)) = M.σ τ (NormedSpace.exp (t • (M.fr τ * X * (M.fr τ)⁻¹))) := by
  show M.σ τ (M.fr τ * NormedSpace.exp (t • X) * (M.fr τ)⁻¹) = _
  rw [← Matrix.exp_conj _ _ (M.fr_unit τ), Matrix.mul_smul, Matrix.smul_mul]

theorem dRep_gvT (M : DSModel V S) (τ : D.what₂.Tau) {Φ : Matrix (Fin V.rank) (Fin V.rank) ℂ → ℂ}
    (hΦ : ContDiff ℝ ∞ Φ) (hΦc : HasCompactSupport Φ) {X : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hX : X ∈ lieAt V τ) (w : M.H τ) :
    dRep (M.rep τ) X (gvT M τ Φ w) = gvT M τ (dKer (M.fr τ * X * (M.fr τ)⁻¹) Φ) w := by
  have : CompleteSpace (M.H τ) := (M.ds τ).1
  unfold dRep
  simp only [rep_exp]
  exact (hasDerivAt_tau_gv (urep M τ) hΦ hΦc (conj_lie M τ hX) w).deriv

theorem foldr_gvT (M : DSModel V S) (τ : D.what₂.Tau) :
    ∀ (l : List (Matrix (Fin V.rank) (Fin V.rank) ℂ)), (∀ X ∈ l, X ∈ lieAt V τ) →
      ∀ Φ : Matrix (Fin V.rank) (Fin V.rank) ℂ → ℂ, ContDiff ℝ ∞ Φ → HasCompactSupport Φ →
        ∃ Ψ : Matrix (Fin V.rank) (Fin V.rank) ℂ → ℂ, ContDiff ℝ ∞ Ψ ∧ HasCompactSupport Ψ ∧
          ∀ w, l.foldr (dRep (M.rep τ)) (gvT M τ Φ w) = gvT M τ Ψ w
  | [], _, Φ, hΦ, hΦc => ⟨Φ, hΦ, hΦc, fun _ => rfl⟩
  | X :: l, hl, Φ, hΦ, hΦc => by
    obtain ⟨Ψ, hΨ, hΨc, e⟩ := foldr_gvT M τ l (fun Y hY => hl Y (List.mem_cons_of_mem _ hY)) Φ hΦ hΦc
    refine ⟨dKer (M.fr τ * X * (M.fr τ)⁻¹) Ψ, dKer_contDiff hΨ, dKer_hasCompactSupport hΨc, fun w => ?_⟩
    rw [List.foldr_cons, e w]
    exact dRep_gvT M τ hΨ hΨc (hl X (by simp)) w

theorem foldr_gvT_le (M : DSModel V S) (τ : D.what₂.Tau) {Φ : Matrix (Fin V.rank) (Fin V.rank) ℂ → ℂ}
    (hΦ : ContDiff ℝ ∞ Φ) (hΦc : HasCompactSupport Φ) (l : List (Matrix (Fin V.rank) (Fin V.rank) ℂ))
    (hl : ∀ X ∈ l, X ∈ lieAt V τ) :
    ∃ c : ℝ, ∀ w, ‖l.foldr (dRep (M.rep τ)) (gvT M τ Φ w)‖ ≤ c * ‖w‖ := by
  obtain ⟨Ψ, -, -, e⟩ := foldr_gvT M τ l hl Φ hΦ hΦc
  exact ⟨_, fun w => by rw [e w]; exact gvT_norm_le M τ Ψ w⟩

theorem sum_gvT_le (M : DSModel V S) (τ : D.what₂.Tau) {Φ : Matrix (Fin V.rank) (Fin V.rank) ℂ → ℂ}
    (hΦ : ContDiff ℝ ∞ Φ) (hΦc : HasCompactSupport Φ) :
    ∀ (L : List (List (Matrix (Fin V.rank) (Fin V.rank) ℂ))), (∀ l ∈ L, ∀ X ∈ l, X ∈ lieAt V τ) →
      ∃ c : ℝ, ∀ w, (L.map fun l => ‖l.foldr (dRep (M.rep τ)) (gvT M τ Φ w)‖).sum ≤ c * ‖w‖
  | [], _ => ⟨0, fun w => by simp⟩
  | l :: L, hL => by
    obtain ⟨c1, h1⟩ := foldr_gvT_le M τ hΦ hΦc l (hL l (by simp))
    obtain ⟨c2, h2⟩ := sum_gvT_le M τ hΦ hΦc L (fun l' hl' => hL l' (List.mem_cons_of_mem _ hl'))
    exact ⟨c1 + c2, fun w => by
      rw [List.map_cons, List.sum_cons, add_mul]
      exact add_le_add (h1 w) (h2 w)⟩

theorem gvT_bd (M : DSModel V S) (τ : D.what₂.Tau) {Φ : Matrix (Fin V.rank) (Fin V.rank) ℂ → ℂ}
    (hΦ : ContDiff ℝ ∞ Φ) (hΦc : HasCompactSupport Φ) {ℓ : M.H τ →ₗ[ℂ] ℂ}
    {L : List (List (Matrix (Fin V.rank) (Fin V.rank) ℂ))} {C c : ℝ}
    (hC : ∀ w, SmoothVec (lieAt V τ) (M.rep τ) w →
      ‖ℓ w‖ ≤ C * (L.map fun l => ‖l.foldr (dRep (M.rep τ)) w‖).sum)
    (hc : ∀ w, (L.map fun l => ‖l.foldr (dRep (M.rep τ)) (gvT M τ Φ w)‖).sum ≤ c * ‖w‖) (w : M.H τ) :
    ‖ℓ (gvT M τ Φ w)‖ ≤ |C| * c * ‖w‖ := by
  have h1 := hC _ (gvT_smooth M τ hΦ hΦc w)
  have h0 := sum_map_norm_nonneg (σ := M.rep τ) L (gvT M τ Φ w)
  calc ‖ℓ (gvT M τ Φ w)‖ ≤ C * (L.map fun l => ‖l.foldr (dRep (M.rep τ)) (gvT M τ Φ w)‖).sum := h1
    _ ≤ |C| * (L.map fun l => ‖l.foldr (dRep (M.rep τ)) (gvT M τ Φ w)‖).sum :=
        mul_le_mul_of_nonneg_right (le_abs_self C) h0
    _ ≤ |C| * (c * ‖w‖) := mul_le_mul_of_nonneg_left (hc w) (abs_nonneg C)
    _ = |C| * c * ‖w‖ := by ring

end Model

section Meet

attribute [local instance] Formalism.BasicNotions.Host.cmStar Matrix.normedAddCommGroup Matrix.normedSpace

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar}

def GvPair : Prop :=
  ∀ {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (τ : D.what₂.Tau)
    (Φ : Matrix (Fin V.rank) (Fin V.rank) ℂ → ℂ), ContDiff ℝ ∞ Φ → HasCompactSupport Φ →
    ∀ ℓ : M.H τ →ₗ[ℂ] ℂ, Sobolev₂ (lieAt V τ) (M.rep τ) ℓ → ∀ w ∈ M.sm τ,
      ℓ (gvT M τ Φ w) =
        ∫ h, Φ (PI.UpqRep.umat h) * ℓ (M.σ τ (PI.UpqRep.umat h) w) ∂(PI.UpqRep.muG (M.ε τ))

theorem conj_back_mem (M : DSModel V S) (τ : D.what₂.Tau) (h : PI.UpqRep.UJ (M.ε τ)) :
    (M.fr τ)⁻¹ * PI.UpqRep.umat h * M.fr τ ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ) := by
  have hh' : (PI.UpqRep.umat h)ᴴ * Formalism.REAL.Jm (M.ε τ) * PI.UpqRep.umat h = Formalism.REAL.Jm (M.ε τ) := h.2
  show ((M.fr τ)⁻¹ * PI.UpqRep.umat h * M.fr τ)ᴴ * gramAt D V τ * ((M.fr τ)⁻¹ * PI.UpqRep.umat h * M.fr τ) =
    gramAt D V τ
  rw [← M.fr_gram τ]
  calc ((M.fr τ)⁻¹ * PI.UpqRep.umat h * M.fr τ)ᴴ * ((M.fr τ)ᴴ * Formalism.REAL.Jm (M.ε τ) * M.fr τ) *
        ((M.fr τ)⁻¹ * PI.UpqRep.umat h * M.fr τ)
      = (M.fr τ)ᴴ * (PI.UpqRep.umat h)ᴴ * ((M.fr τ * (M.fr τ)⁻¹)ᴴ * Formalism.REAL.Jm (M.ε τ) *
          (M.fr τ * (M.fr τ)⁻¹)) * PI.UpqRep.umat h * M.fr τ := by
        simp only [conjTranspose_mul, Matrix.mul_assoc]
    _ = (M.fr τ)ᴴ * ((PI.UpqRep.umat h)ᴴ * Formalism.REAL.Jm (M.ε τ) * PI.UpqRep.umat h) * M.fr τ := by
        rw [fr_mul_inv]; simp only [conjTranspose_one, Matrix.one_mul, Matrix.mul_one, Matrix.mul_assoc]
    _ = (M.fr τ)ᴴ * Formalism.REAL.Jm (M.ε τ) * M.fr τ := by rw [hh']

theorem rep_conj_back (M : DSModel V S) (τ : D.what₂.Tau) (h : PI.UpqRep.UJ (M.ε τ)) :
    M.rep τ ((M.fr τ)⁻¹ * PI.UpqRep.umat h * M.fr τ) = M.σ τ (PI.UpqRep.umat h) := by
  show M.σ τ (M.fr τ * ((M.fr τ)⁻¹ * PI.UpqRep.umat h * M.fr τ) * (M.fr τ)⁻¹) = _
  congr 1
  calc M.fr τ * ((M.fr τ)⁻¹ * PI.UpqRep.umat h * M.fr τ) * (M.fr τ)⁻¹
      = (M.fr τ * (M.fr τ)⁻¹) * PI.UpqRep.umat h * (M.fr τ * (M.fr τ)⁻¹) := by simp only [Matrix.mul_assoc]
    _ = PI.UpqRep.umat h := by rw [fr_mul_inv]; simp

def DerivUnifOn (M : DSModel V S) (τ : D.what₂.Tau) (A : M.sm τ →ₗ[ℂ] (GA D V → ℂ)) (K : Set (GA D V)) : Prop :=
  ∃ (L : List (List (Matrix (Fin V.rank) (Fin V.rank) ℂ))) (C : ℝ), (∀ l ∈ L, ∀ X ∈ l, X ∈ lieAt V τ) ∧
    ∀ y ∈ K, ∀ (w : M.H τ) (hw : SmoothVec (lieAt V τ) (M.rep τ) w),
      ‖A ⟨w, Submodule.subset_span hw⟩ y‖ ≤ C * (L.map fun l => ‖l.foldr (dRep (M.rep τ)) w‖).sum

end Meet

end Formalism.IndefR.SchurOrthogonalityAlt

end
