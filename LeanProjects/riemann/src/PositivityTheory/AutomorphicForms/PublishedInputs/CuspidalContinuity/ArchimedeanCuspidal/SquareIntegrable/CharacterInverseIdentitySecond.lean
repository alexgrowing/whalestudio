import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.SquareIntegrable.SSmooth

noncomputable section

open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic
open scoped ValuativeRel

set_option linter.unusedSectionVars false

namespace Ad3.SchwartzSpaceL2.PFe

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F]

theorem isUnit1_mul {μ ν : Fˣ →* ℂˣ} (hμ : IsUnit1 μ) (hν : IsUnit1 ν) : IsUnit1 (μ * ν) := by
  refine ⟨?_, fun x => ?_⟩
  · exact hμ.1.mul hν.1
  · simp [MonoidHom.mul_apply, Units.val_mul, norm_mul, hμ.2 x, hν.2 x]

theorem isUnit1_inv {μ : Fˣ →* ℂˣ} (hμ : IsUnit1 μ) : IsUnit1 μ⁻¹ := by
  refine ⟨?_, fun x => ?_⟩
  · exact hμ.1.inv
  · simp [MonoidHom.inv_apply, Units.val_inv_eq_inv_val, norm_inv, hμ.2 x]

theorem mp_add (a : Fˣ) (s t : ℂ) : mp a s * mp a t = mp a (s + t) := by
  unfold mp
  rw [Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr (NNReal.coe_ne_zero.mpr (modulus_pos a.ne_zero).ne'))]

theorem mp_one (s : ℂ) : mp (1 : Fˣ) s = 1 := by
  unfold mp
  simp [modulus_one]

theorem det_weyl_GL2 : GeneralLinearGroup.det (w0 : GL (Fin 2) F) = 1 := by
  ext
  simp [w0, Matrix.det_fin_two]

theorem rightTranslate_pureTensor_weyl (f g : F → ℂ) : rt (pt f g) (w0 : GL (Fin 2) F) = pt g (fun x => f (-x)) := by
  funext x
  simp [rt, pt, w0, Matrix.vecMul, dotProduct, Fin.sum_univ_two, mul_comm]

theorem pt_mem {f g : F → ℂ} (hf : f ∈ schwartzBruhat F) (hg : g ∈ schwartzBruhat F) :
    pt f g ∈ GodementSectionLocal.schwartzBruhat2 F := by
  refine ⟨?_, ?_⟩
  · exact (hf.1.comp_continuous (continuous_apply 0)).mul (hg.1.comp_continuous (continuous_apply 1))
  · refine HasCompactSupport.intro ((hf.2.isCompact.prod hg.2.isCompact).image
      (f := fun p : F × F => ![p.1, p.2]) ?_) ?_
    · exact continuous_pi fun i => by fin_cases i <;> simp <;> fun_prop
    · intro x hx
      by_contra h
      apply hx
      refine ⟨(x 0, x 1), ⟨subset_tsupport _ ?_, subset_tsupport _ ?_⟩, ?_⟩
      · exact Function.mem_support.mpr fun h0 => h (by simp [pt, h0])
      · exact Function.mem_support.mpr fun h1 => h (by simp [pt, h1])
      · ext i; fin_cases i <;> rfl

theorem comp_neg_mem {f : F → ℂ} (hf : f ∈ schwartzBruhat F) :
    (fun x => f (-x)) ∈ schwartzBruhat F :=
  ⟨hf.1.comp_continuous continuous_neg, hf.2.comp_homeomorph (Homeomorph.neg F)⟩

theorem fourier_mem {ψ : AddChar F Circle} (hψ : IsStd ψ) {f : F → ℂ} (hf : f ∈ schwartzBruhat F) :
    localFourier (selfDualMeasure ψ) ψ f ∈ schwartzBruhat F :=
  localFourier_mem_schwartzBruhat (μ := selfDualMeasure ψ) (hψ := hψ.1) (hψ1 := hψ.2.1) hf

theorem character_inverse_identity_first (μ₁ μ₂ c : Fˣ →* ℂˣ) : μ₂ * c * (μ₁⁻¹ * μ₂)⁻¹ = μ₁ * c := by
  ext x
  simp only [MonoidHom.mul_apply, MonoidHom.inv_apply, Units.val_mul, Units.val_inv_eq_inv_val]
  field_simp

theorem character_inverse_identity_second (μ₁ μ₂ c : Fˣ →* ℂˣ) : (μ₁ * c)⁻¹ * (μ₁⁻¹ * μ₂)⁻¹ = (μ₂ * c)⁻¹ := by
  ext x
  simp only [MonoidHom.mul_apply, MonoidHom.inv_apply, Units.val_mul, Units.val_inv_eq_inv_val]
  field_simp

theorem rhs_pure (hDZ : SDZ) (hWd : SWd) {ψ : AddChar F Circle} (hψ : IsStd ψ) {μ₁ μ₂ : Fˣ →* ℂˣ}
    (h₁ : IsUnit1 μ₁) (h₂ : IsUnit1 μ₂) {f g : F → ℂ} (hf : f ∈ schwartzBruhat F)
    (hg : g ∈ schwartzBruhat F) {c : Fˣ →* ℂˣ} (hc : IsUnit1 c) {s : ℂ} (hs : 0 < s.re) :
    Integrable (fun a : Fˣ => W2 ψ μ₁ μ₂ (pt f g) (dg2 a 1) * ((c a : ℂˣ) : ℂ) * mp a (s - 1 / 2))
        (multHaar F) ∧
      ∫ a, W2 ψ μ₁ μ₂ (pt f g) (dg2 a 1) * ((c a : ℂˣ) : ℂ) * mp a (s - 1 / 2) ∂multHaar F =
        localZeta f (μ₂ * c) s *
          localZeta (fun x => localFourier (selfDualMeasure ψ) ψ g (-x)) (μ₁ * c) s := by
  obtain ⟨hI, hE⟩ := hDZ F f hf (fun x => localFourier (selfDualMeasure ψ) ψ g (-x))
    (comp_neg_mem (fourier_mem hψ hg)) (μ₂ * c) (μ₁⁻¹ * μ₂) (isUnit1_mul h₂ hc)
    (isUnit1_mul (isUnit1_inv h₁) h₂) s hs
  beta_reduce at hI hE
  have hfun : (fun a : Fˣ => W2 ψ μ₁ μ₂ (pt f g) (dg2 a 1) * ((c a : ℂˣ) : ℂ) * mp a (s - 1 / 2)) =
      fun a => (((μ₂ * c) a : ℂˣ) : ℂ) * mp a s *
        ∫ h : Fˣ, (((μ₁⁻¹ * μ₂) h : ℂˣ) : ℂ) * f ((h : F) * a) *
          localFourier (selfDualMeasure ψ) ψ g (-((h⁻¹ : Fˣ) : F)) ∂multHaar F := by
    funext a
    have key : mp a (1 / 2) * mp a (s - 1 / 2) = mp a s := by rw [mp_add]; congr 1; ring
    rw [hWd F ψ hψ μ₁ μ₂ h₁ h₂ f hf g hg a, ← key]
    simp only [MonoidHom.mul_apply, MonoidHom.inv_apply, Units.val_mul]
    ring
  rw [hfun]
  exact ⟨hI, by rw [hE, character_inverse_identity_first]⟩

theorem lhs_pure (hDZ : SDZ) (hWd : SWd) (hTr : STrans) {ψ : AddChar F Circle} (hψ : IsStd ψ)
    {μ₁ μ₂ : Fˣ →* ℂˣ} (h₁ : IsUnit1 μ₁) (h₂ : IsUnit1 μ₂) {f g : F → ℂ} (hf : f ∈ schwartzBruhat F)
    (hg : g ∈ schwartzBruhat F) {c : Fˣ →* ℂˣ} (hc : IsUnit1 c) {s : ℂ} (hs : s.re < 1) :
    Integrable (fun a : Fˣ => W2 ψ μ₁ μ₂ (pt f g) (dg2 a 1 * w0) * (((μ₁ a * μ₂ a * c a)⁻¹ : ℂˣ) : ℂ) *
        mp a (1 / 2 - s)) (multHaar F) ∧
      ∫ a, W2 ψ μ₁ μ₂ (pt f g) (dg2 a 1 * w0) * (((μ₁ a * μ₂ a * c a)⁻¹ : ℂˣ) : ℂ) *
          mp a (1 / 2 - s) ∂multHaar F =
        localZeta g (μ₁ * c)⁻¹ (1 - s) *
          localZeta (fun x => localFourier (selfDualMeasure ψ) ψ (fun y => f (-y)) (-x)) (μ₂ * c)⁻¹ (1 - s) := by
  have hf' := comp_neg_mem hf
  have hs' : 0 < (1 - s).re := by simp; linarith
  obtain ⟨hI, hE⟩ := hDZ F g hg (fun x => localFourier (selfDualMeasure ψ) ψ (fun y => f (-y)) (-x))
    (comp_neg_mem (fourier_mem hψ hf')) (μ₁ * c)⁻¹ (μ₁⁻¹ * μ₂) (isUnit1_inv (isUnit1_mul h₁ hc))
    (isUnit1_mul (isUnit1_inv h₁) h₂) (1 - s) hs'
  beta_reduce at hI hE
  have hw : ∀ a : Fˣ, W2 ψ μ₁ μ₂ (pt f g) (dg2 a 1 * w0) = W2 ψ μ₁ μ₂ (pt g (fun y => f (-y))) (dg2 a 1) := by
    intro a
    rw [(hTr F ψ hψ μ₁ μ₂ h₁ h₂ _ (pt_mem hf hg) w0).2, det_weyl_GL2, rightTranslate_pureTensor_weyl, map_one, Units.val_one, mp_one,
      one_mul, one_mul]
  have hfun : (fun a : Fˣ => W2 ψ μ₁ μ₂ (pt f g) (dg2 a 1 * w0) * (((μ₁ a * μ₂ a * c a)⁻¹ : ℂˣ) : ℂ) *
        mp a (1 / 2 - s)) =
      fun a => ((((μ₁ * c)⁻¹) a : ℂˣ) : ℂ) * mp a (1 - s) *
        ∫ h : Fˣ, (((μ₁⁻¹ * μ₂) h : ℂˣ) : ℂ) * g ((h : F) * a) *
          localFourier (selfDualMeasure ψ) ψ (fun y => f (-y)) (-((h⁻¹ : Fˣ) : F)) ∂multHaar F := by
    funext a
    have key : mp a (1 / 2) * mp a (1 / 2 - s) = mp a (1 - s) := by rw [mp_add]; congr 1; ring
    rw [hw a, hWd F ψ hψ μ₁ μ₂ h₁ h₂ g hg _ hf' a, ← key]
    have h2 : ((μ₂ a : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
    have h1 : ((μ₁ a : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
    have h3 : ((c a : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
    have hsc : ((μ₂ a : ℂˣ) : ℂ) * (((μ₁ a : ℂˣ) : ℂ) * ((μ₂ a : ℂˣ) : ℂ) * ((c a : ℂˣ) : ℂ))⁻¹ =
        (((μ₁ a : ℂˣ) : ℂ) * ((c a : ℂˣ) : ℂ))⁻¹ := by field_simp
    simp only [MonoidHom.mul_apply, MonoidHom.inv_apply, Units.val_mul, Units.val_inv_eq_inv_val]
    rw [← hsc]
    ring
  rw [hfun]
  exact ⟨hI, by rw [hE, character_inverse_identity_second]⟩

theorem pure (hDZ : SDZ) (hWd : SWd) (hTr : STrans) (hTate : STate) {ψ : AddChar F Circle} (hψ : IsStd ψ)
    {μ₁ μ₂ : Fˣ →* ℂˣ} (h₁ : IsUnit1 μ₁) (h₂ : IsUnit1 μ₂) {f g : F → ℂ} (hf : f ∈ schwartzBruhat F)
    (hg : g ∈ schwartzBruhat F) {c : Fˣ →* ℂˣ} (hc : IsUnit1 c) {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1) :
    Integrable (fun a : Fˣ => W2 ψ μ₁ μ₂ (pt f g) (dg2 a 1 * w0) * (((μ₁ a * μ₂ a * c a)⁻¹ : ℂˣ) : ℂ) *
        mp a (1 / 2 - s)) (multHaar F) ∧
      Integrable (fun a : Fˣ => W2 ψ μ₁ μ₂ (pt f g) (dg2 a 1) * ((c a : ℂˣ) : ℂ) * mp a (s - 1 / 2))
        (multHaar F) ∧
      ∫ a, W2 ψ μ₁ μ₂ (pt f g) (dg2 a 1 * w0) * (((μ₁ a * μ₂ a * c a)⁻¹ : ℂˣ) : ℂ) *
          mp a (1 / 2 - s) ∂multHaar F =
        gam ψ (μ₁ * c) s * gam ψ (μ₂ * c) s *
          ∫ a, W2 ψ μ₁ μ₂ (pt f g) (dg2 a 1) * ((c a : ℂˣ) : ℂ) * mp a (s - 1 / 2) ∂multHaar F := by
  obtain ⟨hIL, hEL⟩ := lhs_pure hDZ hWd hTr hψ h₁ h₂ hf hg hc hs1
  obtain ⟨hIR, hER⟩ := rhs_pure hDZ hWd hψ h₁ h₂ hf hg hc hs0
  refine ⟨hIL, hIR, ?_⟩
  have hf' := comp_neg_mem hf
  have T2 := (hTate F ψ hψ (μ₂ * c) (isUnit1_mul h₂ hc) _ hf' s hs0 hs1).1
  have T1 := (hTate F ψ hψ (μ₁ * c) (isUnit1_mul h₁ hc) g hg s hs0 hs1).2
  rw [hEL, hER, localZeta_comp_neg (localFourier (selfDualMeasure ψ) ψ (fun y => f (-y))) (μ₂ * c)⁻¹ (1 - s),
    T2, localZeta_comp_neg f (μ₂ * c) s, T1,
    localZeta_comp_neg (localFourier (selfDualMeasure ψ) ψ g) (μ₁ * c) s]
  have hu : ((((μ₂ * c)⁻¹ (-1 : Fˣ)) : ℂˣ) : ℂ) * (((μ₂ * c) (-1 : Fˣ) : ℂˣ) : ℂ) = 1 := by
    rw [MonoidHom.inv_apply, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  linear_combination (((μ₁ * c) (-1 : Fˣ) : ℂˣ) : ℂ) * gam ψ (μ₁ * c) s *
    localZeta (localFourier (selfDualMeasure ψ) ψ g) (μ₁ * c) s * gam ψ (μ₂ * c) s * localZeta f (μ₂ * c) s * hu

theorem sum_pure_tensors_whittaker (hLin : SLin) {ψ : AddChar F Circle} (hψ : IsStd ψ) {μ₁ μ₂ : Fˣ →* ℂˣ} (h₁ : IsUnit1 μ₁)
    (h₂ : IsUnit1 μ₂) {n : ℕ} {f g : Fin n → F → ℂ} (hfg : ∀ i, f i ∈ schwartzBruhat F ∧ g i ∈ schwartzBruhat F)
    (t : Finset (Fin n)) :
    (∑ i ∈ t, pt (f i) (g i)) ∈ GodementSectionLocal.schwartzBruhat2 F ∧
      W2 ψ μ₁ μ₂ (∑ i ∈ t, pt (f i) (g i)) = ∑ i ∈ t, W2 ψ μ₁ μ₂ (pt (f i) (g i)) := by
  refine Finset.induction_on t ?_ ?_
  · refine ⟨by simpa using zero_mem _, ?_⟩
    have := (hLin F ψ hψ μ₁ μ₂ h₁ h₂ 0 (zero_mem _) 0 (zero_mem _)).2 0
    simpa using this
  · intro i t hi ih
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    refine ⟨add_mem (pt_mem (hfg i).1 (hfg i).2) ih.1, ?_⟩
    rw [(hLin F ψ hψ μ₁ μ₂ h₁ h₂ _ (pt_mem (hfg i).1 (hfg i).2) _ ih.1).1, ih.2]

end Ad3.SchwartzSpaceL2.PFe

open Ad3.SchwartzSpaceL2.PFe in
theorem Ad3.SchwartzSpaceL2.pfe : Ad3.SchwartzSpaceL2.SFe := by
  intro hDZ hWd hPure hLin hTr hTate F _ _ _ _ _ _ ψ hψ μ₁ μ₂ h₁ h₂ φ hφ c hc s hs0 hs1
  obtain ⟨n, f, g, hfg, rfl⟩ := hPure F φ hφ
  have hW := (sum_pure_tensors_whittaker hLin hψ h₁ h₂ hfg Finset.univ).2
  have hP := fun i => pure hDZ hWd hTr hTate hψ h₁ h₂ (hfg i).1 (hfg i).2 hc hs0 hs1
  have hL : (fun a : Fˣ => W2 ψ μ₁ μ₂ (∑ i, pt (f i) (g i)) (dg2 a 1 * w0) *
      (((μ₁ a * μ₂ a * c a)⁻¹ : ℂˣ) : ℂ) * mp a (1 / 2 - s)) =
      fun a => ∑ i, W2 ψ μ₁ μ₂ (pt (f i) (g i)) (dg2 a 1 * w0) *
        (((μ₁ a * μ₂ a * c a)⁻¹ : ℂˣ) : ℂ) * mp a (1 / 2 - s) := by
    funext a
    rw [hW, Finset.sum_apply, Finset.sum_mul, Finset.sum_mul]
  have hR : (fun a : Fˣ => W2 ψ μ₁ μ₂ (∑ i, pt (f i) (g i)) (dg2 a 1) * ((c a : ℂˣ) : ℂ) *
      mp a (s - 1 / 2)) =
      fun a => ∑ i, W2 ψ μ₁ μ₂ (pt (f i) (g i)) (dg2 a 1) * ((c a : ℂˣ) : ℂ) * mp a (s - 1 / 2) := by
    funext a
    rw [hW, Finset.sum_apply, Finset.sum_mul, Finset.sum_mul]
  rw [hL, hR]
  refine ⟨integrable_finset_sum _ fun i _ => (hP i).1, integrable_finset_sum _ fun i _ => (hP i).2.1, ?_⟩
  rw [integral_finset_sum _ fun i _ => (hP i).1, integral_finset_sum _ fun i _ => (hP i).2.1,
    Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => (hP i).2.2
