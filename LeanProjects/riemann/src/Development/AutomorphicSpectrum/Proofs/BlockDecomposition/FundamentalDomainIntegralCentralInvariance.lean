import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.VerticalStrips.UnramifiedEulerProductIntegral

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.Automorphic
open scoped NumberField.AdeleRing ENNReal

namespace GlobalTheory.CompanionTheory.RS

open Ad3 Ad3.R

abbrev Gam : Subgroup G2 := (AdelicGLn.diagonal ℚ 2).range

instance : Countable Gam := by
  haveI : Countable (Matrix (Fin 2) (Fin 2) ℚ) := inferInstanceAs (Countable (Fin 2 → Fin 2 → ℚ))
  haveI : Countable (GL (Fin 2) ℚ) :=
    Function.Injective.countable (f := fun g : GL (Fin 2) ℚ => (g : Matrix (Fin 2) (Fin 2) ℚ)) Units.val_injective
  exact (Set.countable_range (AdelicGLn.diagonal ℚ 2)).to_subtype

theorem hecke_diagonal_val (z : Jd) : ((dg2 z z : G2) : Matrix (Fin 2) (Fin 2) 𝔸[ℚ]) = Matrix.scalar (Fin 2) (z : 𝔸[ℚ]) := by
  delta Ad3.dg2
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.scalar_apply]

theorem central_diagonal_commute (z : Jd) (g : G2) : dg2 z z * g = g * dg2 z z := by
  ext1
  rw [Units.val_mul, Units.val_mul, hecke_diagonal_val]
  exact (Matrix.scalar_commute _ (fun _ => Commute.all _ _) _).eq

theorem scalar_diagonal_mul (a b : Jd) : dg2 (a * b) (a * b) = (dg2 a a * dg2 b b : G2) := by
  ext1
  rw [Units.val_mul, hecke_diagonal_val, hecke_diagonal_val, hecke_diagonal_val, Units.val_mul, map_mul]

theorem diag_one_one_eq_identity : dg2 (1 : Jd) 1 = (1 : G2) := by
  ext1
  rw [hecke_diagonal_val, Units.val_one, Units.val_one, map_one]

theorem det_diagonal_two (a : Jd) : GeneralLinearGroup.det (dg2 a a : G2) = a * a := by
  ext
  rw [Matrix.GeneralLinearGroup.val_det_apply, hecke_diagonal_val, Units.val_mul]
  simp [Matrix.det_fin_two, Matrix.scalar_apply, sq]

theorem det_rationalEmbedding (γ : GL (Fin 2) ℚ) :
    GeneralLinearGroup.det (dia2 γ) = IdeleGroup.diagonal ℚ (GeneralLinearGroup.det γ) := by
  ext
  delta Ad3.R.dia2 GroundTheory.Automorphic.AdelicGLn.diagonal GroundTheory.Global.IdeleGroup.diagonal
  simp only [Matrix.GeneralLinearGroup.val_det_apply, Units.coe_map, MonoidHom.coe_coe]
  exact (RingHom.map_det _ _).symm

theorem md_mul (a b : Jd) : md (a * b) = md a * md b := by
  show ((GroundTheory.Global.IdeleGroup.ideleModule ℚ (a * b) : {r : ℝ // 0 < r}) : ℝ) =
    ((GroundTheory.Global.IdeleGroup.ideleModule ℚ a : {r : ℝ // 0 < r}) : ℝ) *
      ((GroundTheory.Global.IdeleGroup.ideleModule ℚ b : {r : ℝ // 0 < r}) : ℝ)
  rw [map_mul]
  rfl

theorem Dt_mul (g h : G2) : Dt (g * h) = Dt g * Dt h := by
  show md (GeneralLinearGroup.det (g * h)) = md (GeneralLinearGroup.det g) * md (GeneralLinearGroup.det h)
  rw [map_mul, md_mul]

theorem detModulus_rational (γ : GL (Fin 2) ℚ) : Dt (dia2 γ) = 1 := by
  show md (GeneralLinearGroup.det (dia2 γ)) = 1
  rw [det_rationalEmbedding]
  show ((GroundTheory.Global.IdeleGroup.ideleModule ℚ
    (GroundTheory.Global.IdeleGroup.diagonal ℚ (GeneralLinearGroup.det γ)) : {r : ℝ // 0 < r}) : ℝ) = 1
  rw [GroundTheory.Global.IdeleGroup.ideleModule_diagonal]
  rfl

theorem detModulus_diag (z : Jd) : Dt (dg2 z z) = md z ^ 2 := by
  show md (GeneralLinearGroup.det (dg2 z z : G2)) = md z ^ 2
  rw [det_diagonal_two, md_mul, sq]

theorem continuous_Dt : Continuous Dt := by
  show Continuous fun g : G2 =>
    ((GroundTheory.Global.IdeleGroup.ideleModule ℚ (GeneralLinearGroup.det g) : {r : ℝ // 0 < r}) : ℝ)
  exact continuous_subtype_val.comp
    (GroundTheory.Global.IdeleGroup.continuous_ideleModule.comp Matrix.GeneralLinearGroup.continuous_det)

theorem key {μ : Measure G2} {𝓕 : Set G2} [μ.IsMulLeftInvariant] (hfd : IsFundamentalDomain Gam 𝓕 μ)
    (T : G2 ≃ᵐ G2) (hT : MeasurePreserving T μ μ) (e : Gam ≃ Gam)
    (hs : ∀ (γ : Gam) x, T ((e γ : G2) * x) = (γ : G2) * T x) :
    (∀ F : G2 → ℝ≥0∞, LInv F → ∫⁻ g in 𝓕, F (T g) ∂μ = ∫⁻ g in 𝓕, F g ∂μ) ∧
    ∀ F : G2 → ℂ, LInv F → ∫ g in 𝓕, F (T g) ∂μ = ∫ g in 𝓕, F g ∂μ := by
  have hemb : MeasurableEmbedding T := T.measurableEmbedding
  have h𝓕' : IsFundamentalDomain Gam (T '' 𝓕) μ := hfd.image_of_equiv T.toEquiv (hT.symm T).quasiMeasurePreserving e (fun γ x => hs γ x)
  have hinv : ∀ {X : Type} (F : G2 → X), LInv F → ∀ (γ : Gam) (x : G2), F (γ • x) = F x := by
    intro X F hF γ x
    obtain ⟨γ0, hγ0⟩ := γ.2
    rw [Subgroup.smul_def, smul_eq_mul, ← hγ0]
    exact hF γ0 x
  refine ⟨fun F hF => ?_, fun F hF => ?_⟩
  · rw [hT.setLIntegral_comp_emb hemb F 𝓕]
    exact h𝓕'.setLIntegral_eq hfd F (hinv F hF)
  · rw [← hT.setIntegral_image_emb hemb F 𝓕]
    exact h𝓕'.setIntegral_eq hfd (hinv F hF)

theorem det_inverse_twist_mul (g h : G2) : inv2 (g * h) = inv2 g * inv2 h := by
  show dg2 (GeneralLinearGroup.det (g * h))⁻¹ (GeneralLinearGroup.det (g * h))⁻¹ * (g * h) =
    dg2 (GeneralLinearGroup.det g)⁻¹ (GeneralLinearGroup.det g)⁻¹ * g *
      (dg2 (GeneralLinearGroup.det h)⁻¹ (GeneralLinearGroup.det h)⁻¹ * h)
  rw [map_mul, mul_inv, scalar_diagonal_mul, mul_assoc, mul_assoc, ← mul_assoc _ g h,
    central_diagonal_commute (GeneralLinearGroup.det h)⁻¹ g, mul_assoc]

theorem det_inverse_twist_involutive (g : G2) : inv2 (inv2 g) = g := by
  have hd : GeneralLinearGroup.det (dg2 (GeneralLinearGroup.det g)⁻¹ (GeneralLinearGroup.det g)⁻¹ * g : G2) =
      (GeneralLinearGroup.det g)⁻¹ := by
    rw [map_mul, det_diagonal_two, mul_assoc, inv_mul_cancel, mul_one]
  show dg2 (GeneralLinearGroup.det (dg2 (GeneralLinearGroup.det g)⁻¹ (GeneralLinearGroup.det g)⁻¹ * g : G2))⁻¹
      (GeneralLinearGroup.det (dg2 (GeneralLinearGroup.det g)⁻¹ (GeneralLinearGroup.det g)⁻¹ * g : G2))⁻¹ *
      (dg2 (GeneralLinearGroup.det g)⁻¹ (GeneralLinearGroup.det g)⁻¹ * g) = g
  rw [hd, inv_inv, ← mul_assoc, ← scalar_diagonal_mul, mul_inv_cancel, diag_one_one_eq_identity, one_mul]

theorem scalar_diagonal_inv (z : Jd) : (dg2 z z : G2)⁻¹ = dg2 z⁻¹ z⁻¹ := by
  exact inv_eq_of_mul_eq_one_right (by rw [← scalar_diagonal_mul, mul_inv_cancel, diag_one_one_eq_identity])

theorem continuous_scalar : Continuous fun a : 𝔸[ℚ] => Matrix.scalar (Fin 2) a := by
  simp only [Matrix.scalar_apply]
  exact Continuous.matrix_diagonal (continuous_pi fun _ => continuous_id)

theorem continuous_diagGL2 : Continuous fun z : Jd => (dg2 z z : G2) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · have h1 : (Units.val ∘ fun z : Jd => (dg2 z z : G2)) = fun z : Jd => Matrix.scalar (Fin 2) (z : 𝔸[ℚ]) :=
      funext hecke_diagonal_val
    rw [h1]
    exact continuous_scalar.comp Units.continuous_val
  · have h2 : (fun z : Jd => (((dg2 z z : G2)⁻¹ : G2) : Matrix (Fin 2) (Fin 2) 𝔸[ℚ])) =
        fun z : Jd => Matrix.scalar (Fin 2) ((z⁻¹ : Jd) : 𝔸[ℚ]) :=
      funext fun z => by rw [scalar_diagonal_inv, hecke_diagonal_val]
    rw [h2]
    exact continuous_scalar.comp Units.continuous_coe_inv

theorem continuous_det_inverse_twist : Continuous inv2 := by
  show Continuous fun g : G2 => dg2 (GeneralLinearGroup.det g)⁻¹ (GeneralLinearGroup.det g)⁻¹ * g
  exact (continuous_diagGL2.comp Matrix.GeneralLinearGroup.continuous_det.inv).mul continuous_id

def inv2Equiv : G2 ≃* G2 where
  toFun := inv2
  invFun := inv2
  left_inv := det_inverse_twist_involutive
  right_inv := det_inverse_twist_involutive
  map_mul' := det_inverse_twist_mul

theorem scalar_diagonal_of_rational (d : ℚˣ) :
    dg2 (IdeleGroup.diagonal ℚ d) (IdeleGroup.diagonal ℚ d) = dia2 (dg2 d d) := by
  ext1
  rw [hecke_diagonal_val]
  delta Ad3.R.dia2 GroundTheory.Automorphic.AdelicGLn.diagonal GroundTheory.Global.IdeleGroup.diagonal Ad3.dg2
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.scalar_apply, Matrix.algebraMap_matrix_apply]

theorem det_inverse_twist_mem_arithmetic {g : G2} (hg : g ∈ Gam) : inv2 g ∈ Gam := by
  obtain ⟨γ, rfl⟩ := hg
  have h1 : inv2 (AdelicGLn.diagonal ℚ 2 γ) =
      dia2 (dg2 (GeneralLinearGroup.det γ)⁻¹ (GeneralLinearGroup.det γ)⁻¹ * γ) := by
    change dg2 (GeneralLinearGroup.det (dia2 γ))⁻¹ (GeneralLinearGroup.det (dia2 γ))⁻¹ * dia2 γ =
      AdelicGLn.diagonal ℚ 2 (dg2 (GeneralLinearGroup.det γ)⁻¹ (GeneralLinearGroup.det γ)⁻¹ * γ)
    rw [det_rationalEmbedding, ← map_inv, scalar_diagonal_of_rational, map_mul]
  exact ⟨_, h1.symm⟩

theorem measurePreserving_det_inverse_twist {μ : Measure G2} [μ.IsHaarMeasure] : MeasurePreserving inv2 μ μ := by
  have hc : Continuous inv2 := continuous_det_inverse_twist
  refine ⟨hc.measurable, ?_⟩
  haveI : (μ.map inv2).IsHaarMeasure := MulEquiv.isHaarMeasure_map μ inv2Equiv hc hc
  set c := Measure.haarScalarFactor (μ.map inv2) μ with hc_def
  have h1 : μ.map inv2 = c • μ := Measure.isMulLeftInvariant_eq_smul _ _
  have h2 : (μ.map inv2).map inv2 = μ := by
    rw [Measure.map_map hc.measurable hc.measurable]
    have hid : inv2 ∘ inv2 = id := funext det_inverse_twist_involutive
    rw [hid, Measure.map_id]
  rw [h1, Measure.map_smul, h1, smul_smul] at h2
  obtain ⟨K, hKc, hKn⟩ := exists_compact_mem_nhds (1 : G2)
  have hpos : μ K ≠ 0 := (Measure.measure_pos_of_mem_nhds μ hKn).ne'
  have hfin : μ K ≠ ⊤ := hKc.measure_lt_top.ne
  have h3 := congrArg (fun ν : Measure G2 => ν K) h2
  simp only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at h3
  have h4 : ((c * c : NNReal) : ENNReal) * μ K = 1 * μ K := by
    rw [one_mul, ENNReal.coe_mul]
    exact h3
  have h5 : (c * c : NNReal) = 1 := by
    exact_mod_cast (ENNReal.mul_left_inj hpos hfin).1 h4
  have h6 : c = 1 := by
    have h7 : ((c : ℝ) * c) = 1 := by exact_mod_cast h5
    have h8 : (0 : ℝ) ≤ c := c.2
    have h9 : (c : ℝ) = 1 := by nlinarith
    exact NNReal.eq h9
  rw [h1, h6, one_smul]

theorem exists_unit_one_add_generator (r : ℝ) (hr : 0 < r) :
    ∃ z : Jd, md z ^ 2 = r ∧ ∀ c : HeckeCharacter ℚ, IsOfFinOrder c → c.toIdele z = 1 := by
  classical
  have hsub : ∀ v w : NumberField.InfinitePlace ℚ, v = w := fun v w => by
    obtain ⟨φ, hφ⟩ := v.2
    obtain ⟨ψ, hψ⟩ := w.2
    exact Subtype.ext (by rw [← hφ, ← hψ, Subsingleton.elim φ ψ])
  haveI : Subsingleton (NumberField.InfinitePlace ℚ) := ⟨hsub⟩
  have hv : ∀ v : NumberField.InfinitePlace ℚ, v.IsReal := fun v => by
    obtain ⟨φ, hφ⟩ := v.2
    exact ⟨φ, Subsingleton.elim _ _, Subtype.ext hφ⟩
  let p0 : NumberField.InfinitePlace ℚ := NumberField.InfinitePlace.mk (Rat.castHom ℂ)
  let ι : ℝ →* NumberField.InfiniteAdeleRing ℚ :=
    { toFun := fun t v => (NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal (hv v)).symm t
      map_one' := funext fun v => map_one _
      map_mul' := fun s t => funext fun v => map_mul _ s t }
  have hnorm : ∀ (t : ℝ) (v : NumberField.InfinitePlace ℚ), ‖ι t v‖ = |t| := by
    intro t v
    have h := (AddMonoidHomClass.isometry_iff_norm
      (NumberField.InfinitePlace.Completion.extensionEmbeddingOfIsReal (hv v))).1
      (NumberField.InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal (hv v)) (ι t v)
    rw [← h]
    show ‖(NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal (hv v))
      ((NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal (hv v)).symm t)‖ = |t|
    rw [RingEquiv.apply_symm_apply, Real.norm_eq_abs]
  let Z : ℝˣ →* Jd := GroundTheory.Global.IdeleGroup.ofInfinite.comp (Units.map ι)
  have hmd : ∀ t : ℝˣ, md (Z t) = |(t : ℝ)| := by
    intro t
    have hinf : (Z t).infiniteModule = |(t : ℝ)| := by
      show ∏ w, ‖(↑(Z t) : NumberField.AdeleRing (𝓞 ℚ) ℚ).1 w‖ ^ w.mult = |(t : ℝ)|
      rw [Fintype.prod_subsingleton _ p0]
      show ‖ι t p0‖ ^ p0.mult = |(t : ℝ)|
      rw [hnorm, NumberField.InfinitePlace.mult, if_pos (hv _), pow_one]
    have hfin : (Z t).finiteModule = 1 := by
      show ∏ᶠ v, ‖(↑(Z t) : NumberField.AdeleRing (𝓞 ℚ) ℚ).2 v‖ = 1
      have h1 : ∀ v, ‖(↑(Z t) : NumberField.AdeleRing (𝓞 ℚ) ℚ).2 v‖ = 1 := fun v => by
        show ‖(1 : IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ) v‖ = 1
        rw [show (1 : IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ) v = 1 from rfl, norm_one]
      simp only [h1, finprod_one]
    show (Z t).infiniteModule * (Z t).finiteModule = |(t : ℝ)|
    rw [hinf, hfin, mul_one]
  have hs0 : 0 < Real.sqrt r := Real.sqrt_pos.2 hr
  refine ⟨Z (Units.mk0 (Real.sqrt r) hs0.ne'), ?_, ?_⟩
  · rw [hmd, Units.val_mk0, abs_of_pos hs0]
    exact Real.sq_sqrt hr.le
  · intro c hc
    obtain ⟨N, hN, hcN⟩ := isOfFinOrder_iff_pow_eq_one.1 hc
    have hw : (Real.sqrt r) ^ ((N : ℝ)⁻¹) ≠ 0 := (Real.rpow_pos_of_pos hs0 _).ne'
    have hroot : Units.mk0 (Real.sqrt r) hs0.ne' = (Units.mk0 ((Real.sqrt r) ^ ((N : ℝ)⁻¹)) hw) ^ N := by
      ext
      rw [Units.val_pow_eq_pow_val, Units.val_mk0, Units.val_mk0]
      exact (Real.rpow_inv_natCast_pow hs0.le hN.ne').symm
    rw [hroot, map_pow, map_pow]
    have h2 : (c ^ N).toIdele (Z (Units.mk0 ((Real.sqrt r) ^ ((N : ℝ)⁻¹)) hw)) =
        (c.toIdele (Z (Units.mk0 ((Real.sqrt r) ^ ((N : ℝ)⁻¹)) hw))) ^ N :=
      ContinuousMonoidHom.pow_apply c N
        (GroundTheory.Global.IdeleClassGroup.mk ℚ (Z (Units.mk0 ((Real.sqrt r) ^ ((N : ℝ)⁻¹)) hw)))
    rw [← h2, hcN]
    rfl

theorem fundamental_domain_integral_invariance {μ : Measure G2} {𝓕 : Set G2} {mK : Measure KA} {𝓓 : Set Jd} (h : Set0 μ 𝓕 mK 𝓓)
    (T : G2 → G2) (hT : T = inv2 ∨ (∃ h, T = fun g => g * h) ∨ ∃ z : Jd, T = fun g => dg2 z z * g) :
    (∀ F : G2 → ℝ≥0∞, LInv F → ∫⁻ g in 𝓕, F (T g) ∂μ = ∫⁻ g in 𝓕, F g ∂μ) ∧
    ∀ F : G2 → ℂ, LInv F → ∫ g in 𝓕, F (T g) ∂μ = ∫ g in 𝓕, F g ∂μ := by
  obtain ⟨haar, right, fd, -, -, -, -, -, -, -⟩ := h
  rcases hT with rfl | ⟨h', rfl⟩ | ⟨z, rfl⟩
  · let Tm : G2 ≃ᵐ G2 :=
      { toEquiv := inv2Equiv.toEquiv
        measurable_toFun := continuous_det_inverse_twist.measurable
        measurable_invFun := continuous_det_inverse_twist.measurable }
    let e : Gam ≃ Gam :=
      { toFun := fun γ => ⟨inv2 γ, det_inverse_twist_mem_arithmetic γ.2⟩
        invFun := fun γ => ⟨inv2 γ, det_inverse_twist_mem_arithmetic γ.2⟩
        left_inv := fun γ => Subtype.ext (det_inverse_twist_involutive γ)
        right_inv := fun γ => Subtype.ext (det_inverse_twist_involutive γ) }
    have hs : ∀ (γ : Gam) x, Tm ((e γ : G2) * x) = (γ : G2) * Tm x := fun γ x => by
      show inv2 (inv2 (γ : G2) * x) = (γ : G2) * inv2 x
      rw [det_inverse_twist_mul, det_inverse_twist_involutive]
    exact key fd Tm measurePreserving_det_inverse_twist e hs
  · exact key fd (MeasurableEquiv.mulRight h') (measurePreserving_mul_right μ h') (Equiv.refl _)
      (fun γ x => by simp [mul_assoc])
  · exact key fd (MeasurableEquiv.mulLeft (dg2 z z : G2)) (measurePreserving_mul_left μ _) (Equiv.refl _)
      (fun γ x => by
        simp only [MeasurableEquiv.coe_mulLeft, Equiv.refl_apply]
        rw [← mul_assoc, ← mul_assoc, central_diagonal_commute])

theorem level {μ : Measure G2} {𝓕 : Set G2} {mK : Measure KA} {𝓓 : Set Jd} (h : Set0 μ 𝓕 mK 𝓓) :
    μ {g | Dt g = 1} = 0 := by
  classical
  haveI := h.haar
  have hGinv : ∀ (γ : Gam) (x : G2), Dt ((γ : G2) * x) = Dt x := fun γ x => by
    obtain ⟨γ0, hγ0⟩ := γ.2
    rw [← hγ0, Dt_mul]
    have h1 : Dt ((AdelicGLn.diagonal ℚ 2) γ0) = 1 := detModulus_rational γ0
    rw [h1, one_mul]
  have hmeasS : ∀ r : ℝ, MeasurableSet {g : G2 | Dt g = r} := fun r =>
    (isClosed_eq continuous_Dt continuous_const).measurableSet
  have hLInv : ∀ r : ℝ, LInv ({g : G2 | Dt g = r}.indicator (1 : G2 → ℝ≥0∞)) := by
    intro r γ g
    have h1 : Dt (dia2 γ * g) = Dt g := by rw [Dt_mul, detModulus_rational, one_mul]
    simp only [Set.indicator, Set.mem_setOf_eq, h1, Pi.one_apply]
  have heq : ∀ r : ℝ, 0 < r → μ ({g : G2 | Dt g = r} ∩ 𝓕) = μ ({g : G2 | Dt g = 1} ∩ 𝓕) := by
    intro r hr
    obtain ⟨z, hz, -⟩ := exists_unit_one_add_generator r hr
    have key := (fundamental_domain_integral_invariance h (fun g => dg2 z z * g) (Or.inr (Or.inr ⟨z, rfl⟩))).1
      ({g : G2 | Dt g = r}.indicator 1) (hLInv r)
    have hpre : (fun g => {g : G2 | Dt g = r}.indicator (1 : G2 → ℝ≥0∞) (dg2 z z * g)) =
        {g : G2 | Dt g = 1}.indicator 1 := by
      funext g
      have hD : Dt (dg2 z z * g) = r * Dt g := by rw [Dt_mul, detModulus_diag, hz]
      by_cases hg : Dt g = 1
      · have h2 : Dt (dg2 z z * g) = r := by rw [hD, hg, mul_one]
        simp only [Set.indicator, Set.mem_setOf_eq, h2, hg, if_true, Pi.one_apply]
      · have h2 : Dt (dg2 z z * g) ≠ r := by
          rw [hD]
          intro h3
          apply hg
          have h4 : r * Dt g = r * 1 := by rw [h3, mul_one]
          exact mul_left_cancel₀ hr.ne' h4
        simp only [Set.indicator, Set.mem_setOf_eq, h2, hg, if_false]
    beta_reduce at key
    rw [hpre, lintegral_indicator_one (hmeasS 1), lintegral_indicator_one (hmeasS r),
      Measure.restrict_apply (hmeasS 1), Measure.restrict_apply (hmeasS r)] at key
    exact key.symm
  have hzero : μ ({g : G2 | Dt g = 1} ∩ 𝓕) = 0 := by
    by_contra hne
    obtain ⟨n, hn⟩ := ENNReal.exists_nat_mul_gt hne h.vol.ne
    let rr : ℕ → ℝ := fun k => 1 + 1 / ((k : ℝ) + 2)
    have hrr : ∀ k, 1 ≤ rr k ∧ rr k < 2 := fun k => by
      have hk : (0 : ℝ) < (k : ℝ) + 2 := by positivity
      constructor
      · have : 0 ≤ 1 / ((k : ℝ) + 2) := by positivity
        show 1 ≤ 1 + 1 / ((k : ℝ) + 2)
        linarith
      · have : 1 / ((k : ℝ) + 2) < 1 := by
          rw [div_lt_one hk]
          have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
          linarith
        show 1 + 1 / ((k : ℝ) + 2) < 2
        linarith
    have hinj : Function.Injective rr := fun i j hij => by
      have h1 : 1 / ((i : ℝ) + 2) = 1 / ((j : ℝ) + 2) := by
        have := hij
        simp only [rr] at this
        linarith
      have hi : (0 : ℝ) < (i : ℝ) + 2 := by positivity
      have hj : (0 : ℝ) < (j : ℝ) + 2 := by positivity
      rw [div_eq_div_iff hi.ne' hj.ne', one_mul, one_mul] at h1
      exact_mod_cast (by linarith : (i : ℝ) = j)
    have hdisj : Set.PairwiseDisjoint (↑(Finset.range n) : Set ℕ)
        (fun k => {g : G2 | Dt g = rr k} ∩ 𝓕) := fun i _ j _ hij =>
      Set.disjoint_left.2 fun g hgi hgj => hij (hinj (hgi.1.symm.trans hgj.1))
    have hsum : μ (⋃ k ∈ Finset.range n, {g : G2 | Dt g = rr k} ∩ 𝓕) =
        ∑ k ∈ Finset.range n, μ ({g : G2 | Dt g = rr k} ∩ 𝓕) :=
      measure_biUnion_finset hdisj (fun k _ => (hmeasS _).inter h.meas)
    have hsub : (⋃ k ∈ Finset.range n, {g : G2 | Dt g = rr k} ∩ 𝓕) ⊆ 𝓕 ∩ band := by
      intro g hg
      rw [Set.mem_iUnion₂] at hg
      obtain ⟨k, -, hg1, hg2⟩ := hg
      refine ⟨hg2, ?_⟩
      show 1 ≤ Dt g ∧ Dt g < 2
      rw [show Dt g = rr k from hg1]
      exact hrr k
    have hle : (n : ℝ≥0∞) * μ ({g : G2 | Dt g = 1} ∩ 𝓕) ≤ μ (𝓕 ∩ band) := by
      calc (n : ℝ≥0∞) * μ ({g : G2 | Dt g = 1} ∩ 𝓕)
          = ∑ k ∈ Finset.range n, μ ({g : G2 | Dt g = rr k} ∩ 𝓕) := by
            rw [Finset.sum_congr rfl (fun k _ => heq (rr k) (by linarith [(hrr k).1])),
              Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        _ = μ (⋃ k ∈ Finset.range n, {g : G2 | Dt g = rr k} ∩ 𝓕) := hsum.symm
        _ ≤ μ (𝓕 ∩ band) := measure_mono hsub
    exact absurd hn (not_lt.2 hle)
  open scoped Pointwise in
  have hinvS : ∀ γ : Gam, γ • {g : G2 | Dt g = 1} = {g : G2 | Dt g = 1} := fun γ => by
    ext x
    rw [Set.mem_smul_set_iff_inv_smul_mem]
    simp only [Set.mem_setOf_eq, Subgroup.smul_def, smul_eq_mul]
    rw [hGinv γ⁻¹ x]
  rw [h.fd.measure_eq_tsum]
  simp only [hinvS, hzero, tsum_zero]

theorem rankinSelberg_measure_facts : Ad3.R.G1a := by
  intro μ 𝓕 mK 𝓓 h
  exact ⟨level h, exists_unit_one_add_generator, fun T hT => ⟨fun F _ hF => (fundamental_domain_integral_invariance h T hT).1 F hF,
    fun F _ hF => (fundamental_domain_integral_invariance h T hT).2 F hF⟩⟩

end GlobalTheory.CompanionTheory.RS

end
