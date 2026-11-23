import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.PlaceAll
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.LamCut

noncomputable section

namespace PI.AprimeInfW

open MeasureTheory Matrix
open scoped ENNReal NNReal

section Lin

variable {n m : ℕ} {α β : Type} [Fintype α] [Fintype β]

def jacM (w : Matrix (Fin n) (Fin m) ℂ) (B : Matrix (Fin n) (Fin m) ℂ)
    (Lv : EuclideanSpace ℝ α →ₗ[ℝ] Matrix (Fin n) (Fin n) ℂ) (Hv : EuclideanSpace ℝ β →ₗ[ℝ] Matrix (Fin m) (Fin m) ℂ) :
    (EuclideanSpace ℝ α × EuclideanSpace ℝ β) →ₗ[ℝ] (Fin n → Fin m → ℂ) where
  toFun z := (Lv z.1 * w + (1 / 2 : ℂ) • (B * Hv z.2) : Matrix (Fin n) (Fin m) ℂ)
  map_add' z z' := by
    simp only [Prod.fst_add, Prod.snd_add, map_add, Matrix.add_mul, Matrix.mul_add, smul_add]
    abel
  map_smul' r z := by
    simp only [Prod.smul_fst, Prod.smul_snd, map_smul, Matrix.smul_mul, Matrix.mul_smul, RingHom.id_apply]
    rw [smul_comm]
    exact (smul_add _ _ _).symm

def mulCR (c : Matrix (Fin n) (Fin n) ℂ) :
    EuclideanSpace ℝ (Fin n × Fin m × Bool) →ₗ[ℝ] EuclideanSpace ℝ (Fin n × Fin m × Bool) :=
  (reimE (r := n) (m := m)).toLinearMap ∘ₗ ((mulLC (c := m) c).restrictScalars ℝ) ∘ₗ
    (reimE (r := n) (m := m)).symm.toLinearMap

theorem mulCR_apply (c : Matrix (Fin n) (Fin n) ℂ) (y : EuclideanSpace ℝ (Fin n × Fin m × Bool)) :
    mulCR c y = reim (c * Matrix.of ((reimE (r := n) (m := m)).symm y)) := by
  unfold mulCR
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.coe_restrictScalars, mulLC_apply]
  rfl

end Lin

def flatL (V β : Type) [Fintype V] [Fintype β] :
    (∀ _ : V, EuclideanSpace ℝ β) →ₗ[ℝ] EuclideanSpace ℝ (V × β) where
  toFun z := WithLp.toLp 2 (fun p : V × β => z p.1 p.2)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem flatL_pres (V β : Type) [Fintype V] [Fintype β] :
    (Measure.pi fun _ : V => (volume : Measure (EuclideanSpace ℝ β))).map (flatL V β) = volume := by
  classical
  have hmeas : Measurable (fun z : V → β → ℝ => Function.uncurry z) := by
    have h := (MeasurableEquiv.curry V β ℝ).symm.measurable
    rw [MeasurableEquiv.coe_curry_symm] at h
    exact h
  have hU : MeasurePreserving (fun z : V → β → ℝ => Function.uncurry z) volume volume := by
    refine ⟨hmeas, ?_⟩
    refine (Measure.pi_eq fun s hs => ?_).symm
    rw [Measure.map_apply hmeas (MeasurableSet.univ_pi hs)]
    have hpre : (fun z : V → β → ℝ => Function.uncurry z) ⁻¹' Set.pi Set.univ s =
        Set.pi Set.univ (fun v => Set.pi Set.univ (fun b => s (v, b))) := by
      ext z
      simp [Function.uncurry]
    rw [hpre, volume_pi, Measure.pi_pi]
    simp only [volume_pi, Measure.pi_pi]
    rw [Fintype.prod_prod_type]
  have hP := volume_preserving_pi (fun _ : V => PiLp.volume_preserving_ofLp β)
  have hT := PiLp.volume_preserving_toLp (V × β)
  have h := (hT.comp hU).comp hP
  have hf : (⇑(flatL V β)) = (WithLp.toLp 2 ∘ fun z : V → β → ℝ => Function.uncurry z) ∘
      (fun z : V → EuclideanSpace ℝ β => fun v => WithLp.ofLp (z v)) := by
    funext z
    rfl
  rw [hf]
  exact h.map_eq

theorem detJm_ne {n : ℕ} (ε : Fin n → Bool) : (Formalism.REAL.Jm ε).det ≠ 0 := by
  unfold Formalism.REAL.Jm
  rw [Matrix.det_diagonal]
  exact Finset.prod_ne_zero_iff.2 (fun a _ => by split_ifs <;> norm_num)

theorem normSq_det_of_unitary {n : ℕ} (ε : Fin n → Bool) (c : Matrix (Fin n) (Fin n) ℂ)
    (hc : cᴴ * Formalism.REAL.Jm ε * c = Formalism.REAL.Jm ε) : Complex.normSq c.det = 1 := by
  have h := congrArg Matrix.det hc
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose] at h
  have hJ := detJm_ne ε
  have h2 : star c.det * c.det = 1 := by
    have e : (star c.det * c.det) * (Formalism.REAL.Jm ε).det = 1 * (Formalism.REAL.Jm ε).det := by
      rw [one_mul]
      nth_rewrite 2 [← h]
      ring
    exact mul_right_cancel₀ hJ e
  have h3 : ((Complex.normSq c.det : ℝ) : ℂ) = 1 := by
    rw [← Complex.mul_conj, mul_comm]
    exact h2
  exact_mod_cast h3

theorem placeJacAll_of (h : PlaceJac) : PlaceJacAll := by
  classical
  intro V _ n m ε S w c ι κ _ _ L H hn hw hG hc hL1 hL2 hL3 hH1 hH2 hH3
  obtain ⟨ιv, _, Lv, T, hLQ, hLn, hLs, hLT, hTb, hTn⟩ := place_split L
    (fun v M => Mᴴ * Formalism.REAL.Jm (ε v) + Formalism.REAL.Jm (ε v) * M = 0 ∧ ∀ i ∈ S v, ∀ j ∈ S v, M i j = 0)
    hL1 (fun v => ⟨by simp, fun i _ j _ => rfl⟩) hL2 hL3
  obtain ⟨κv, _, Hv, T', hHQ, hHn, hHs, hHT, hT'b, hT'n⟩ := place_split H (fun v M => Mᴴ = M)
    hH1 (fun v => by simp) hH2 hH3
  let G : V → Matrix (Fin m) (Fin m) ℂ := fun v => (w v)ᴴ * Formalism.REAL.Jm (ε v) * w v
  let cst : V → ℝ := fun v => 2 ^ (n * m) / ‖(G v).det‖ ^ (S v).card
  have hcst : ∀ v, 0 < cst v := fun v => div_pos (by positivity) (pow_pos (norm_pos_iff.2 (hG v)) _)
  let Φ : ∀ v, (EuclideanSpace ℝ (ιv v) × EuclideanSpace ℝ (κv v)) →ₗ[ℝ]
      EuclideanSpace ℝ (Fin n × Fin m × Bool) :=
    fun v => mulCR (c v) ∘ₗ (reimE (r := n) (m := m)).toLinearMap ∘ₗ jacM (w v) (w v * (G v)⁻¹) (Lv v) (Hv v)
  have hΦ : ∀ v z, Φ v z = reim (c v * (Lv v z.1 * w v + (1 / 2 : ℂ) • (w v * (G v)⁻¹ * Hv v z.2))) := by
    intro v z
    simp only [Φ, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe, mulCR_apply]
    congr 2
  have hPJ : ∀ v, (volume : Measure (EuclideanSpace ℝ (ιv v) × EuclideanSpace ℝ (κv v))).map
      (fun z => reim (Lv v z.1 * w v + (1 / 2 : ℂ) • (w v * (G v)⁻¹ * Hv v z.2))) =
      ENNReal.ofReal (cst v) • volume :=
    fun v => h n m (ε v) (S v) (w v) (Lv v) (Hv v) (hn v) (hw v) (hG v) (hLQ v) (hLn v)
      (fun M h1 h2 => hLs v M ⟨h1, h2⟩) (hHQ v) (hHn v) (hHs v)
  have hd : ∀ v, (c v).det ≠ 0 := fun v h0 => by
    have := normSq_det_of_unitary (ε v) (c v) (hc v)
    rw [h0] at this
    simp at this
  have hΦm : ∀ v, (volume : Measure (EuclideanSpace ℝ (ιv v) × EuclideanSpace ℝ (κv v))).map (Φ v) =
      ((cst v).toNNReal : ℝ≥0∞) • volume := by
    intro v
    have e : (Φ v : _ → _) = (mulCR (m := m) (c v)) ∘
        (fun z => reim (Lv v z.1 * w v + (1 / 2 : ℂ) • (w v * (G v)⁻¹ * Hv v z.2))) := rfl
    have hm1 : Measurable (fun z : EuclideanSpace ℝ (ιv v) × EuclideanSpace ℝ (κv v) =>
        reim (Lv v z.1 * w v + (1 / 2 : ℂ) • (w v * (G v)⁻¹ * Hv v z.2))) :=
      ((reimE (r := n) (m := m)).toLinearMap ∘ₗ
        jacM (w v) (w v * (G v)⁻¹) (Lv v) (Hv v)).continuous_of_finiteDimensional.measurable
    rw [e, ← Measure.map_map (mulCR (m := m) (c v)).continuous_of_finiteDimensional.measurable hm1, hPJ v,
      Measure.map_smul]
    have hC : (volume : Measure (EuclideanSpace ℝ (Fin n × Fin m × Bool))).map (mulCR (m := m) (c v)) = volume := by
      have e2 : (mulCR (m := m) (c v) : _ → _) =
          fun y => reim (c v * Matrix.of ((reimE (r := n) (m := m)).symm y)) := funext (mulCR_apply (c v))
      rw [e2, map_mulL (c v) (hd v), normSq_det_of_unitary (ε v) (c v) (hc v)]
      simp
    rw [hC]
    rfl
  let F : (EuclideanSpace ℝ ι × EuclideanSpace ℝ κ) →ₗ[ℝ] EuclideanSpace ℝ (V × Fin n × Fin m × Bool) :=
    flatL V (Fin n × Fin m × Bool) ∘ₗ
      (LinearMap.pi fun v => Φ v ∘ₗ LinearMap.prodMap (LinearMap.proj v ∘ₗ T) (LinearMap.proj v ∘ₗ T'))
  have hF : ∀ z, F z = reimV (fun v => c v * (L z.1 v * w v +
      (1 / 2 : ℂ) • (w v * ((w v)ᴴ * Formalism.REAL.Jm (ε v) * w v)⁻¹ * H z.2 v))) := by
    intro z
    have e1 : F z = flatL V (Fin n × Fin m × Bool) (fun v => Φ v (T z.1 v, T' z.2 v)) := rfl
    rw [e1]
    simp only [hΦ, hLT, hHT]
    rfl
  have hmT := PI.AprimeInfG.measurePreserving_of_normSq T hTb hTn
  have hmT' := PI.AprimeInfG.measurePreserving_of_normSq T' hT'b hT'n
  have h12 := hmT.prod hmT'
  have h3 := MeasurePreserving.symm (PI.AprimeInfG.piProdEquiv (fun v => EuclideanSpace ℝ (ιv v))
    (fun v => EuclideanSpace ℝ (κv v))) (PI.AprimeInfG.measurePreserving_piProdEquiv
    (fun v => EuclideanSpace ℝ (ιv v)) (fun v => EuclideanSpace ℝ (κv v)) (fun v => volume) (fun v => volume))
  have h123 := h3.comp h12
  have hPm : Measurable (fun x : ∀ v, EuclideanSpace ℝ (ιv v) × EuclideanSpace ℝ (κv v) => fun v => Φ v (x v)) :=
    measurable_pi_lambda _ fun v => (Φ v).continuous_of_finiteDimensional.measurable.comp (measurable_pi_apply v)
  have h4 := pi_map_smul (fun v => (volume : Measure (EuclideanSpace ℝ (ιv v))).prod volume)
    (fun v => (volume : Measure (EuclideanSpace ℝ (Fin n × Fin m × Bool)))) (fun v => Φ v)
    (fun v => (Φ v).continuous_of_finiteDimensional.measurable) (fun v => (cst v).toNNReal)
    (fun v => by rw [ENNReal.smul_def]; exact hΦm v)
  have hfun : (F : _ → _) = flatL V (Fin n × Fin m × Bool) ∘ ((fun x v => Φ v (x v)) ∘
      ((PI.AprimeInfG.piProdEquiv (fun v => EuclideanSpace ℝ (ιv v)) (fun v => EuclideanSpace ℝ (κv v))).symm ∘
        Prod.map T T')) := rfl
  have hmap : (volume : Measure (EuclideanSpace ℝ ι × EuclideanSpace ℝ κ)).map F =
      ENNReal.ofReal (∏ v, cst v) • volume := by
    rw [hfun, ← Measure.map_map (flatL V (Fin n × Fin m × Bool)).continuous_of_finiteDimensional.measurable
      (hPm.comp h123.measurable), ← Measure.map_map hPm h123.measurable,
      show (volume : Measure (EuclideanSpace ℝ ι × EuclideanSpace ℝ κ)) = volume.prod volume from rfl,
      h123.map_eq, h4, Measure.map_smul, flatL_pres, ENNReal.ofReal_prod_of_nonneg (fun v _ => (hcst v).le)]
    rfl
  have hpos : ENNReal.ofReal (∏ v, cst v) ≠ 0 := by
    rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]
    exact Finset.prod_pos fun v _ => hcst v
  have : (volume : Measure (EuclideanSpace ℝ ι × EuclideanSpace ℝ κ)).IsAddHaarMeasure := by
    rw [show (volume : Measure (EuclideanSpace ℝ ι × EuclideanSpace ℝ κ)) = volume.prod volume from rfl]
    infer_instance
  have hbij := bij_of_map (volume : Measure (EuclideanSpace ℝ ι × EuclideanSpace ℝ κ)) volume F _ hpos
    ENNReal.ofReal_ne_top hmap
  exact ⟨(LinearEquiv.ofBijective F hbij).toContinuousLinearEquiv, fun z => hF z, hmap⟩

end PI.AprimeInfW
