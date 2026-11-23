import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.SumLPresHolds
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.PsiInv
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.CayDensExHaar

noncomputable section

namespace PI.AprimeInfW

open MeasureTheory Topology Metric Matrix Formalism.MainNotions.S Formalism.MainNotions.S.Gauge
open scoped ENNReal

namespace CDX

section Perm

variable {n : ℕ} (ε : Fin n → Bool)

abbrev pP : ℕ := Fintype.card {i : Fin n // ε i = true}

abbrev pQ : ℕ := Fintype.card {i : Fin n // ¬ ε i = true}

def eS : Fin n ≃ Fin (pP ε) ⊕ Fin (pQ ε) :=
  (Equiv.sumCompl (fun i : Fin n => ε i = true)).symm.trans
    (Equiv.sumCongr (Fintype.equivFin _) (Fintype.equivFin _))

theorem eS_symm_inl (a : Fin (pP ε)) : ε ((eS ε).symm (Sum.inl a)) = true := by
  unfold eS
  first
    | (simp; done)
    | (simp; exact ((Fintype.equivFin _).symm a).2)
    | exact ((Fintype.equivFin _).symm a).2

theorem eS_symm_inr (b : Fin (pQ ε)) : ε ((eS ε).symm (Sum.inr b)) = false := by
  unfold eS
  first
    | (simp; done)
    | (simpa using ((Fintype.equivFin _).symm b).2)
    | (simp; simpa using ((Fintype.equivFin _).symm b).2)

abbrev rA : Matrix (Fin n) (Fin n) ℂ ≃ₐ[ℂ] Matrix (Fin (pP ε) ⊕ Fin (pQ ε)) (Fin (pP ε) ⊕ Fin (pQ ε)) ℂ :=
  reindexAlgEquiv ℂ ℂ (eS ε)

theorem rA_conj (M : Matrix (Fin n) (Fin n) ℂ) : (rA ε M)ᴴ = rA ε Mᴴ := by
  ext i j
  simp [Matrix.conjTranspose_apply]

theorem rA_Jm : rA ε (Formalism.REAL.Jm ε) = HcS.UG.Jpq (pP ε) (pQ ε) := by
  ext i j
  simp only [rA, reindexAlgEquiv_apply, Matrix.reindex_apply, Matrix.submatrix_apply, Formalism.REAL.Jm, HcS.UG.Jpq,
    Matrix.diagonal_apply, (eS ε).symm.injective.eq_iff]
  rcases i with a | a <;> rcases j with b | b
  · by_cases h : a = b <;> simp [h, eS_symm_inl, Matrix.one_apply]
  · simp
  · simp
  · by_cases h : a = b <;> simp [h, eS_symm_inr, Matrix.one_apply]

theorem rA_mem_iff (M : Matrix (Fin n) (Fin n) ℂ) :
    (rA ε M)ᴴ * HcS.UG.Jpq (pP ε) (pQ ε) * rA ε M = HcS.UG.Jpq (pP ε) (pQ ε) ↔ Formalism.REAL.inUJ ε M := by
  rw [rA_conj, ← rA_Jm, ← map_mul, ← map_mul, (rA ε).injective.eq_iff]
  rfl

theorem rA_skew_iff (M : Matrix (Fin n) (Fin n) ℂ) :
    (rA ε M)ᴴ * HcS.UG.Jpq (pP ε) (pQ ε) + HcS.UG.Jpq (pP ε) (pQ ε) * rA ε M = 0 ↔
      Mᴴ * Formalism.REAL.Jm ε + Formalism.REAL.Jm ε * M = 0 := by
  rw [rA_conj, ← rA_Jm, ← map_mul, ← map_mul, ← map_add, ← map_zero (rA ε), (rA ε).injective.eq_iff]

theorem continuous_rA : Continuous (rA ε) := by
  exact LinearMap.continuous_of_finiteDimensional (rA ε).toLinearMap

theorem continuous_rA_symm : Continuous (rA ε).symm := by
  exact LinearMap.continuous_of_finiteDimensional (rA ε).symm.toLinearMap

def rM : Matrix (Fin n) (Fin n) ℂ →* Matrix (Fin (pP ε) ⊕ Fin (pQ ε)) (Fin (pP ε) ⊕ Fin (pQ ε)) ℂ where
  toFun := rA ε
  map_one' := map_one _
  map_mul' := map_mul _

def rMs : Matrix (Fin (pP ε) ⊕ Fin (pQ ε)) (Fin (pP ε) ⊕ Fin (pQ ε)) ℂ →* Matrix (Fin n) (Fin n) ℂ where
  toFun := (rA ε).symm
  map_one' := map_one _
  map_mul' := map_mul _

def phiF (g : Formalism.REAL.UJ ε) : HcS.BasicNotions.UpqT (pP ε) (pQ ε) :=
  ((⟨Units.map (rM ε) g.1, by
      rw [HcInf.mem_Upq_iff]; exact (rA_mem_iff ε _).2 g.2⟩ : HcS.UG.Upq (pP ε) (pQ ε)) :
        HcS.BasicNotions.UpqT (pP ε) (pQ ε))

theorem phiB_mem (h : HcS.BasicNotions.UpqT (pP ε) (pQ ε)) :
    Formalism.REAL.inUJ ε ((rA ε).symm (HcS.BasicNotions.UpqT.mat h)) := by
  rw [← rA_mem_iff, AlgEquiv.apply_symm_apply]
  exact (HcInf.mem_Upq_iff _ _ _).1 (h : HcS.UG.Upq (pP ε) (pQ ε)).2

def phiB (h : HcS.BasicNotions.UpqT (pP ε) (pQ ε)) : Formalism.REAL.UJ ε :=
  ⟨Units.map (rMs ε) (HcInf.toS _ _ h).1, phiB_mem ε h⟩

theorem phiF_mat (g : Formalism.REAL.UJ ε) :
    HcS.BasicNotions.UpqT.mat (phiF ε g) = rA ε (((g : (Matrix (Fin n) (Fin n) ℂ)ˣ)) : Matrix (Fin n) (Fin n) ℂ) := rfl

theorem phiB_val (h : HcS.BasicNotions.UpqT (pP ε) (pQ ε)) :
    (((phiB ε h : Formalism.REAL.UJ ε) : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) =
      (rA ε).symm (HcS.BasicNotions.UpqT.mat h) := rfl

theorem mat_mul' (a b : HcS.BasicNotions.UpqT (pP ε) (pQ ε)) :
    HcS.BasicNotions.UpqT.mat (a * b) = HcS.BasicNotions.UpqT.mat a * HcS.BasicNotions.UpqT.mat b := rfl

def phiU : Formalism.REAL.UJ ε ≃* HcS.BasicNotions.UpqT (pP ε) (pQ ε) where
  toFun := phiF ε
  invFun := phiB ε
  left_inv g := by
    apply Subtype.ext; apply Units.ext
    rw [phiB_val, phiF_mat]
    exact (rA ε).symm_apply_apply _
  right_inv h := by
    apply (HcInf.isClosedEmbedding_mat _ _).injective
    rw [phiF_mat, phiB_val]
    exact (rA ε).apply_symm_apply _
  map_mul' a b := by
    apply (HcInf.isClosedEmbedding_mat _ _).injective
    rw [mat_mul', phiF_mat, phiF_mat, phiF_mat, Subgroup.coe_mul, Units.val_mul]
    exact map_mul (rA ε) _ _

theorem continuous_phiF : Continuous (phiF ε) := by
  first
  | exact (HcInf.isClosedEmbedding_mat _ _).isInducing.continuous_iff.mpr
      ((continuous_rA ε).comp (Units.continuous_val.comp continuous_subtype_val))
  | exact (HcInf.isClosedEmbedding_mat _ _).toIsInducing.continuous_iff.mpr
      ((continuous_rA ε).comp (Units.continuous_val.comp continuous_subtype_val))

theorem continuous_toS : Continuous fun h : HcS.BasicNotions.UpqT (pP ε) (pQ ε) =>
    ((HcInf.toS _ _ h : HcS.UG.Upq (pP ε) (pQ ε)) : GL (Fin (pP ε) ⊕ Fin (pQ ε)) ℂ) :=
  continuous_subtype_val

theorem continuous_phiB : Continuous (phiB ε) :=
  ((Continuous.units_map (rMs ε) (continuous_rA_symm ε)).comp (continuous_toS ε)).subtype_mk _

def phiC : Formalism.REAL.UJ ε ≃ₜ* HcS.BasicNotions.UpqT (pP ε) (pQ ε) where
  toMulEquiv := phiU ε
  continuous_toFun := continuous_phiF ε
  continuous_invFun := continuous_phiB ε

def psiL : gLie ε →ₗ[ℝ] HcS.BasicNotions.lieU (pP ε) (pQ ε) where
  toFun x := ⟨rA ε (unrealify (x : EuclideanSpace ℝ (Fin n × Fin n × Bool))), by
    show (rA ε _)ᴴ * HcS.UG.Jpq (pP ε) (pQ ε) + HcS.UG.Jpq (pP ε) (pQ ε) * rA ε _ = 0
    rw [rA_skew_iff]
    exact lieSkew_holds n ε _ x.2⟩
  map_add' x y := by
    apply Subtype.ext
    show rA ε (unrLin n ((x + y : gLie ε) : EuclideanSpace ℝ _)) = rA ε (unrLin n x) + rA ε (unrLin n y)
    rw [Submodule.coe_add, map_add, map_add]
  map_smul' c x := by
    apply Subtype.ext
    ext i j
    apply Complex.ext <;> simp [unrealify]

theorem psiL_val (x : gLie ε) :
    (psiL ε x).1 =
      rA ε (unrealify (x : EuclideanSpace ℝ (Fin n × Fin n × Bool))) := rfl

theorem psiL_bij : Function.Bijective (psiL ε) := by
  constructor
  · intro x y hxy
    have h1 : rA ε (unrealify (x : EuclideanSpace ℝ (Fin n × Fin n × Bool))) =
        rA ε (unrealify (y : EuclideanSpace ℝ (Fin n × Fin n × Bool))) := by
      rw [← psiL_val, ← psiL_val, hxy]
    have h2 := (rA ε).injective h1
    apply Subtype.ext
    rw [← re_unr n (x : EuclideanSpace ℝ _), ← re_unr n (y : EuclideanSpace ℝ _)]
    exact congrArg (reLin n) h2
  · intro Y
    set X := (rA ε).symm Y.1 with hX
    have hY : Y.1ᴴ * HcS.UG.Jpq (pP ε) (pQ ε) + HcS.UG.Jpq (pP ε) (pQ ε) * Y.1 = 0 :=
      Y.2
    have hsk : Xᴴ * Formalism.REAL.Jm ε + Formalism.REAL.Jm ε * X = 0 := by
      rw [← rA_skew_iff, hX, AlgEquiv.apply_symm_apply]; exact hY
    refine ⟨⟨(WithLp.equiv 2 _).symm (realifyFun X), skewLie_holds n ε X hsk⟩, ?_⟩
    apply Subtype.ext
    rw [psiL_val]
    show rA ε (unrealify ((WithLp.equiv 2 _).symm (realifyFun X))) = _
    rw [unr_re, hX, AlgEquiv.apply_symm_apply]

def psiC : gLie ε ≃L[ℝ] HcS.BasicNotions.lieU (pP ε) (pQ ε) :=
  (LinearEquiv.ofBijective (psiL ε) (psiL_bij ε)).toContinuousLinearEquiv

theorem psiC_val (x : gLie ε) :
    (psiC ε x).1 =
      rA ε (unrealify (x : EuclideanSpace ℝ (Fin n × Fin n × Bool))) := rfl

theorem rel_iff (g : Formalism.REAL.UJ ε) (x : gLie ε) :
    HcS.BasicNotions.UpqT.mat (phiC ε g) * ((1 + 1) - (psiC ε x).1) =
        (1 + 1) + (psiC ε x).1 ↔
      (((g : (Matrix (Fin n) (Fin n) ℂ)ˣ)) : Matrix (Fin n) (Fin n) ℂ) *
          (2 - unrealify (x : EuclideanSpace ℝ (Fin n × Fin n × Bool))) =
        2 + unrealify (x : EuclideanSpace ℝ (Fin n × Fin n × Bool)) := by
  have e1 : HcS.BasicNotions.UpqT.mat (phiC ε g) = rA ε (((g : (Matrix (Fin n) (Fin n) ℂ)ˣ)) : Matrix (Fin n) (Fin n) ℂ) :=
    phiF_mat ε g
  rw [e1, psiC_val, one_add_one_eq_two, ← map_ofNat (rA ε) 2, ← map_sub, ← map_mul, ← map_add,
    (rA ε).injective.eq_iff]

theorem isUnit_of_mem_cayley_domain (x : gLie ε) (hx : psiC ε x ∈ HcInf.D0 (pP ε) (pQ ε)) :
    IsUnit (2 - unrealify (x : EuclideanSpace ℝ (Fin n × Fin n × Bool))).det := by
  have h : IsUnit ((1 + 1) - ((psiC ε x : HcS.BasicNotions.lieU (pP ε) (pQ ε)) :
      Matrix (Fin (pP ε) ⊕ Fin (pQ ε)) (Fin (pP ε) ⊕ Fin (pQ ε)) ℂ)).det := hx
  rw [psiC_val] at h
  have e : (1 + 1 : Matrix (Fin (pP ε) ⊕ Fin (pQ ε)) (Fin (pP ε) ⊕ Fin (pQ ε)) ℂ) -
      rA ε (unrealify (x : EuclideanSpace ℝ (Fin n × Fin n × Bool))) =
      rA ε (2 - unrealify (x : EuclideanSpace ℝ (Fin n × Fin n × Bool))) := by
    rw [map_sub, map_ofNat, one_add_one_eq_two]
  rw [e] at h
  simpa [Matrix.det_reindex_self] using h

theorem cayR_eq (x : EuclideanSpace ℝ (Fin n × Fin n × Bool)) (g : Formalism.REAL.UJ ε)
    (h : (2 + unrealify x) * (2 - unrealify x)⁻¹ = (((g : (Matrix (Fin n) (Fin n) ℂ)ˣ)) : Matrix (Fin n) (Fin n) ℂ)) :
    cayR ε x = g := by
  have hc : IsUnit ((2 + unrealify x) * (2 - unrealify x)⁻¹) ∧
      Formalism.REAL.inUJ ε ((2 + unrealify x) * (2 - unrealify x)⁻¹) := by
    rw [h]; exact ⟨(g : (Matrix (Fin n) (Fin n) ℂ)ˣ).isUnit, g.2⟩
  unfold cayR
  rw [dif_pos hc]
  apply Subtype.ext; apply Units.ext
  rw [IsUnit.unit_spec]; exact h

theorem cay_mat (x : EuclideanSpace ℝ (Fin n × Fin n × Bool)) (M : Matrix (Fin n) (Fin n) ℂ)
    (hu : IsUnit (2 - unrealify x).det) (h : M * (2 - unrealify x) = 2 + unrealify x) :
    (2 + unrealify x) * (2 - unrealify x)⁻¹ = M := by
  rw [← h, Matrix.mul_nonsing_inv_cancel_right _ _ hu]

end Perm

end CDX

open CDX in

theorem cayDensEx_holds : CayDensEx := by
  intro n ε
  classical
  set φ := phiC ε with hφ
  set ψ := psiC ε with hψ
  set φM := φ.toHomeomorph.toMeasurableEquiv with hφM
  set ψM := ψ.toHomeomorph.toMeasurableEquiv with hψM
  set m : Measure (HcS.BasicNotions.UpqT (pP ε) (pQ ε)) := (Formalism.REAL.muG ε).map φM with hm
  haveI : m.IsHaarMeasure := ContinuousMulEquiv.isHaarMeasure_map (Formalism.REAL.muG ε) φ
  set lam : Measure (HcS.BasicNotions.lieU (pP ε) (pQ ε)) := (volume : Measure (gLie ε)).map ψM with hlam
  haveI : lam.IsAddHaarMeasure := ψ.isAddHaarMeasure_map volume
  obtain ⟨D, hD, hDm, f, hfm, hfc, -, hfT, hmap⟩ := HcHDC.cayDensU (pP ε) (pQ ε) m lam
  have hψ0 : ψ 0 = 0 := map_zero ψ
  have hψc : ContinuousAt ψ 0 := ψ.continuous.continuousAt
  have hN1 : ψ ⁻¹' D ∈ 𝓝 (0 : gLie ε) := hψc.preimage_mem_nhds (by rw [hψ0]; exact hD)
  have hN2 : ψ ⁻¹' HcInf.D0 (pP ε) (pQ ε) ∈ 𝓝 (0 : gLie ε) :=
    hψc.preimage_mem_nhds (by rw [hψ0]; exact HcInf.isOpen_cell_domain.mem_nhds HcInf.zero_mem_cayley_domain)
  have hN3 : ψ ⁻¹' {X | f X ≠ ⊤} ∈ 𝓝 (0 : gLie ε) :=
    hψc.preimage_mem_nhds (by rw [hψ0]; exact hfc.eventually_ne hfT)
  obtain ⟨r₀, hr₀, hball⟩ := Metric.mem_nhds_iff.1 (Filter.inter_mem (Filter.inter_mem hN1 hN2) hN3)
  refine ⟨r₀, hr₀, fun x => (f (ψ x)).toReal, ?_, ?_, ?_⟩
  · exact ENNReal.measurable_toReal.comp (hfm.comp ψ.continuous.measurable)
  · have h1 : ContinuousAt (fun x => f (ψ x)) 0 :=
      ContinuousAt.comp (x := 0) (by rw [hψ0]; exact hfc) hψc
    have h2 : ContinuousAt ENNReal.toReal (f (ψ 0)) := ENNReal.continuousAt_toReal (by rw [hψ0]; exact hfT)
    exact ContinuousAt.comp (f := fun x => f (ψ x)) (x := 0) h2 h1
  · intro S hS hSm
    have hpt : ∀ x ∈ S, ψ x ∈ D ∧ ψ x ∈ HcInf.D0 (pP ε) (pQ ε) ∧ f (ψ x) ≠ ⊤ := fun x hx =>
      ⟨(hball (hS hx)).1.1, (hball (hS hx)).1.2, (hball (hS hx)).2⟩
    set T := ψM '' S with hTdef
    have hT : MeasurableSet T := ψM.measurableSet_image.2 hSm
    have hTD : T ⊆ D := by rintro _ ⟨x, hx, rfl⟩; exact (hpt x hx).1

    have hset : φM ⁻¹' HcInf.cayS T =
        (fun x : gLie ε => cayR ε (x : EuclideanSpace ℝ (Fin n × Fin n × Bool))) '' S := by
      ext g
      constructor
      · rintro ⟨X, ⟨x, hx, rfl⟩, hgX⟩
        refine ⟨x, hx, ?_⟩
        have hu := isUnit_of_mem_cayley_domain ε x (hpt x hx).2.1
        exact cayR_eq ε _ g (cay_mat _ _ hu ((rel_iff ε g x).1 hgX))
      · rintro ⟨x, hx, rfl⟩
        have hD0 := (hpt x hx).2.1
        have hu := isUnit_of_mem_cayley_domain ε x hD0
        set h := HcInf.cayF (pP ε) (pQ ε) (ψ x) with hh
        have hs := HcInf.cayF_spec (ψ x) hD0
        have hrel := (rel_iff ε (φ.symm h) x).1 (by rw [ContinuousMulEquiv.apply_symm_apply]; exact hs)
        have hc : cayR ε (x : EuclideanSpace ℝ (Fin n × Fin n × Bool)) = φ.symm h :=
          cayR_eq ε _ _ (cay_mat _ _ hu hrel)
        refine ⟨ψ x, ⟨x, hx, rfl⟩, ?_⟩
        show HcS.BasicNotions.UpqT.mat (φ (cayR ε (x : EuclideanSpace ℝ (Fin n × Fin n × Bool)))) * _ = _
        rw [hc, ContinuousMulEquiv.apply_symm_apply]
        exact hs
    have hsetD : HcInf.cayInv (pP ε) (pQ ε) ⁻¹' T ∩ HcInf.cayS D = HcInf.cayS T := by
      ext g
      constructor
      · rintro ⟨hgT, X, hXD, hgX⟩
        have e := HcInf.cayley_inverse_iff _ _ g X hgX
        exact ⟨X, e ▸ hgT, hgX⟩
      · rintro ⟨X, hXT, hgX⟩
        have e := HcInf.cayley_inverse_iff _ _ g X hgX
        exact ⟨show HcInf.cayInv _ _ g ∈ T from e ▸ hXT, X, hTD hXT, hgX⟩
    have hmeasT := HcInf.cayley_inverse_measurable (pP ε) (pQ ε) hT
    calc Formalism.REAL.muG ε ((fun x : gLie ε => cayR ε (x : EuclideanSpace ℝ (Fin n × Fin n × Bool))) '' S)
        = m (HcInf.cayS T) := by rw [hm, MeasurableEquiv.map_apply, hset]
      _ = ((m.restrict (HcInf.cayS D)).map (HcInf.cayInv (pP ε) (pQ ε))) T := by
          rw [Measure.map_apply (HcInf.cayley_inverse_measurable _ _) hT, Measure.restrict_apply hmeasT, hsetD]
      _ = ∫⁻ X in T, f X ∂lam := by
          rw [hmap, withDensity_apply _ hT, Measure.restrict_restrict hT, Set.inter_eq_left.2 hTD]
      _ = ∫⁻ x in S, f (ψ x) := by
          rw [hlam, MeasurableEquiv.restrict_map, hTdef, MeasurableEquiv.preimage_image, lintegral_map_equiv]
          rfl
      _ = ∫⁻ x in S, ENNReal.ofReal ((f (ψ x)).toReal) := by
          refine setLIntegral_congr_fun hSm (fun x hx => ?_)
          exact (ENNReal.ofReal_toReal (hpt x hx).2.2).symm

end PI.AprimeInfW
