import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.HeckeFubiniCompatibility.CompatFub
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.HeckeFubiniCompatibility.PSplit
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LcscAdelicUnitaryGroup

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Measure Topology
open GlobalTheory.CuspRep PositivityTheory.Rg.BcB.E
open PositivityTheory.RgTw (G)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf)

attribute [local instance] PositivityTheory.Rg.BcB.E.borelH

namespace PositivityTheory.Rg.BcB.CG

section Gen

theorem hasCompactSupport_slice {A B : Type} [TopologicalSpace A] [TopologicalSpace B] [T2Space B] {F : A × B → ℂ}
    (hF : HasCompactSupport F) (a : A) : HasCompactSupport (fun b => F (a, b)) :=
  HasCompactSupport.intro (hF.isCompact.image continuous_snd) fun b hb =>
    image_eq_zero_of_notMem_tsupport fun h => hb ⟨(a, b), h, rfl⟩

theorem integral_tensor {X Y Z : Type} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z] (mX : Measure X) (mY : Measure Y) (mZ : Measure Z) [SigmaFinite mX] [SigmaFinite mY]
    [SigmaFinite mZ] (p : X → ℂ) (q : Y → ℂ) (r : Z → ℂ) :
    ∫ z, p z.1 * q z.2.1 * r z.2.2 ∂(mX.prod (mY.prod mZ)) = (∫ x, p x ∂mX) * (∫ y, q y ∂mY) * ∫ w, r w ∂mZ := by
  calc ∫ z, p z.1 * q z.2.1 * r z.2.2 ∂(mX.prod (mY.prod mZ))
      = ∫ z, p z.1 * (fun w : Y × Z => q w.1 * r w.2) z.2 ∂(mX.prod (mY.prod mZ)) := by simp only [mul_assoc]
    _ = (∫ x, p x ∂mX) * ∫ w, q w.1 * r w.2 ∂(mY.prod mZ) :=
      integral_prod_mul (L := ℂ) (μ := mX) (ν := mY.prod mZ) p (fun w : Y × Z => q w.1 * r w.2)
    _ = _ := by rw [integral_prod_mul (L := ℂ) (μ := mY) (ν := mZ) q r, mul_assoc]

end Gen

section Abstract

variable {X : Type} [Group X] [TopologicalSpace X] [IsTopologicalGroup X] [LocallyCompactSpace X]
  [SecondCountableTopology X] [T2Space X] [MeasurableSpace X] [BorelSpace X]
variable {Y : Type} [Group Y] [TopologicalSpace Y] [IsTopologicalGroup Y] [LocallyCompactSpace Y]
  [SecondCountableTopology Y] [T2Space Y] [MeasurableSpace Y] [BorelSpace Y]
variable {Z : Type} [Group Z] [TopologicalSpace Z] [IsTopologicalGroup Z] [LocallyCompactSpace Z]
  [SecondCountableTopology Z] [T2Space Z] [MeasurableSpace Z] [BorelSpace Z]
variable {K : Type} [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [MeasurableSpace K] [BorelSpace K]

omit [SecondCountableTopology X] in
theorem exists_bump (μ : Measure X) [IsHaarMeasure μ] :
    ∃ f : X → ℂ, Continuous f ∧ HasCompactSupport f ∧ ∫ x, f x ∂μ ≠ 0 := by
  obtain ⟨f, hf1, -, hfc, hf01⟩ := exists_continuous_one_zero_of_isCompact (isCompact_singleton (x := (1 : X)))
    isClosed_empty (Set.disjoint_empty _)
  refine ⟨fun x => ((f x : ℝ) : ℂ), Complex.continuous_ofReal.comp f.continuous, hfc.comp_left Complex.ofReal_zero, ?_⟩
  show ∫ x, ((f x : ℝ) : ℂ) ∂μ ≠ 0
  rw [show ∫ x, ((f x : ℝ) : ℂ) ∂μ = ((∫ x, f x ∂μ : ℝ) : ℂ) from integral_ofReal, Complex.ofReal_ne_zero]
  exact (f.continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero hfc (fun x => (hf01 x).1) (x := 1)
    (by simp [hf1 (Set.mem_singleton (1 : X))])).ne'

theorem exists_split (e : X × (Y × Z) ≃ₜ* K) (μ : Measure K) [IsHaarMeasure μ] (mX : Measure X) [IsHaarMeasure mX]
    (mY : Measure Y) [IsHaarMeasure mY] (mZ : Measure Z) [IsHaarMeasure mZ] :
    ∃ c : NNReal, 0 < c ∧ ∀ f : K → ℂ, ∫ g, f g ∂μ = c • ∫ z, f (e z) ∂(mX.prod (mY.prod mZ)) := by
  haveI : IsHaarMeasure (μ.map e.symm) := ContinuousMulEquiv.isHaarMeasure_map μ e.symm
  obtain ⟨c, hc0, h⟩ : ∃ c : NNReal, 0 < c ∧ μ.map e.symm = c • mX.prod (mY.prod mZ) :=
    ⟨_, haarScalarFactor_pos_of_isHaarMeasure _ _, isMulLeftInvariant_eq_smul _ _⟩
  refine ⟨c, hc0, fun f => ?_⟩
  have he : ∫ z, f (e z) ∂(μ.map e.symm) = ∫ g, f g ∂μ := by
    have := integral_map_equiv (μ := μ) (e.toHomeomorph.toMeasurableEquiv.symm) (fun z => f (e z))
    refine this.trans ?_
    congr 1
    funext x
    exact congrArg f (e.apply_symm_apply x)
  rw [← he, h, integral_smul_nnreal_measure]

theorem integral_iter (mX : Measure X) [IsHaarMeasure mX] (mY : Measure Y) [IsHaarMeasure mY] (mZ : Measure Z)
    [IsHaarMeasure mZ] (f : X × (Y × Z) → ℂ) (hf : Continuous f) (hfc : HasCompactSupport f) :
    ∫ z, f z ∂(mX.prod (mY.prod mZ)) = ∫ x, ∫ y, ∫ w, f (x, (y, w)) ∂mZ ∂mY ∂mX := by
  rw [integral_prod _ (hf.integrable_of_hasCompactSupport hfc)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  exact integral_prod _ ((hf.comp (continuous_const.prodMk continuous_id)).integrable_of_hasCompactSupport
    (hasCompactSupport_slice hfc x))

end Abstract

section Inst

theorem lc_G (n : ℕ) : LocallyCompactSpace (G n) := Units.isClosedEmbedding_embedProduct.locallyCompactSpace

theorem sc_G (n : ℕ) : SecondCountableTopology (G n) :=
  haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) ℂ) :=
    inferInstanceAs (SecondCountableTopology (Fin n → Fin n → ℂ))
  haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) ℂ)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology
  Units.isEmbedding_embedProduct.secondCountableTopology

variable (E : Type) [Field E] [NumberField E]

theorem lc_GLf (n : ℕ) : LocallyCompactSpace (GL (Fin n) (Af E)) :=
  haveI := GlobalTheory.AdelicUnitaryTop.locallyCompact_finiteAdele E
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_finiteAdeleRing_of_numberField E
  haveI : LocallyCompactSpace (Matrix (Fin n) (Fin n) (Af E)) :=
    inferInstanceAs (LocallyCompactSpace (Fin n → Fin n → Af E))
  haveI : LocallyCompactSpace (Matrix (Fin n) (Fin n) (Af E))ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isClosedEmbedding.locallyCompactSpace
  Units.isClosedEmbedding_embedProduct.locallyCompactSpace

theorem sc_GLf (n : ℕ) : SecondCountableTopology (GL (Fin n) (Af E)) :=
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_finiteAdele E
  haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) (Af E)) :=
    inferInstanceAs (SecondCountableTopology (Fin n → Fin n → Af E))
  haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) (Af E))ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology
  Units.isEmbedding_embedProduct.secondCountableTopology

theorem t2_GL_finite_adeles (n : ℕ) : T2Space (GL (Fin n) (Af E)) :=
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_finiteAdeleRing_of_numberField E
  Units.isEmbedding_embedProduct.t2Space

end Inst

attribute [local instance] lc_G sc_G lc_GLf sc_GLf t2_GL_finite_adeles

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ}

theorem borelSpaceH : BorelSpace (H E a b) := ⟨rfl⟩

attribute [local instance] borelSpaceH

theorem haar_of_dom (D : Dom E a b) : IsHaarMeasure D.μ :=
  haveI := D.haar.2.2.2
  { toIsFiniteMeasureOnCompacts := isFiniteMeasureOnCompacts_of_isLocallyFiniteMeasure
    toIsMulLeftInvariant := D.haar.1
    toIsOpenPosMeasure := D.haar.2.2.1 }

def tensH (fa : InfinitePlace E → G a → ℂ) (fb : InfinitePlace E → G b → ℂ) (ψ : Hf E a b → ℂ) (g : H E a b) : ℂ :=
  (∏ v, fa v (gInf v g.1)) * (∏ v, fb v (gInf v g.2)) * ψ (hFin g)

theorem tensH_splitH (fa : InfinitePlace E → G a → ℂ) (fb : InfinitePlace E → G b → ℂ) (ψ : Hf E a b → ℂ)
    (z : (InfinitePlace E → G a) × ((InfinitePlace E → G b) × Hf E a b)) :
    tensH fa fb ψ (splitH a b z) = (∏ v, fa v (z.1 v)) * (∏ v, fb v (z.2.1 v)) * ψ z.2.2 := by
  simp only [tensH, gInf_splitH₁, gInf_splitH₂, hFin_splitH]

theorem integral_tensH_splitH [MeasurableSpace (G a)] [MeasurableSpace (G b)] [MeasurableSpace (Hf E a b)]
    (μa : Measure (G a)) [SigmaFinite μa] (μb : Measure (G b)) [SigmaFinite μb] (ν : Measure (Hf E a b)) [SigmaFinite ν]
    (fa : InfinitePlace E → G a → ℂ) (fb : InfinitePlace E → G b → ℂ) (ψ : Hf E a b → ℂ) :
    ∫ z, tensH fa fb ψ (splitH a b z) ∂((Measure.pi fun _ : InfinitePlace E => μa).prod
      ((Measure.pi fun _ : InfinitePlace E => μb).prod ν)) =
      (∏ v, ∫ y, fa v y ∂μa) * (∏ v, ∫ y, fb v y ∂μb) * ∫ h, ψ h ∂ν := by
  simp_rw [tensH_splitH]
  rw [integral_tensor _ _ _ (fun y : InfinitePlace E → G a => ∏ v, fa v (y v))
    (fun y : InfinitePlace E → G b => ∏ v, fb v (y v)) ψ]
  beta_reduce
  rw [integral_fintype_prod_eq_prod, integral_fintype_prod_eq_prod]

theorem compatFub : CompatFub := by
  intro E _ _ _ a b D _ _ _ _ _ _ μa _ μb _ ν _ hC F hF hFc
  haveI := haar_of_dom D
  have : IsHaarMeasure (Measure.pi fun _ : InfinitePlace E => μa) := pi.isHaarMeasure _
  have : IsHaarMeasure (Measure.pi fun _ : InfinitePlace E => μb) := pi.isHaarMeasure _
  obtain ⟨c, hc0, hc⟩ := exists_split (splitH a b) D.μ (Measure.pi fun _ : InfinitePlace E => μa)
    (Measure.pi fun _ : InfinitePlace E => μb) ν
  obtain ⟨fa, hfa, hfac, hfa0⟩ := exists_bump μa
  obtain ⟨fb, hfb, hfbc, hfb0⟩ := exists_bump μb
  obtain ⟨ψ, hψ, hψc, hψ0⟩ := exists_bump ν
  have h1 := hC (fun _ => fa) (fun _ => fb) ψ (fun _ => ⟨hfa, hfac⟩) (fun _ => ⟨hfb, hfbc⟩) hψ hψc
  change ∫ g, tensH (fun _ => fa) (fun _ => fb) ψ g ∂D.μ = _ at h1
  rw [hc, integral_tensH_splitH] at h1
  have hc1 : c = 1 := by
    have hne : (∏ _v : InfinitePlace E, ∫ y, fa y ∂μa) * (∏ _v : InfinitePlace E, ∫ y, fb y ∂μb) * ∫ h, ψ h ∂ν ≠ 0 := by
      simp [hfa0, hfb0, hψ0]
    rw [NNReal.smul_def, Complex.real_smul] at h1
    have h2 : ((c : ℝ) : ℂ) = 1 := mul_right_cancel₀ hne (by rw [one_mul]; exact h1)
    exact_mod_cast h2
  rw [hc F, hc1, one_smul]
  exact integral_iter _ _ _ (fun z => F (splitH a b z)) (hF.comp (splitH a b).continuous)
    (hFc.comp_homeomorph (splitH a b).toHomeomorph)

theorem compatEx : CompatEx := by
  intro E _ _ _ a b D _ _ _ _ _ _ μa _ μb _
  haveI := haar_of_dom D
  haveI : D.μ.IsMulRightInvariant := D.haar.2.1
  have : IsHaarMeasure (Measure.pi fun _ : InfinitePlace E => μa) := pi.isHaarMeasure _
  have : IsHaarMeasure (Measure.pi fun _ : InfinitePlace E => μb) := pi.isHaarMeasure _
  set ν₀ : Measure (Hf E a b) := Measure.haar
  obtain ⟨c, hc0, hc⟩ := exists_split (splitH a b) D.μ (Measure.pi fun _ : InfinitePlace E => μa)
    (Measure.pi fun _ : InfinitePlace E => μb) ν₀
  obtain ⟨fa, hfa, hfac, hfa0⟩ := exists_bump μa
  obtain ⟨fb, hfb, hfbc, hfb0⟩ := exists_bump μb
  have hR : ∀ h : Hf E a b, ν₀.map (· * h) = ν₀ := by
    intro h
    obtain ⟨k, hk⟩ : ∃ k : NNReal, ν₀.map (· * h) = k • ν₀ := ⟨_, isMulLeftInvariant_eq_smul _ _⟩
    obtain ⟨ψ, hψ, hψc, hψ0⟩ := exists_bump ν₀
    have h1 := integral_mul_right_eq_self (μ := D.μ) (tensH (fun _ => fa) (fun _ => fb) ψ) (splitH a b (1, (1, h)))
    rw [hc, hc] at h1
    have e1 : ∀ z : (InfinitePlace E → G a) × ((InfinitePlace E → G b) × Hf E a b),
        tensH (fun _ => fa) (fun _ => fb) ψ (splitH a b z * splitH a b (1, (1, h))) =
          (∏ v, fa (z.1 v)) * (∏ v, fb (z.2.1 v)) * ψ (z.2.2 * h) := by
      intro z
      rw [← map_mul, tensH_splitH]
      simp
    simp_rw [e1] at h1
    rw [integral_tensor _ _ _ (fun y : InfinitePlace E → G a => ∏ v, fa (y v))
      (fun y : InfinitePlace E → G b => ∏ v, fb (y v)) (fun w : Hf E a b => ψ (w * h)),
      integral_tensH_splitH] at h1
    beta_reduce at h1
    rw [integral_fintype_prod_eq_prod, integral_fintype_prod_eq_prod] at h1
    have e2 : ∫ w, ψ (w * h) ∂ν₀ = k • ∫ w, ψ w ∂ν₀ := by
      rw [← integral_smul_nnreal_measure, ← hk, integral_map (measurable_mul_const h).aemeasurable
        hψ.aestronglyMeasurable]
    rw [e2] at h1
    have hne : (∏ _v : InfinitePlace E, ∫ y, fa y ∂μa) * (∏ _v : InfinitePlace E, ∫ y, fb y ∂μb) * ∫ w, ψ w ∂ν₀ ≠ 0 := by
      simp [hfa0, hfb0, hψ0]
    simp only [NNReal.smul_def, Complex.real_smul] at h1
    have hc' : ((c : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hc0.ne'
    have h2 : ((k : ℝ) : ℂ) * (((c : ℝ) : ℂ) * ((∏ _v : InfinitePlace E, ∫ y, fa y ∂μa) *
        (∏ _v : InfinitePlace E, ∫ y, fb y ∂μb) * ∫ w, ψ w ∂ν₀)) = 1 * (((c : ℝ) : ℂ) *
        ((∏ _v : InfinitePlace E, ∫ y, fa y ∂μa) * (∏ _v : InfinitePlace E, ∫ y, fb y ∂μb) * ∫ w, ψ w ∂ν₀)) := by
      linear_combination h1
    have h3 : ((k : ℝ) : ℂ) = 1 := mul_right_cancel₀ (mul_ne_zero hc' hne) h2
    have hk1 : k = 1 := by exact_mod_cast h3
    rw [hk, hk1, one_smul]
  haveI : ν₀.IsMulRightInvariant := ⟨hR⟩
  refine ⟨c • ν₀, IsHaarMeasure.nnreal_smul _ hc0.ne', ⟨fun h => by rw [Measure.map_smul, hR]⟩, ?_⟩
  intro fa' fb' ψ' hfa' hfb' hψ' hψc'
  change ∫ g, tensH fa' fb' ψ' g ∂D.μ = _
  rw [hc, integral_tensH_splitH, integral_smul_nnreal_measure]
  simp only [NNReal.smul_def, Complex.real_smul]
  ring

end PositivityTheory.Rg.BcB.CG

end
