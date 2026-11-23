import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InclRMulPtAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DifferentCoprimeAtGoodPlaces
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDualFamilyOfIsLattice
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetNeZeroOfHasSig

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc GlobalTheory.InertCoord
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.SkewFrameInert

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {v : Pl F} {w : HeightOneSpectrum (𝓞 E)}

theorem mul_mem_range_of_trace {t : 𝓞 E} (ht : t ∈ differentIdeal ℤ (𝓞 E)) {z : E}
    (hz : ∀ o : 𝓞 E, IsIntegral ℤ (Algebra.trace ℚ E (o * z))) : (t : E) * z ∈ (algebraMap (𝓞 E) E).range := by
  have hz' : z ∈ FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) := by
    rw [FractionalIdeal.mem_dual (one_ne_zero : (1 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) ≠ 0)]
    intro a ha
    obtain ⟨o, rfl⟩ := (FractionalIdeal.mem_one_iff _).1 ha
    rw [Algebra.traceForm_apply, mul_comm]
    exact IsIntegrallyClosed.isIntegral_iff.mp (hz o)
  have ht' : (t : E) ∈ ((differentIdeal ℤ (𝓞 E) : Ideal (𝓞 E)) : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) :=
    (FractionalIdeal.mem_coeIdeal _).2 ⟨t, ht, rfl⟩
  rw [coeIdeal_differentIdeal ℤ ℚ] at ht'
  have hm := FractionalIdeal.mul_mem_mul ht' hz'
  rw [inv_mul_cancel₀ (FractionalIdeal.dual_ne_zero ℤ ℚ (one_ne_zero : (1 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) ≠ 0))] at hm
  exact (FractionalIdeal.mem_one_iff _).1 hm

theorem exists_mem_different {σ : E →ₐ[F] E} {B : Base F E} (hB : B.IsGood σ) (hw : Formalism.UG.IsInertAt F E v w)
    (h : w.under (𝓞 F) = v) : ∃ t ∈ differentIdeal ℤ (𝓞 E), t ∉ w.asIdeal := by
  by_contra hcon
  push_neg at hcon
  have hle : differentIdeal ℤ (𝓞 E) ≤ w.asIdeal := fun t ht => hcon t ht
  rw [differentIdeal_eq_differentIdeal_mul_differentIdeal ℤ (𝓞 F) (𝓞 E)] at hle
  rcases (Ideal.IsPrime.mul_le w.isPrime).1 hle with h1 | h2
  · have := hB.unram
    have hu : Algebra.IsUnramifiedAt (𝓞 F) w.asIdeal := inferInstance
    exact (not_dvd_differentIdeal_iff.2 hu) (Ideal.dvd_iff_le.2 h1)
  · rw [Ideal.map_le_iff_le_comap] at h2
    have hc : w.asIdeal.comap (algebraMap (𝓞 F) (𝓞 E)) = v.asIdeal := by
      rw [← h]; rfl
    rw [hc] at h2
    exact GlobalTheory.DiffCoprimeP.not_le_differentIdeal_of_psiUnr hB.std v (hB.inert v w hw).2.2 h2

theorem latLoc_le (hw : Formalism.UG.IsInertAt F E v w) (h : w.under (𝓞 F) = v) {n : ℕ}
    {L L' : Submodule (𝓞 E) (Fin n → E)} {t : 𝓞 E} (ht : t ∉ w.asIdeal) (hL : ∀ y ∈ L, t • y ∈ L') :
    latLoc F L v ≤ latLoc F L' v := by
  have key : GlobalTheory.LFun.latAt w L ≤ GlobalTheory.LFun.latAt w L' := by
    unfold GlobalTheory.LFun.latAt
    rw [Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    have htx := hL x hx
    have hv : Valued.v (algebraMap E (w.adicCompletion E) (t : E)) = 1 := by
      have e1 := IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (v := w) (t : E)
      refine e1.trans ?_
      exact (IsDedekindDomain.HeightOneSpectrum.valuation_eq_one_iff_notMem (K := E) w).2 ht
    have hne : algebraMap E (w.adicCompletion E) (t : E) ≠ 0 := by
      intro h0
      rw [h0, map_zero] at hv
      exact zero_ne_one hv
    have hu : (algebraMap E (w.adicCompletion E) (t : E))⁻¹ ∈ w.adicCompletionIntegers E := by
      rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, hv, inv_one]
    have heq : (fun i => algebraMap E (w.adicCompletion E) (x i)) = (⟨_, hu⟩ : Formalism.UG.Ov E w) •
        (fun i => algebraMap E (w.adicCompletion E) ((t • x) i)) := by
      funext i
      have hc : ((t • x) i : E) = (t : E) * x i := rfl
      show _ = (algebraMap E (w.adicCompletion E) (t : E))⁻¹ * algebraMap E (w.adicCompletion E) ((t • x) i)
      rw [hc, map_mul, ← mul_assoc, inv_mul_cancel₀ hne, one_mul]
    rw [SetLike.mem_coe]
    show (fun i => algebraMap E (w.adicCompletion E) (x i)) ∈ _
    rw [heq]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨t • x, htx, rfl⟩)
  intro y hy
  rw [GlobalTheory.LFun.InertChart.mem_latLoc_iff (L := L) hw h] at hy
  rw [GlobalTheory.LFun.InertChart.mem_latLoc_iff (L := L') hw h]
  exact key hy

omit [NumberField F] [NumberField E] in
theorem hE_smul_transpose (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (c : E) (x y : Fin n → E) :
    hE σ (c • Jᵀ) x y = c * form σ J y x := by
  simp only [hE, Formalism.UG.hform, form, dotProduct, Matrix.mulVec, Matrix.smul_apply, Matrix.transpose_apply,
    smul_eq_mul, Finset.mul_sum, AlgHom.coe_toRingHom]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem det_ne_zero {σ : E →ₐ[F] E} {B : Base F E} {n r s : ℕ} {X : Spc F E n} (hX : X.IsSkew σ B r s) :
    X.J.det ≠ 0 := by
  obtain ⟨w0⟩ : Nonempty (InfinitePlace F) := inferInstance
  have h0 := GlobalTheory.SigDet.det_ne_zero_of_hasSig _ _ r s (hX.sig w0)
  intro hJ
  apply h0
  rw [Matrix.det_smul, ← RingHom.mapMatrix_apply, ← RingHom.map_det, hJ, map_zero, mul_zero]

private theorem form_smul_left_divisor (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (c : 𝓞 E)
    (y x : Fin n → E) : form σ J (c • y) x = (c : E) * form σ J y x := by
  show ((c : E) • y) ⬝ᵥ _ = _
  rw [smul_dotProduct, smul_eq_mul]
  rfl

theorem isSelfDualAt {σ : E →ₐ[F] E} {B : Base F E} (hB : B.IsGood σ) {n r s : ℕ} {X : Spc F E n}
    (hX : X.IsSkew σ B r s) (hw : Formalism.UG.IsInertAt F E v w) (h : w.under (𝓞 F) = v) {d : 𝓞 E} (hd : d ∉ w.asIdeal) :
    ((d : E)⁻¹ • X.Jᵀ).det ≠ 0 ∧ IsSelfDualAt σ ((d : E)⁻¹ • X.Jᵀ) X.L v := by
  have hd0 : (d : E) ≠ 0 := by
    intro h0
    apply hd
    have hd' : d = 0 := by exact_mod_cast h0
    rw [hd']
    exact w.asIdeal.zero_mem
  have hdet : ((d : E)⁻¹ • X.Jᵀ).det ≠ 0 := by
    rw [Matrix.det_smul, Matrix.det_transpose]
    exact mul_ne_zero (pow_ne_zero _ (inv_ne_zero hd0)) (det_ne_zero hX)
  refine ⟨hdet, ?_⟩
  unfold GlobalTheory.AdelicU.IsSelfDualAt
  rw [← SelfDual.latLoc_dualGlob hdet hX.lat v]
  obtain ⟨t, ht, htw⟩ := exists_mem_different hB hw h
  apply le_antisymm
  · refine latLoc_le hw h (t := d * t) ?_ ?_
    · intro hm
      rcases w.isPrime.mem_or_mem hm with h1 | h1
      · exact hd h1
      · exact htw h1
    · intro y hy
      rw [SelfDual.mem_dualGlob]
      intro x hx
      rw [hE_smul_transpose, form_smul_left_divisor]
      have hf : (t : E) * form σ X.J y x ∈ (algebraMap (𝓞 E) E).range :=
        mul_mem_range_of_trace ht (fun o => (hX.dual y).1 hy x hx o)
      have he : (d : E)⁻¹ * (((d * t : 𝓞 E) : E) * form σ X.J y x) = (t : E) * form σ X.J y x := by
        push_cast
        rw [← mul_assoc, ← mul_assoc, inv_mul_cancel₀ hd0, one_mul]
      rw [he]
      exact hf
  · refine latLoc_le hw h (t := 1) ?_ ?_
    · intro h1
      exact w.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h1)
    · intro y hy
      rw [one_smul]
      rw [SelfDual.mem_dualGlob] at hy
      refine (hX.dual y).2 fun x hx o => ?_
      have h1 := hy x hx
      rw [hE_smul_transpose] at h1
      obtain ⟨e, he⟩ := h1
      have hf : form σ X.J y x = (d : E) * algebraMap (𝓞 E) E e := by
        rw [he, ← mul_assoc, mul_inv_cancel₀ hd0, one_mul]
      rw [hf]
      have hi : IsIntegral ℤ ((o : E) * ((d : E) * algebraMap (𝓞 E) E e)) :=
        (RingOfIntegers.isIntegral_coe o).mul ((RingOfIntegers.isIntegral_coe d).mul (RingOfIntegers.isIntegral_coe e))
      exact Algebra.isIntegral_trace hi

theorem exists_frame_skew {σ : E →ₐ[F] E} {B : Base F E} (hB : B.IsGood σ) {n r s : ℕ} {X : Spc F E n}
    (hX : X.IsSkew σ B r s) (hw : Formalism.UG.IsInertAt F E v w) (h : w.under (𝓞 F) = v)
    {c : w.adicCompletion E →+* w.adicCompletion E} (hc : IsConjAt σ h c) :
    ∃ (δ : w.adicCompletion E) (Bm : GL (Fin n) (w.adicCompletion E)), Valued.v δ = 1 ∧ c δ = -δ ∧
      IsFrameAt w X.L Bm ∧
      (Bm : Matrix (Fin n) (Fin n) (w.adicCompletion E))ᵀ * X.J.map (algebraMap E (w.adicCompletion E)) *
        (Bm : Matrix (Fin n) (Fin n) (w.adicCompletion E)).map c = δ • 1 := by
  have hcm := hB.cm
  obtain ⟨x, hx⟩ := GlobalTheory.LFun.InertChart.exists_conj_sub_unit hcm hw
  have hxi : IsIntegral ℤ (σ (x : E) - (x : E)) :=
    (map_isIntegral_int (σ : E →+* E) (RingOfIntegers.isIntegral_coe x)).sub (RingOfIntegers.isIntegral_coe x)
  let d : 𝓞 E := ⟨σ (x : E) - (x : E), hxi⟩
  have hdE : (d : E) = σ (x : E) - (x : E) := rfl
  have hd : d ∉ w.asIdeal := (IsDedekindDomain.HeightOneSpectrum.valuation_eq_one_iff_notMem (K := E) w).1 hx
  obtain ⟨hdet, hs⟩ := isSelfDualAt hB hX hw h hd
  have hσd : σ (d : E) = -(d : E) := by
    rw [hdE, map_sub, GlobalTheory.LFun.InertChart.conj_conj hcm]
    ring
  have hd0 : (d : E) ≠ 0 := by
    intro h0
    apply hd
    have hd' : d = 0 := by exact_mod_cast h0
    rw [hd']
    exact w.asIdeal.zero_mem
  have hherm : IsHermND σ ((d : E)⁻¹ • X.Jᵀ) := by
    refine ⟨fun i j => ?_, hdet⟩
    simp only [Matrix.smul_apply, Matrix.transpose_apply, smul_eq_mul, map_mul, map_inv₀, hσd, hX.skew j i]
    rw [inv_neg]
    ring
  obtain ⟨a, ha, haJ⟩ := GlobalTheory.LFun.InertChart.exists_frame_antiJ hcm hherm hX.lat.fg hX.lat.span_eq_top hw hc hs
  obtain ⟨ϖ, hU⟩ := GlobalTheory.LFun.InertChart.exists_isUnramInv hcm hw hc
  obtain ⟨k, hk, hk1⟩ := GlobalTheory.LFun.InertChart.exists_congr_antiJ hU (B := 1) (one_mem _) (by
    unfold Formalism.UG.cT
    simp)
  set δ := algebraMap E (w.adicCompletion E) (d : E) with hδ
  have hδ0 : δ ≠ 0 := by
    rw [hδ]
    exact (map_ne_zero _).2 hd0
  set Jw := X.J.map (algebraMap E (w.adicCompletion E)) with hJw
  have e1 : (a.1.map c)ᵀ * Jwᵀ * a.1 = δ • ((k.1.map c)ᵀ * k.1) := by
    have h2 := haJ.trans hk1.symm
    unfold Formalism.UG.cT at h2
    have hKm : ((d : E)⁻¹ • X.Jᵀ).map (algebraMap E (w.adicCompletion E)) = δ⁻¹ • Jwᵀ := by
      ext i j
      simp [hδ, hJw, map_inv₀]
    rw [hKm, Matrix.mul_smul, Matrix.smul_mul] at h2
    have h2' : δ⁻¹ • ((a.1.map c)ᵀ * Jwᵀ * a.1) = (k.1.map c)ᵀ * k.1 := by simpa using h2
    rw [← h2', smul_smul, mul_inv_cancel₀ hδ0, one_smul]
  have e2 : a.1ᵀ * Jw * a.1.map c = δ • (k.1ᵀ * k.1.map c) := by
    have h3 := congrArg Matrix.transpose e1
    simpa only [Matrix.transpose_mul, Matrix.transpose_smul, Matrix.transpose_transpose, Matrix.mul_assoc] using h3
  have hkk : k.1 * (k⁻¹).1 = 1 := by
    rw [← Matrix.GeneralLinearGroup.coe_mul, mul_inv_cancel]
    rfl
  refine ⟨δ, a * k⁻¹, ?_, ?_, (GlobalTheory.LFun.InertChart.isFrameAt_mul ha (inv_mem hk)).1, ?_⟩
  · exact (IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (v := w) (d : E)).trans hx
  · rw [hδ, GlobalTheory.LFun.InertChart.conj_algebraMap hc, hσd, map_neg]
  · rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.transpose_mul, Matrix.map_mul]
    calc (k⁻¹).1ᵀ * a.1ᵀ * Jw * (a.1.map c * (k⁻¹).1.map c)
        = (k⁻¹).1ᵀ * (a.1ᵀ * Jw * a.1.map c) * (k⁻¹).1.map c := by
          simp only [Matrix.mul_assoc]
      _ = δ • ((k.1 * (k⁻¹).1)ᵀ * (k.1 * (k⁻¹).1).map c) := by
          rw [e2, Matrix.mul_smul, Matrix.smul_mul, Matrix.transpose_mul, Matrix.map_mul]
          simp only [Matrix.mul_assoc]
      _ = δ • 1 := by
          rw [hkk]
          simp

theorem exists_inertPlace_seesawW_scalar_frame : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a'), B.IsGood σ → G.IsGood B → ∀ (v : Pl F) (w : HeightOneSpectrum (𝓞 E)),
    Formalism.UG.IsInertAt F E v w → ∀ (h : w.under (𝓞 F) = v) (σL : w.adicCompletion E →+* w.adicCompletion E), IsConjAt σ h σL →
    ∃ (δ : w.adicCompletion E) (Bm : GL (Fin (a + a')) (w.adicCompletion E)), Valued.v δ = 1 ∧ σL δ = -δ ∧
      IsFrameAt w G.W.L Bm ∧
      (Bm : Matrix (Fin (a + a')) (Fin (a + a')) (w.adicCompletion E))ᵀ * G.W.J.map (algebraMap E (w.adicCompletion E)) *
        (Bm : Matrix (Fin (a + a')) (Fin (a + a')) (w.adicCompletion E)).map σL = δ • 1 := by
  intro F E _ _ _ _ _ σ B a a' G hB hG v w hw h σL hc
  exact exists_frame_skew hB hG.hW hw h hc

end GlobalTheory.SkewFrameInert

end
