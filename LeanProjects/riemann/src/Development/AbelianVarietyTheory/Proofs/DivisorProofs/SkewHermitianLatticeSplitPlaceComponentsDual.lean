import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndicatorIntMMemSB
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Definitions.Foundations.GLintEqKOAndPrincEqKOne
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDualFamilyOfIsLattice
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorLatticeInertPlaceSelfDual
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DifferentCoprimeAtGoodPlaces
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FormallyUnramifiedRingOfIntegersIffDifferentIdea
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceDualRingOfIntegersIffOfUnramifiedExtensionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalGeneratorOfNonzeroIdealStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemLocalLatticeIdealMapSmulIffGeneratorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdealMapSmulIsLatticeOfNeBotStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.KSplit
open scoped Matrix TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.SkewSplitDual

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem hE_transpose (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (x y : Fin n → E) :
    hE σ Jᵀ x y = form σ J y x := by
  simp only [hE, Formalism.UG.hform, form, dotProduct, Matrix.mulVec, Matrix.transpose_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  simp only [AlgHom.coe_toRingHom]
  ring

theorem form_add_right (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (y x x' : Fin n → E) :
    form σ J y (x + x') = form σ J y x + form σ J y x' := by
  have : (fun i => σ ((x + x') i)) = (fun i => σ (x i)) + fun i => σ (x' i) := funext fun i => by simp
  simp only [form, this, Matrix.mulVec_add, dotProduct_add]

theorem form_smul_right (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (c : E) (y x : Fin n → E) :
    form σ J y (c • x) = σ c * form σ J y x := by
  have : (fun i => σ ((c • x) i)) = σ c • fun i => σ (x i) := funext fun i => by simp
  simp only [form, this, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]

theorem isIntegral_iff_mem_range (e : E) : IsIntegral ℤ e ↔ e ∈ (algebraMap (𝓞 E) E).range :=
  ⟨fun h => ⟨⟨e, h⟩, rfl⟩, fun ⟨r, hr⟩ => hr ▸ r.isIntegral_coe⟩

theorem coe_algebraMap_int (d : 𝓞 F) : ((algebraMap (𝓞 F) (𝓞 E) d : 𝓞 E) : E) = algebraMap F E (d : F) := rfl

theorem eq_dualGlob {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {L : Submodule (𝓞 E) (Fin n → E)}
    (hu : Algebra.Unramified (𝓞 F) (𝓞 E))
    (hdual : ∀ y, y ∈ L ↔ ∀ x ∈ L, ∀ o : 𝓞 E, IsIntegral ℤ (Algebra.trace ℚ E (o * form σ J y x))) :
    L = SelfDual.dualGlob σ Jᵀ ((differentIdeal ℤ (𝓞 F)).map (algebraMap (𝓞 F) (𝓞 E)) • L) := by
  ext y
  rw [SelfDual.mem_dualGlob]
  simp only [hE_transpose]
  constructor
  · intro hy x hx
    refine Submodule.smul_induction_on hx (fun i hi x hx => ?_) (fun a b ha hb => ?_)
    · have key := (GlobalTheory.T.traceDual_ringOfIntegers_iff_of_unramified_extension F E hu (form σ J y x)).1 ((hdual y).1 hy x hx)
      have e1 : i • x = (i : E) • x := by ext j; rfl
      rw [e1, form_smul_right]
      have hi' : i ∈ Ideal.span (algebraMap (𝓞 F) (𝓞 E) '' (differentIdeal ℤ (𝓞 F) : Set (𝓞 F))) := hi
      refine Submodule.span_induction
        (p := fun (i : 𝓞 E) _ => σ (i : E) * form σ J y x ∈ (algebraMap (𝓞 E) E).range) ?_ ?_ ?_ ?_ hi'
      · rintro _ ⟨d, hd, rfl⟩
        rw [coe_algebraMap_int, AlgHom.commutes, ← isIntegral_iff_mem_range]
        exact key d hd
      · simp
      · intro a b _ _ ha hb
        simp only [Subalgebra.coe_add, map_add, add_mul]
        exact add_mem ha hb
      · intro c a _ ha
        have e2 : σ ((c • a : 𝓞 E) : E) * form σ J y x = σ (c : E) * (σ (a : E) * form σ J y x) := by
          rw [← mul_assoc, ← map_mul]; rfl
        rw [e2]
        exact mul_mem ((isIntegral_iff_mem_range _).1
          ((isIntegral_algHom_iff ((σ : E →+* E).toIntAlgHom) σ.injective).2 c.isIntegral_coe)) ha
    · rw [form_add_right]; exact add_mem ha hb
  · intro hy
    rw [hdual y]
    intro x hx o
    refine (GlobalTheory.T.traceDual_ringOfIntegers_iff_of_unramified_extension F E hu (form σ J y x)).2 (fun d hd => ?_) o
    have hmem : (algebraMap (𝓞 F) (𝓞 E) d) • x ∈ (differentIdeal ℤ (𝓞 F)).map (algebraMap (𝓞 F) (𝓞 E)) • L :=
      Submodule.smul_mem_smul (Ideal.mem_map_of_mem _ hd) hx
    have h2 := hy _ hmem
    have e1 : (algebraMap (𝓞 F) (𝓞 E) d) • x = ((algebraMap (𝓞 F) (𝓞 E) d : 𝓞 E) : E) • x := by ext j; rfl
    rw [e1, form_smul_right, coe_algebraMap_int, AlgHom.commutes] at h2
    exact (isIntegral_iff_mem_range _).2 h2

theorem mem_splitLat_comp_iff_skew {σ : E →ₐ[F] E} (hcm : IsCMExt F E σ) {n : ℕ} {J : Matrix (Fin n) (Fin n) E}
    (hskew : ∀ i j, σ (J j i) = -J i j) {L L₁ : Submodule (𝓞 E) (Fin n → E)} {v : HeightOneSpectrum (𝓞 F)}
    (t : E →ₐ[F] Fv F v) (z : Fv F v)
    (hloc : latLoc F L v = dualLoc σ Jᵀ L₁ v)
    (h1 : ∀ y, y ∈ latLoc F L₁ v ↔ ∃ x ∈ latLoc F L v, y = z • x) (u' : Fin n → Fv F v) :
    u' ∈ splitLat (t.comp σ) L ↔ ∀ u ∈ splitLat t L, z * (u ⬝ᵥ J.map t *ᵥ u') ∈ v.adicCompletionIntegers F := by
  have hJ : Jᵀ.map (t.comp σ) = -J.map t := by
    ext i j; simp [Matrix.transpose_apply, hskew]
  rw [← splitIncl_mem_latLoc_iff hcm, hloc]
  change (∀ x ∈ latLoc F L₁ v, hLin σ Jᵀ (Fv F v) (splitIncl hcm (t.comp σ) u') x ∈ intLoc F E v) ↔ _
  have hc : ∀ x, hLin σ Jᵀ (Fv F v) (splitIncl hcm (t.comp σ) u') x ∈ intLoc F E v ↔
      splitVec t x ⬝ᵥ J.map t *ᵥ u' ∈ v.adicCompletionIntegers F := by
    intro x
    rw [mem_intLoc_iff_split hcm t, splitProj_hLin, splitProj_hLin, comp_conj_conj hcm, splitVec_splitIncl_comp,
      splitVec_splitIncl, hJ, Matrix.mulVec_zero, dotProduct_zero, Matrix.neg_mulVec, dotProduct_neg, neg_mem_iff]
    exact and_iff_right (zero_mem _)
  simp only [hc]
  have hsv : ∀ x : Fin n → Fv F v ⊗[F] E, splitVec t (z • x) = z • splitVec t x := fun x =>
    funext fun i => map_smul (splitProj t) z (x i)
  constructor
  · rintro H _ ⟨x, hx, rfl⟩
    have := H (z • x) ((h1 _).2 ⟨x, hx, rfl⟩)
    rwa [hsv, smul_dotProduct, smul_eq_mul] at this
  · intro H y hy
    obtain ⟨x, hx, rfl⟩ := (h1 y).1 hy
    rw [hsv, smul_dotProduct, smul_eq_mul]
    exact H _ ⟨x, hx, rfl⟩

theorem skewSplitDual : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (d : ℕ) (W : Spc F E d) (r s : ℕ), B.IsGood σ → W.IsSkew σ B r s →
    ∀ (v : Pl F) (t : E →ₐ[F] Fv F v) (c : GL (Fin d) (Fv F v)), IsSplitBasis t W.L c →
    ∃ (z : (Fv F v)ˣ) (c₂ : GL (Fin d) (Fv F v)), (PsiUnr B.ψ v → z = 1) ∧
      (c₂⁻¹).1 = (z : Fv F v) • (c.1ᵀ * W.J.map t) ∧ IsSplitBasis (t.comp σ) W.L c₂ := by
  intro F E _ _ _ _ _ σ B d W r s hB hW v t c hc
  haveI := hB.unram
  have hcm : IsCMExt F E σ := hB.cm
  have h𝔡0 : differentIdeal ℤ (𝓞 F) ≠ ⊥ := differentIdeal_ne_bot
  have hdet : W.J.det ≠ 0 := GlobalTheory.InertSelfDual.det_ne_zero_of_skew σ B hW
  have hdetT : W.Jᵀ.det ≠ 0 := by rw [Matrix.det_transpose]; exact hdet
  have hglob := eq_dualGlob (σ := σ) (J := W.J) (L := W.L) hB.unram hW.dual
  have hloc : latLoc F W.L v =
      dualLoc σ W.Jᵀ ((differentIdeal ℤ (𝓞 F)).map (algebraMap (𝓞 F) (𝓞 E)) • W.L) v :=
    (congrArg (fun L => latLoc F L v) hglob).trans
      (SelfDual.latLoc_dualGlob hdetT (GlobalTheory.T.ideal_map_smul_isLattice_of_ne_bot F E d W.L _ h𝔡0 hW.lat) v)
  obtain ⟨z, hz0, hz1, hzle, hzeq⟩ := GlobalTheory.T.exists_local_generator_of_nonzero_ideal F (differentIdeal ℤ (𝓞 F)) v h𝔡0
  have key := mem_splitLat_comp_iff_skew hcm hW.skew t z hloc (GlobalTheory.T.mem_localLattice_idealMap_smul_iff_generator F E d W.L _ v z hzle hzeq)
  set M : Matrix (Fin d) (Fin d) (Fv F v) := z • (c.1ᵀ * W.J.map t) with hM
  have hMdet : M.det ≠ 0 := by
    rw [hM, Matrix.det_smul, Matrix.det_mul, Matrix.det_transpose]
    refine mul_ne_zero (pow_ne_zero _ hz0) (mul_ne_zero (c.isUnit.map Matrix.detMonoidHom).ne_zero ?_)
    rw [← AlgHom.mapMatrix_apply, ← AlgHom.map_det]; exact (map_ne_zero t).2 hdet
  obtain ⟨g, hg⟩ : ∃ g : GL (Fin d) (Fv F v), g.1 = M :=
    ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero M hMdet, rfl⟩
  refine ⟨Units.mk0 z hz0, g⁻¹, fun hp => Units.ext ?_, ?_, ?_⟩
  · simpa using hz1 (GlobalTheory.DiffCoprimeP.not_le_differentIdeal_of_psiUnr hB.std v hp)
  · rw [inv_inv, hg]; rfl
  · have hMc : M * (g⁻¹).1 = 1 := by rw [← hg]; exact g.mul_inv
    have hid : ∀ (w a : Fin d → Fv F v), z * ((c.1 *ᵥ a) ⬝ᵥ W.J.map t *ᵥ ((g⁻¹).1 *ᵥ w)) = a ⬝ᵥ w := by
      intro w a
      have e1 : z * ((c.1 *ᵥ a) ⬝ᵥ W.J.map t *ᵥ ((g⁻¹).1 *ᵥ w)) = a ⬝ᵥ ((M * (g⁻¹).1) *ᵥ w) := by
        rw [hM, ← Matrix.mulVec_mulVec, Matrix.smul_mulVec, ← Matrix.mulVec_mulVec, dotProduct_smul,
          smul_eq_mul]
        congr 1
        generalize W.J.map t *ᵥ ((g⁻¹).1 *ᵥ w) = X
        simp only [dotProduct, Matrix.mulVec, Matrix.transpose_apply, Finset.sum_mul, Finset.mul_sum]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
      rw [e1, hMc, Matrix.one_mulVec]
    intro w
    rw [key]
    constructor
    · intro hw u hu
      have hu' := hc.mem_iff.1 hu
      have e : u = c.1 *ᵥ ((c⁻¹).1 *ᵥ u) := by rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
      rw [e, hid]
      simp only [dotProduct]
      exact sum_mem fun i _ => mul_mem (hu' i) (hw i)
    · intro H i
      have hs : ∀ j, (Pi.single i (1 : Fv F v) : Fin d → Fv F v) j ∈ v.adicCompletionIntegers F := fun j => by
        by_cases e : j = i
        · subst e; simp
        · simp [e]
      have := H _ ((hc _).1 hs)
      rwa [hid, single_dotProduct, one_mul] at this

end GlobalTheory.SkewSplitDual

end
