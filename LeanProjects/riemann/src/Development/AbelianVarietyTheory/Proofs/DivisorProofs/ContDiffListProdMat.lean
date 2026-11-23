import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemThInt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThLiftMemLiftSpace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCuspW
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsNotIsConstTerm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeApproximationUpwardIdele
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchEmbeddingConjByAdelic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealLineContinuous
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContDiffOfPartialDerivativeClosure
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ListProdUpdateConjugate
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasureFundDomLtTopSmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryHaarRightInvariant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicUnitaryLocallyCompactHausdorff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdmissibleFormAdelicThetaSum
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
open scoped TensorProduct NNReal Matrix ContDiff
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.LiftConst GlobalTheory.ThK.SplitInv GlobalTheory.ThK.SquareIntegrability

noncomputable section

namespace GlobalTheory.ThK.LiftUnit

section Smooth

open GlobalTheory.SiegelSet GlobalTheory.UAut

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

theorem contDiff_list_prod_mat {k N : ℕ} {ι : Type} (l : List ι) (f : ι → (Fin k → ℝ) → Matrix (Fin N) (Fin N) ℂ)
    (hf : ∀ i ∈ l, ContDiff ℝ ∞ (f i)) : ContDiff ℝ ∞ fun t => (l.map fun i => f i t).prod := by
  induction l with
  | nil => simpa using contDiff_const
  | cons i l ih =>
    simp only [List.map_cons, List.prod_cons]
    exact (hf i List.mem_cons_self).mul (ih fun j hj => hf j (List.mem_cons_of_mem _ hj))

theorem smooth_of_der {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    (hcm : IsCMExt F E σ) {n : ℕ} (J' : Matrix (Fin n) (Fin n) E) {κ : Type} (S₀ : Submodule ℂ (κ → ℂ))
    (FF : (κ → ℂ) → GAd σ J' → ℂ) (hcont : ∀ Ψ ∈ S₀, Continuous (FF Ψ))
    (hsum : ∀ {ι : Type} (s : Finset ι) (a : ι → ℝ) (Ψ : ι → κ → ℂ), (∀ i ∈ s, Ψ i ∈ S₀) → ∀ x,
      FF (∑ i ∈ s, (a i : ℂ) • Ψ i) x = ∑ i ∈ s, (a i : ℂ) * FF (Ψ i) x)
    (hder : ∀ (w : InfinitePlace F) (τ : EmbOver E w), ∃ D : Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] Module.End ℂ (κ → ℂ),
      (∀ Z, ∀ Φ ∈ S₀, D Z Φ ∈ S₀) ∧ ∀ (Z : Matrix (Fin n) (Fin n) ℂ) (γ : ℝ → GAd σ J'), Continuous γ → (∀ s t, γ (s + t) = γ s * γ t) →
        (∀ t, embArch σ J' w (projArch σ J' w (γ t)) = γ t) →
        (∀ t, GlobalTheory.Orb.archMat σ J' τ (projArch σ J' w (γ t)) = NormedSpace.exp (t • Z)) →
        ∀ Φ ∈ S₀, ∀ x, HasDerivAt (fun s : ℝ => FF Φ (x * γ s)) (FF (D Z Φ) x) 0)
    {Φ : κ → ℂ} (hΦ : Φ ∈ S₀) :
    (∀ (k : ℕ) (γ : Fin k → ℝ → GAd σ J'), (∀ i, IsRealLine σ J' (γ i)) → ∀ g,
      ContDiff ℝ ∞ fun t : Fin k → ℝ => FF Φ (g * (List.ofFn fun i => γ i (t i)).prod)) ∧
    ∀ l : List (ℝ → GAd σ J'), (∀ γ ∈ l, IsRealLine σ J' γ) → ∃ Ψ ∈ S₀, l.foldr lineDer (FF Φ) = FF Ψ := by
  refine ⟨fun k γ hγ g => ?_, fun l hl => ?_⟩
  swap
  · induction l with
    | nil => exact ⟨Φ, hΦ, rfl⟩
    | cons γ l ih =>
      obtain ⟨Ψ, hΨ, e⟩ := ih fun δ hδ => hl δ (List.mem_cons_of_mem _ hδ)
      obtain ⟨w, τ, Z, -, hZ⟩ := hl γ List.mem_cons_self
      obtain ⟨D, hDP, hDd⟩ := hder w τ
      refine ⟨D Z Ψ, hDP Z Ψ hΨ, ?_⟩
      rw [List.foldr_cons, e]
      funext x
      have hγ := hl γ List.mem_cons_self
      refine (hDd Z γ (GlobalTheory.RealLineCont.continuous_of_isRealLine F E σ hcm _ J' γ hγ)
        (GlobalTheory.SiegelSet.isRealLine_add F E σ hcm _ J' γ hγ) (fun t => ?_) (fun t => ?_) Ψ hΨ x).deriv
      · obtain ⟨y, hy, -⟩ := hZ t
        rw [hy, projArch_embArch_self]
      · obtain ⟨y, hy, hy2⟩ := hZ t
        rw [hy, projArch_embArch_self, hy2]
  haveI : CompleteSpace (Matrix (Fin n) (Fin n) ℂ) := FiniteDimensional.complete ℝ _
  let P : (Fin k → ℝ) → GAd σ J' := fun t => (List.ofFn fun i => γ i (t i)).prod
  let S : Set ((Fin k → ℝ) → ℂ) := {f | ∃ Ψ ∈ S₀, f = fun t => FF Ψ (g * P t)}
  have hP : Continuous P := by
    have e : P = fun t => ((List.finRange k).map fun i => γ i (t i)).prod := by
      funext t; simp [P, List.ofFn_eq_map]
    rw [e]
    exact continuous_list_prod (f := fun (i : Fin k) (t : Fin k → ℝ) => γ i (t i)) _ fun i _ =>
      (GlobalTheory.RealLineCont.continuous_of_isRealLine F E σ hcm _ J' (γ i) (hγ i)).comp (continuous_apply i)
  refine GlobalTheory.contDiff_of_partials_in_smooth_span k S ?_ ?_ _ ⟨Φ, hΦ, rfl⟩
  · rintro f ⟨Ψ, hΨ, rfl⟩
    exact (hcont Ψ hΨ).comp (continuous_const.mul hP)
  · rintro f ⟨Ψ, hΨ, rfl⟩ j
    obtain ⟨w, τ, Z, -, hZ⟩ := hγ j
    obtain ⟨D, hDP, hDd⟩ := hder w τ
    let A : GAd σ J' →* Matrix (Fin n) (Fin n) ℂ := (GlobalTheory.Orb.archMat σ J' τ).comp (projArch σ J' w)
    let suf : (Fin k → ℝ) → GAd σ J' := fun t => (List.ofFn fun i => if j < i then γ i (t i) else 1).prod
    let Zt : (Fin k → ℝ) → Matrix (Fin n) (Fin n) ℂ := fun t => A (suf t)⁻¹ * Z * A (suf t)
    have hexp : ContDiff ℝ ∞ (NormedSpace.exp : Matrix (Fin n) (Fin n) ℂ → _) :=
      contDiff_iff_contDiffAt.2 fun x => (NormedSpace.exp_analytic (𝕂 := ℝ) x).contDiffAt
    have hA : ContDiff ℝ ∞ fun t => A (suf t) := by
      choose Zi hZi using fun i => GlobalTheory.UAut.Model.exists_exp hcm τ (hγ i)
      have e : (fun t => A (suf t)) = fun t => ((List.finRange k).map fun i =>
          (if j < i then NormedSpace.exp (t i • Zi i) else 1 : Matrix (Fin n) (Fin n) ℂ)).prod := by
        funext t
        simp only [suf, List.ofFn_eq_map, map_list_prod, List.map_map]
        congr 1
        refine List.map_congr_left fun i _ => ?_
        simp only [Function.comp_apply]
        split_ifs
        · exact hZi i (t i)
        · exact map_one A
      rw [e]
      refine contDiff_list_prod_mat _ _ fun i _ => ?_
      by_cases h : j < i
      · simp only [h, if_true]
        exact hexp.comp ((contDiff_apply ℝ ℝ i).smul contDiff_const)
      · simp only [h, if_false]
        exact contDiff_const
    have hinv : ∀ t, A (suf t)⁻¹ = Ring.inverse (A (suf t)) := fun t => by
      rw [← MonoidHom.coe_toHomUnits A (suf t), Ring.inverse_unit, ← map_inv, MonoidHom.coe_toHomUnits]
    have hAi : ContDiff ℝ ∞ fun t => A (suf t)⁻¹ := by
      simp only [hinv]
      refine contDiff_iff_contDiffAt.2 fun t => ?_
      have h1 := contDiffAt_ringInverse ℝ (n := ∞) (A.toHomUnits (suf t))
      rw [MonoidHom.coe_toHomUnits] at h1
      exact h1.comp t hA.contDiffAt
    have hZt : ContDiff ℝ ∞ Zt := (hAi.mul contDiff_const).mul hA
    let bm : Fin n × Fin n × Bool → Matrix (Fin n) (Fin n) ℂ :=
      fun x => Matrix.single x.1 x.2.1 (if x.2.2 then Complex.I else 1)
    let cf : Fin n × Fin n × Bool → (Fin k → ℝ) → ℝ :=
      fun x t => if x.2.2 then (Zt t x.1 x.2.1).im else (Zt t x.1 x.2.1).re
    have hcf : ∀ x, ContDiff ℝ ∞ fun t => ((cf x t : ℝ) : ℂ) := by
      intro x
      have he : ContDiff ℝ ∞ fun t => Zt t x.1 x.2.1 :=
        (LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℝ ℂ x.1 x.2.1)).contDiff.comp hZt
      rcases x with ⟨p, q, b⟩
      cases b
      · exact Complex.ofRealCLM.contDiff.comp (Complex.reCLM.contDiff.comp he)
      · exact Complex.ofRealCLM.contDiff.comp (Complex.imCLM.contDiff.comp he)
    have hZe : ∀ t, Zt t = ∑ x, cf x t • bm x := by
      intro t
      ext p q
      simp only [Matrix.sum_apply, Fintype.sum_prod_type, Fintype.sum_bool, Matrix.smul_apply, bm, cf,
        Matrix.single_apply, if_true, Bool.false_eq_true, if_false]
      simp [Finset.sum_add_distrib, Complex.real_smul, ite_and]
      conv_lhs => rw [← Complex.re_add_im (Zt t p q)]
      ring
    refine ⟨Fin n × Fin n × Bool, inferInstance, fun x t => (cf x t : ℂ),
      fun x t => FF (D (bm x) Ψ) (g * P t), hcf, fun x => ⟨_, hDP _ Ψ hΨ, rfl⟩, fun t => ?_⟩
    let γ' : ℝ → GAd σ J' := fun s => (suf t)⁻¹ * γ j s * suf t
    have hγe : ∀ s, ∃ y, γ' s = embArch σ J' w ((projArch σ J' w (suf t))⁻¹ * y * projArch σ J' w (suf t)) ∧
        GlobalTheory.Orb.archMat σ J' τ y = NormedSpace.exp (s • Z) := by
      intro s
      obtain ⟨y, hy, hy2⟩ := hZ s
      exact ⟨y, by simp only [γ']; rw [hy]; exact GlobalTheory.ConjArch.conj_embArch F E σ _ J' w y (suf t), hy2⟩
    have h1 : ∀ s, embArch σ J' w (projArch σ J' w (γ' s)) = γ' s := by
      intro s
      obtain ⟨y, hy, -⟩ := hγe s
      rw [hy, projArch_embArch_self]
    have h2 : ∀ s, GlobalTheory.Orb.archMat σ J' τ (projArch σ J' w (γ' s)) = NormedSpace.exp (s • Zt t) := by
      intro s
      obtain ⟨y, hy, hy2⟩ := hγe s
      rw [hy, projArch_embArch_self, map_mul, map_mul, hy2]
      let Ui : (Matrix (Fin n) (Fin n) ℂ)ˣ := A.toHomUnits (suf t)⁻¹
      have hU1 : (Ui : Matrix (Fin n) (Fin n) ℂ) = A (suf t)⁻¹ := MonoidHom.coe_toHomUnits _ _
      have hU2 : ((Ui⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix _ _ ℂ) = A (suf t) := by
        simp only [Ui]
        rw [← map_inv, inv_inv, MonoidHom.coe_toHomUnits]
      have e1 : s • Zt t = (Ui : Matrix _ _ ℂ) * (s • Z) * ((Ui⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix _ _ ℂ) := by
        rw [hU1, hU2]
        simp only [Zt, smul_mul_assoc, mul_smul_comm]
      rw [e1, Matrix.exp_units_conj, hU1, hU2]
      simp only [A, MonoidHom.comp_apply, map_inv]
    have hPs : ∀ s, g * P (t + s • Pi.single j 1) = g * P t * γ' s := by
      intro s
      have e1 : (fun i => γ i ((t + s • (Pi.single j 1 : Fin k → ℝ)) i)) =
          Function.update (fun i => γ i (t i)) j (γ j (t j) * γ j s) := by
        funext i
        by_cases hi : i = j
        · subst hi
          simp [GlobalTheory.SiegelSet.isRealLine_add F E σ hcm _ J' (γ i) (hγ i)]
        · simp [hi, Function.update_of_ne hi]
      simp only [P, γ', suf, e1, GlobalTheory.list_prod_ofFn_update_mul_right, mul_assoc]
    have hd := hDd (Zt t) γ' ((continuous_const.mul (GlobalTheory.RealLineCont.continuous_of_isRealLine F E σ hcm _ J' _ (hγ j))).mul
      continuous_const) (fun s u => by
        simp only [γ', GlobalTheory.SiegelSet.isRealLine_add F E σ hcm _ J' _ (hγ j)]; group) h1 h2 Ψ hΨ (g * P t)
    have hval : FF (D (Zt t) Ψ) (g * P t) =
        ∑ x, (cf x t : ℂ) * FF (D (bm x) Ψ) (g * P t) := by
      have e2 : D (Zt t) Ψ = ∑ x, (cf x t : ℂ) • D (bm x) Ψ := by
        rw [hZe t, map_sum, LinearMap.sum_apply]
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [map_smul, LinearMap.smul_apply]
        funext y
        simp [Complex.real_smul]
      rw [e2]
      exact hsum _ (fun x => cf x t) _ (fun x _ => hDP _ Ψ hΨ) _
    rw [← hval]
    refine hd.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_)
    simp only [hPs]

end Smooth

section Unit

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem unitary_of_bounded {n : ℕ} {J : Matrix (Fin n) (Fin n) E} [ContinuousMul (UA σ J)] (μ : Measure (UA σ J))
    [μ.IsHaarMeasure] [μ.IsMulRightInvariant] {𝓕 : Set (UA σ J)} (h𝓕 : IsFundamentalDomain (ratU σ J) 𝓕 μ) (hv : μ 𝓕 < ⊤)
    (G₀ : Subgroup (UA σ J)) (S : Submodule ℂ (UA σ J → ℂ))
    (hS : ∀ φ ∈ S, Continuous φ ∧ (∀ γ ∈ ratU σ J, ∀ g, φ (γ * g) = φ g) ∧ ∃ C : ℝ, ∀ g, ‖φ g‖ ≤ C) : Unitary G₀ S := by
  haveI : BorelSpace (UA σ J) := ⟨rfl⟩
  haveI := GlobalTheory.UnitaryVol.countable_ratU σ J
  haveI : MeasurableMul (UA σ J) :=
    ⟨fun g => (continuous_const.mul continuous_id).measurable, fun g => (continuous_id.mul continuous_const).measurable⟩
  haveI : MeasurableConstSMul (ratU σ J) (UA σ J) :=
    ⟨fun γ => (continuous_const.mul continuous_id : Continuous fun x : UA σ J => γ.1 * x).measurable⟩
  haveI : SMulInvariantMeasure (ratU σ J) (UA σ J) μ := ⟨fun γ A _ => measure_preimage_mul μ γ.1 A⟩
  have hint : ∀ φ ∈ S, ∀ ψ ∈ S, IntegrableOn (fun g => φ g * starRingEnd ℂ (ψ g)) 𝓕 μ := by
    intro φ hφ ψ hψ
    obtain ⟨c1, -, C, hC⟩ := hS φ hφ
    obtain ⟨c2, -, C', hC'⟩ := hS ψ hψ
    refine Measure.integrableOn_of_bounded (M := C * C') hv.ne
      (c1.mul (Complex.continuous_conj.comp c2)).aestronglyMeasurable (.of_forall fun g => ?_)
    rw [norm_mul, Complex.norm_conj]
    exact mul_le_mul (hC g) (hC' g) (norm_nonneg _) ((norm_nonneg _).trans (hC g))
  refine ⟨fun φ ψ => ∫ g in 𝓕, φ g * starRingEnd ℂ (ψ g) ∂μ, fun φ hφ ψ hψ χ hχ c => ?_, fun φ _ ψ _ => ?_,
    fun φ hφ h0 => ?_, fun φ hφ ψ hψ k _ => ?_⟩
  · beta_reduce
    rw [← integral_const_mul, ← integral_add ((hint φ hφ χ hχ).const_mul c) (hint ψ hψ χ hχ)]
    refine integral_congr_ae (.of_forall fun g => ?_)
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  · beta_reduce
    rw [← integral_conj]
    refine integral_congr_ae (.of_forall fun g => ?_)
    simp only [map_mul, Complex.conj_conj]
    ring
  · beta_reduce
    obtain ⟨c1, hl, -⟩ := hS φ hφ
    have e : (fun g => φ g * starRingEnd ℂ (φ g)) = fun g => ((Complex.normSq (φ g) : ℝ) : ℂ) :=
      funext fun g => Complex.mul_conj _
    have hi : IntegrableOn (fun g => Complex.normSq (φ g)) 𝓕 μ := by
      have h := hint φ hφ φ hφ
      rw [e] at h
      simpa [IntegrableOn] using h.re
    rw [e, integral_complex_ofReal, Complex.ofReal_re,
      integral_pos_iff_support_of_nonneg (fun g => Complex.normSq_nonneg _) hi]
    have es : (Function.support fun g => Complex.normSq (φ g)) = Function.support φ := by
      ext g; simp
    have ho : IsOpen (Function.support φ) := c1.isOpen_support
    rw [es, Measure.restrict_apply ho.measurableSet, pos_iff_ne_zero]
    intro hz
    have := h𝓕.measure_zero_of_invariant (Function.support φ) (fun γ => ?_) hz
    · exact (ho.measure_pos μ (Function.support_nonempty_iff.2 h0)).ne' this
    · ext x
      rw [Set.mem_smul_set_iff_inv_smul_mem]
      simp only [Function.mem_support]
      rw [show γ⁻¹ • x = (γ⁻¹).1 * x from rfl, hl _ (γ⁻¹).2]
  · beta_reduce
    obtain ⟨-, hl, -⟩ := hS φ hφ
    obtain ⟨-, hl', -⟩ := hS ψ hψ
    let e : UA σ J ≃ᵐ UA σ J := MeasurableEquiv.mulRight k
    have hmp : MeasurePreserving e μ μ := measurePreserving_mul_right μ k
    have h1 : ∫ g in 𝓕, rt k φ g * starRingEnd ℂ (rt k ψ g) ∂μ = ∫ g in e '' 𝓕, φ g * starRingEnd ℂ (ψ g) ∂μ :=
      (hmp.setIntegral_image_emb e.measurableEmbedding (fun g => φ g * starRingEnd ℂ (ψ g)) 𝓕).symm
    have h2 : IsFundamentalDomain (ratU σ J) (e '' 𝓕) μ :=
      h𝓕.image_of_equiv e.toEquiv (hmp.symm e).quasiMeasurePreserving (Equiv.refl _)
        (fun γ x => (mul_assoc γ.1 x k))
    rw [h1]
    exact h2.setIntegral_eq h𝓕 fun γ x => by
      rw [show γ • x = γ.1 * x from rfl, hl _ γ.2, hl' _ γ.2]

end Unit

section Lift

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem lift_reg {n m : ℕ} {J : Matrix (Fin n) (Fin n) E} {JW : Matrix (Fin m) (Fin m) E} [ContinuousMul (UA σ J)]
    {f : UA σ JW → ℂ} (hfc : Continuous f) (hdec : ∀ N : ℕ, ∃ C : ℝ, ∀ h, ‖f h‖ * (qht h : ℝ) ^ N ≤ C)
    {μ : Measure (UA σ JW)} {𝓕 : Set (UA σ JW)} (hv : μ 𝓕 < ⊤) (N : ℕ) {θ : UA σ J → UA σ JW → ℂ}
    (hθc : Continuous fun x : UA σ J × UA σ JW => θ x.1 x.2)
    (hθb : ∃ (C : ℝ) (k : ℕ), ∀ g h, ‖θ g h‖ ≤ C * (ht g : ℝ) ^ N * (qht h : ℝ) ^ k) :
    (∀ g, IntegrableOn (fun h => f h * starRingEnd ℂ (θ g h)) 𝓕 μ) ∧
    Continuous (fun g => ∫ h in 𝓕, f h * starRingEnd ℂ (θ g h) ∂μ) ∧
    (∃ C : ℝ, ∀ g, ‖∫ h in 𝓕, f h * starRingEnd ℂ (θ g h) ∂μ‖ ≤ C * (ht g : ℝ) ^ N) ∧
    ∀ (θ₀ : UA σ J → UA σ JW → ℂ) (δ : ℝ → UA σ J), Continuous δ → (∀ s t, δ (s + t) = δ s * δ t) →
      (∀ g, IntegrableOn (fun h => f h * starRingEnd ℂ (θ₀ g h)) 𝓕 μ) →
      (∀ g h, HasDerivAt (fun t : ℝ => θ₀ (g * δ t) h) (θ g h) 0) → ∀ g,
      HasDerivAt (fun t : ℝ => ∫ h in 𝓕, f h * starRingEnd ℂ (θ₀ (g * δ t) h) ∂μ) (∫ h in 𝓕, f h * starRingEnd ℂ (θ g h) ∂μ) 0 := by
  haveI : BorelSpace (UA σ JW) := ⟨rfl⟩
  obtain ⟨-, _, -⟩ := GlobalTheory.AdelicUnitaryTop.lcsc_UA F E σ n J
  haveI : FirstCountableTopology (UA σ J) := TopologicalSpace.SecondCountableTopology.to_firstCountableTopology _
  obtain ⟨C, k, hC⟩ := hθb
  obtain ⟨D, hD⟩ := hdec k
  have hht : Continuous (fun g : UA σ J => (ht g : ℝ)) :=
    NNReal.continuous_coe.comp ((GlobalTheory.Grow.continuous_heightGL F).comp continuous_subtype_val)
  have hD0 : 0 ≤ D := le_trans (by positivity) (hD 1)
  have hb : ∀ g h, ‖f h * starRingEnd ℂ (θ g h)‖ ≤ max C 0 * D * (ht g : ℝ) ^ N := fun g h => by
    rw [norm_mul, Complex.norm_conj]
    calc ‖f h‖ * ‖θ g h‖ ≤ ‖f h‖ * (max C 0 * (ht g : ℝ) ^ N * (qht h : ℝ) ^ k) := by
          refine mul_le_mul_of_nonneg_left ((hC g h).trans ?_) (norm_nonneg _)
          gcongr
          exact le_max_left _ _
      _ = max C 0 * (‖f h‖ * (qht h : ℝ) ^ k) * (ht g : ℝ) ^ N := by ring
      _ ≤ max C 0 * D * (ht g : ℝ) ^ N := by gcongr; exact hD h
  have hb' : ∀ g h (R : ℝ), (ht g : ℝ) < R → ‖f h * starRingEnd ℂ (θ g h)‖ ≤ max C 0 * D * R ^ N := fun g h R hR =>
    (hb g h).trans (by gcongr)
  have hcont : ∀ g, Continuous (fun h => f h * starRingEnd ℂ (θ g h)) :=
    fun g => hfc.mul (Complex.continuous_conj.comp (hθc.comp (continuous_const.prodMk continuous_id)))
  refine ⟨fun g => Measure.integrableOn_of_bounded hv.ne (hcont g).aestronglyMeasurable (.of_forall (hb g)), ?_,
    ⟨max C 0 * D * μ.real 𝓕, fun g => ?_⟩, fun θ₀ δ hδ hadd hint hder g => ?_⟩
  · rw [continuous_iff_continuousAt]
    intro g₀
    refine continuousAt_of_dominated (bound := fun _ => max C 0 * D * ((ht g₀ : ℝ) + 1) ^ N)
      (.of_forall fun g => (hcont g).aestronglyMeasurable) ?_ (integrableOn_const hv.ne) (.of_forall fun h => ?_)
    · filter_upwards [hht.continuousAt.eventually_lt (continuousAt_const (y := (ht g₀ : ℝ) + 1)) (lt_add_one _)] with g hg
      exact .of_forall fun h => hb' g h _ hg
    · exact (continuous_const.mul (Complex.continuous_conj.comp
        (hθc.comp (continuous_id.prodMk continuous_const)))).continuousAt
  · refine (norm_setIntegral_le_of_norm_le_const hv fun h _ => hb g h).trans (le_of_eq ?_)
    ring
  · have h0 : δ 0 = 1 := by
      have := hadd 0 0
      rw [add_zero] at this
      exact left_eq_mul.1 this
    have hc : Continuous fun t => (ht (g * δ t) : ℝ) := hht.comp (continuous_const.mul hδ)
    have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ.restrict 𝓕) (x₀ := (0 : ℝ))
      (F := fun t h => f h * starRingEnd ℂ (θ₀ (g * δ t) h)) (F' := fun t h => f h * starRingEnd ℂ (θ (g * δ t) h))
      (bound := fun _ => max C 0 * D * ((ht (g * δ 0) : ℝ) + 1) ^ N)
      (s := {t | (ht (g * δ t) : ℝ) < (ht (g * δ 0) : ℝ) + 1})
      (hc.continuousAt.eventually_lt continuousAt_const (lt_add_one _))
      (.of_forall fun t => (hint _).aestronglyMeasurable) (hint _) (hcont _).aestronglyMeasurable
      (.of_forall fun h t ht => hb' _ h _ ht) (integrableOn_const hv.ne) (.of_forall fun h t _ => ?_)
    · simpa only [h0, mul_one] using key.2
    have h1 := hder (g * δ t) h
    rw [← sub_self t] at h1
    have h2 := (HasDerivAt.comp_sub_const t t h1).congr_of_eventuallyEq (f₁ := fun u => θ₀ (g * δ u) h)
      (.of_forall fun u => by simp only [mul_assoc, ← hadd, add_sub_cancel])
    exact h2.star.const_mul (f h)

end Lift

end GlobalTheory.ThK.LiftUnit

end
