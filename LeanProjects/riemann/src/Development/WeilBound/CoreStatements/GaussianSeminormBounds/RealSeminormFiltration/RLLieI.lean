import Mathlib
import Development.WeilBound.CoreStatements.GaussianSeminormBounds.RealSeminormFiltration.RLLieE

noncomputable section

open scoped TensorProduct Matrix Classical Real SchwartzMap
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift Complex MeasureTheory

namespace PositivityTheory.RL.Up

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

theorem box_SB {g g' : (κ → Af F) → ℂ} (hg : g ∈ SB (κ → Af F)) (hg' : g' ∈ SB (κ → Af F)) :
    boxFun g g' ∈ SB (κ ⊕ κ → Af F) := by
  have := GlobalTheory.AdelicUnitaryTop.t2Space_finiteAdeleRing_of_numberField F
  refine ⟨(hg.1.comp_continuous (f := fun x : κ ⊕ κ → Af F => x ∘ Sum.inl) (by fun_prop)).mul
    (hg'.1.comp_continuous (f := fun x : κ ⊕ κ → Af F => x ∘ Sum.inr) (by fun_prop)), ?_⟩
  refine HasCompactSupport.intro ((hg.2.prod hg'.2).image
    (Homeomorph.sumArrowHomeomorphProdArrow (ι := κ) (ι' := κ) (X := Af F)).symm.continuous) fun x hx => ?_
  by_contra h
  obtain ⟨h1, h2⟩ := mul_ne_zero_iff.1 h
  exact hx ⟨(x ∘ Sum.inl, x ∘ Sum.inr), ⟨subset_tsupport _ h1, subset_tsupport _ h2⟩, Sum.elim_comp_inl_inr x⟩

variable (F κ) in
theorem exists_box : ∃ (f : SInf F κ) (B : SInf F (κ ⊕ κ)) (r : (κ → mixedEmbedding.mixedSpace F) → ℝ),
    (∀ x, B x = f (x ∘ Sum.inl) * f (x ∘ Sum.inr)) ∧ (∀ x, f x = r x) ∧ Continuous r ∧ HasCompactSupport r ∧ r 0 = 1 := by
  let b : ContDiffBump (0 : κ → mixedEmbedding.mixedSpace F) := ⟨1, 2, by norm_num, by norm_num⟩
  have h1 : HasCompactSupport fun x => ((b x : ℝ) : ℂ) := b.hasCompactSupport.comp_left (g := fun r : ℝ => (r : ℂ)) rfl
  have h2 : ContDiff ℝ (⊤ : ℕ∞) fun x => ((b x : ℝ) : ℂ) := ofRealCLM.contDiff.comp b.contDiff
  have h3 : HasCompactSupport fun x : κ ⊕ κ → mixedEmbedding.mixedSpace F =>
      ((b (x ∘ Sum.inl) : ℝ) : ℂ) * ((b (x ∘ Sum.inr) : ℝ) : ℂ) := by
    refine HasCompactSupport.intro ((h1.prod h1).image
      (Homeomorph.sumArrowHomeomorphProdArrow (ι := κ) (ι' := κ) (X := mixedEmbedding.mixedSpace F)).symm.continuous)
      fun x hx => ?_
    by_contra h
    obtain ⟨h1, h2⟩ := mul_ne_zero_iff.1 h
    exact hx ⟨(x ∘ Sum.inl, x ∘ Sum.inr), ⟨subset_tsupport _ h1, subset_tsupport _ h2⟩, Sum.elim_comp_inl_inr x⟩
  exact ⟨h1.toSchwartzMap h2, h3.toSchwartzMap ((h2.comp (contDiff_pi.2 fun i => contDiff_apply ℝ _ (Sum.inl i))).mul
    (h2.comp (contDiff_pi.2 fun i => contDiff_apply ℝ _ (Sum.inr i)))), b, fun _ => rfl, fun _ => rfl, b.continuous,
    b.hasCompactSupport, b.one_of_mem_closedBall (Metric.mem_closedBall_self b.rIn_pos.le)⟩

variable (F κ) in
theorem exists_form (ψ : AddChar (AF F) ℂ) : ∃ l ∈ (adeleClass F).adm (κ ⊕ κ),
    (∀ x y : κ → AF F, ∀ φ ∈ schA F (κ ⊕ κ), l (schr ψ (Sum.elim x x, Sum.elim y (-y)) φ) = l φ) ∧
      ∃ (B : SInf F (κ ⊕ κ)), ∃ G ∈ SB (κ ⊕ κ → Af F), l (pureA F B G) ≠ 0 := by
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_finiteAdeleRing_of_numberField F
  haveI := GlobalTheory.AdelicUnitaryTop.locallyCompact_finiteAdele F
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_finiteAdele F
  borelize (κ → Af F)
  let X := κ → mixedEmbedding.mixedSpace F
  borelize X
  let μ : Measure X := Measure.addHaar
  let ν : Measure (κ → Af F) := Measure.addHaar
  haveI : MeasurableAdd X := ContinuousAdd.measurableAdd
  haveI : MeasurableAdd (κ → Af F) := ContinuousAdd.measurableAdd
  haveI : (μ.prod ν).IsAddHaarMeasure := Measure.prod.instIsAddHaarMeasure μ ν
  let k : ((κ ⊕ κ → AF F) → ℂ) →ₗ[ℂ] (X × (κ → Af F) → ℂ) :=
    LinearMap.funLeft ℂ ℂ fun p => Sum.elim (SeminormBoundRestriction.pt p.1 p.2) (SeminormBoundRestriction.pt p.1 p.2)
  let N : Submodule ℂ ((κ ⊕ κ → AF F) → ℂ) :=
    { carrier := {φ | Integrable (k φ) (μ.prod ν)}
      zero_mem' := integrable_zero _ _ _
      add_mem' := fun ha hb => ha.add hb
      smul_mem' := fun c _ h => h.smul c }
  let l0 : N →ₗ[ℂ] ℂ :=
    { toFun := fun φ => ∫ p, k φ p ∂(μ.prod ν)
      map_add' := fun a b => integral_add a.2 b.2
      map_smul' := fun c a => integral_smul c _ }
  obtain ⟨l, hl⟩ := l0.exists_extend
  have hl' : ∀ φ ∈ N, l φ = ∫ p, k φ p ∂(μ.prod ν) := fun φ h => LinearMap.congr_fun hl ⟨φ, h⟩
  let dg : X →L[ℝ] (κ ⊕ κ → mixedEmbedding.mixedSpace F) :=
    ContinuousLinearMap.pi fun i => ContinuousLinearMap.proj (Sum.elim id id i)
  have hdg : AntilipschitzWith 1 dg := AddMonoidHomClass.antilipschitz_of_bound dg fun x => by
    rw [NNReal.coe_one, one_mul]
    exact (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => norm_le_pi_norm (dg x) (Sum.inl i)
  let Rs : SInf F (κ ⊕ κ) →L[ℂ] 𝓢(X, ℂ) := SchwartzMap.compCLMOfAntilipschitz ℂ dg.hasTemperateGrowth hdg
  have hk : ∀ (B : SInf F (κ ⊕ κ)) (G : (κ ⊕ κ → Af F) → ℂ),
      k (pureA F B G) = fun p => Rs B p.1 * G (Sum.elim p.2 p.2) := fun B G => by
    funext p
    refine congrArg₂ (· * ·) (congrArg B (funext fun i => ?_)) (congrArg G (funext fun i => ?_))
    · rcases i with i | i <;> exact RingEquiv.apply_symm_apply _ _
    · rcases i with i | i <;> rfl
  have hc : Continuous fun b : κ → Af F => (Sum.elim b b : κ ⊕ κ → Af F) :=
    continuous_pi fun i => by rcases i with i | i <;> exact continuous_apply i
  have hG : ∀ G ∈ SB (κ ⊕ κ → Af F), Integrable (fun b : κ → Af F => G (Sum.elim b b)) ν := fun G hG =>
    (hG.1.continuous.comp hc).integrable_of_hasCompactSupport (hG.2.comp_isClosedEmbedding
      (Function.LeftInverse.isClosedEmbedding (f := fun x : κ ⊕ κ → Af F => x ∘ Sum.inl) (fun _ => rfl) (by fun_prop) hc))
  have hp : ∀ (B : SInf F (κ ⊕ κ)), ∀ G ∈ SB (κ ⊕ κ → Af F), pureA F B G ∈ N := fun B G h => by
    show Integrable (k _) _
    rw [hk]
    exact (Rs B).integrable.mul_prod (hG G h)
  have hv : ∀ (B : SInf F (κ ⊕ κ)), ∀ G ∈ SB (κ ⊕ κ → Af F),
      l (pureA F B G) = (∫ a, Rs B a ∂μ) * ∫ b, G (Sum.elim b b) ∂ν := fun B G h => by
    rw [hl' _ (hp B G h), hk]
    exact integral_prod_mul (Rs B) fun b => G (Sum.elim b b)
  refine ⟨l, fun G h => ⟨(∫ b, G (Sum.elim b b) ∂ν) • (SchwartzMap.integralCLM ℂ μ ∘L Rs), fun B => ?_⟩,
    fun x y φ hφ => ?_, ?_⟩
  · rw [hv B G h, mul_comm]
    rfl
  · have hN : φ ∈ N := (Submodule.span_le.2 (by rintro _ ⟨B, G, h, rfl⟩; exact hp B G h) : schA F (κ ⊕ κ) ≤ N) hφ
    let c : X × (κ → Af F) := (fun i => evI F (x i), fun i => (x i).2)
    have e : k (schr ψ (Sum.elim x x, Sum.elim y (-y)) φ) = fun p => k φ (c + p) := by
      funext p
      have e1 : SeminormBoundRestriction.pt (c + p).1 (c + p).2 = SeminormBoundRestriction.pt p.1 p.2 + x := funext fun i =>
        Prod.ext (((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm.map_add _ _).trans ((add_comm _ _).trans
          (congrArg (_ + ·) (RingEquiv.symm_apply_apply _ _)))) (add_comm _ _)
      show schr _ _ _ (Sum.elim (SeminormBoundRestriction.pt p.1 p.2) (SeminormBoundRestriction.pt p.1 p.2)) =
        φ (Sum.elim (SeminormBoundRestriction.pt (c + p).1 (c + p).2) (SeminormBoundRestriction.pt (c + p).1 (c + p).2))
      rw [e1, schr, sumElim_dotProduct_sumElim, sumElim_dotProduct_sumElim]
      simp only [dotProduct_neg, add_neg_cancel, mul_zero, add_zero, AddChar.map_zero_eq_one, one_mul]
      congr 1
      funext i
      rcases i with i | i <;> rfl
    rw [hl' _ hN, hl' _ (by
      show Integrable (k _) _
      rw [e]
      exact (show Integrable (k φ) (μ.prod ν) from hN).comp_add_left c), e]
    exact integral_add_left_eq_self (k φ) c
  · obtain ⟨f, B, r, hB, hf, hr, hr', hr0⟩ := exists_box F κ
    obtain ⟨g, hg, y, hy⟩ := SeminormBoundRestriction.exists_SB (F := F) (κ := κ)
    have hg' : (fun x => ((‖g x‖ : ℝ) : ℂ)) ∈ SB (κ → Af F) :=
      ⟨hg.1.comp fun z => ((‖z‖ : ℝ) : ℂ), hg.2.comp_left (g := fun z => ((‖z‖ : ℝ) : ℂ)) (by simp)⟩
    refine ⟨B, _, box_SB hg' hg', ?_⟩
    rw [hv _ _ (box_SB hg' hg')]
    refine mul_ne_zero ?_ ?_
    · have : ∀ a, Rs B a = ((r a * r a : ℝ) : ℂ) := fun a => by
        rw [ofReal_mul, ← hf]
        exact hB _
      simp only [this]
      rw [integral_complex_ofReal, ofReal_ne_zero]
      exact ((hr.mul hr).integral_pos_of_hasCompactSupport_nonneg_nonzero hr'.mul_left (fun _ => mul_self_nonneg _)
        (x := 0) (by simp [hr0])).ne'
    · have : ∀ b, boxFun (fun x => ((‖g x‖ : ℝ) : ℂ)) (fun x => ((‖g x‖ : ℝ) : ℂ)) (Sum.elim b b) =
          ((‖g b‖ * ‖g b‖ : ℝ) : ℂ) := fun b => (ofReal_mul _ _).symm
      simp only [this]
      rw [integral_complex_ofReal, ofReal_ne_zero]
      exact ((hg.1.continuous.norm.mul hg.1.continuous.norm).integral_pos_of_hasCompactSupport_nonneg_nonzero
        hg.2.norm.mul_left (fun _ => mul_self_nonneg _) (x := y) (by simp [hy])).ne'

end PositivityTheory.RL.Up

end
