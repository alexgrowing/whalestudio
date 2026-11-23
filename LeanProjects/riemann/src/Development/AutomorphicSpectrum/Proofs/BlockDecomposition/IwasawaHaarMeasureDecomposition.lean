import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.LocalWhittakerDuality.WhittakerFunctionalEquationAdditive
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Th
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IwasawaDecompositionGlTwoHolds
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TestVectorNonvanishingLocal
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K.GL2LocalData GlobalTheory.CompanionTheory.DampedZetaMajorant
open scoped ValuativeRel

noncomputable section

namespace GlobalTheory.CompanionTheory.IwaHaar

section Abstract

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]

theorem lintegral_avg (K : Subgroup G) (ρ : Measure G) [SFinite ρ] (hρK : ∀ᵐ k ∂ρ, k ∈ K)
    (μ : Measure G) [SFinite μ] (hμ : ∀ k ∈ K, μ.map (· * k) = μ)
    {f : G → ENNReal} (hf : Measurable f) :
    ∫⁻ g, ∫⁻ k, f (g * k) ∂ρ ∂μ = ρ Set.univ * ∫⁻ g, f g ∂μ := by
  have hm : Measurable (Function.uncurry fun g k : G => f (g * k)) := hf.comp measurable_mul
  rw [lintegral_lintegral_swap hm.aemeasurable]
  have h1 : ∀ᵐ k ∂ρ, ∫⁻ g, f (g * k) ∂μ = ∫⁻ g, f g ∂μ := by
    filter_upwards [hρK] with k hk
    conv_rhs => rw [← hμ k hk]
    rw [lintegral_map hf (measurable_mul_const k)]
  rw [lintegral_congr_ae h1, lintegral_const, mul_comm]

theorem lintegral_coset (K : Subgroup G) (hK : IsOpen (K : Set G)) (μ : Measure G)
    {Q : G → ENNReal} (hQ : ∀ g, ∀ k ∈ K, Q (g * k) = Q g) :
    ∫⁻ g, Q g ∂μ = ∑' c : G ⧸ K, Q c.out * μ {h | (c.out)⁻¹ * h ∈ K} := by
  have hd : DiscreteTopology (G ⧸ K) := QuotientGroup.discreteTopology hK
  have hc : Countable (G ⧸ K) := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  have hS : ∀ c : G ⧸ K, {h | (c.out)⁻¹ * h ∈ K} = (QuotientGroup.mk : G → G ⧸ K) ⁻¹' {c} := by
    intro c
    ext h
    simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_singleton_iff]
    rw [← QuotientGroup.eq, QuotientGroup.out_eq']
    exact eq_comm
  have hmeas : ∀ c : G ⧸ K, MeasurableSet ((QuotientGroup.mk : G → G ⧸ K) ⁻¹' {c}) := fun c =>
    ((isOpen_discrete {c}).preimage QuotientGroup.continuous_mk).measurableSet
  have hU : (⋃ c : G ⧸ K, (QuotientGroup.mk : G → G ⧸ K) ⁻¹' {c}) = Set.univ := by
    ext h; simp
  have hdis : Pairwise (Function.onFun Disjoint fun c : G ⧸ K => (QuotientGroup.mk : G → G ⧸ K) ⁻¹' {c}) := by
    intro a b hab
    exact Disjoint.preimage _ (Set.disjoint_singleton.2 hab)
  rw [← setLIntegral_univ, ← hU, lintegral_iUnion hmeas hdis]
  refine tsum_congr fun c => ?_
  rw [hS c, ← setLIntegral_const]
  refine setLIntegral_congr_fun (hmeas c) fun h hh => ?_
  have e : (c.out)⁻¹ * h ∈ K := by
    have : h ∈ {h | (c.out)⁻¹ * h ∈ K} := by rw [hS c]; exact hh
    exact this
  have := hQ c.out _ e
  rw [mul_inv_cancel_left] at this
  exact this

theorem measure_eq_of_coset (K : Subgroup G) (hK : IsOpen (K : Set G)) (ρ : Measure G)
    [IsFiniteMeasure ρ] (hρ0 : ρ Set.univ ≠ 0) (hρK : ∀ᵐ k ∂ρ, k ∈ K)
    (hρ : ∀ k ∈ K, ρ.map (k * ·) = ρ)
    (μ₁ μ₂ : Measure G) [SFinite μ₁] [SFinite μ₂]
    (h₁ : ∀ k ∈ K, μ₁.map (· * k) = μ₁) (h₂ : ∀ k ∈ K, μ₂.map (· * k) = μ₂)
    (hc : ∀ g, μ₁ {h | g⁻¹ * h ∈ K} = μ₂ {h | g⁻¹ * h ∈ K}) : μ₁ = μ₂ := by
  refine Measure.ext_of_lintegral _ fun f hf => ?_
  have hQ : ∀ g, ∀ k ∈ K, ∫⁻ l, f (g * k * l) ∂ρ = ∫⁻ l, f (g * l) ∂ρ := by
    intro g k hk
    conv_rhs => rw [← hρ k hk]
    rw [lintegral_map (f := fun l => f (g * l)) (hf.comp (measurable_const_mul g)) (measurable_const_mul k)]
    simp only [mul_assoc]
  have e₁ := lintegral_avg K ρ hρK μ₁ h₁ hf
  have e₂ := lintegral_avg K ρ hρK μ₂ h₂ hf
  rw [lintegral_coset K hK μ₁ hQ] at e₁
  rw [lintegral_coset K hK μ₂ hQ] at e₂
  simp only [hc] at e₁
  have := e₁.symm.trans e₂
  exact (ENNReal.mul_right_inj hρ0 (measure_ne_top _ _)).1 this

end Abstract

section Loc

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F]

omit [MeasurableSpace F] [BorelSpace F] in
theorem secondCountable_units : SecondCountableTopology Fˣ :=
  isOpenEmbedding_units_val.isEmbedding.secondCountableTopology

attribute [local instance] secondCountable_units GlobalTheory.CompanionTheory.LocalTestVectors.secondCountable_GL2

omit [MeasurableSpace F] [BorelSpace F] in
theorem continuous_unipotentGL2 : Continuous (uni2 : F → GL (Fin 2) F) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [uni2] <;> fun_prop
  · refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [uni2] <;> fun_prop

def wE (p : Fˣ × Fˣ × GL (Fin 2) F) : ENNReal := ENNReal.ofReal (wR p)

def Hf (ψ : AddChar F Circle) (f : GL (Fin 2) F → ENNReal) (p : Fˣ × Fˣ × GL (Fin 2) F) : ENNReal :=
  ∫⁻ x, wE p * f (uni2 x * hI p) ∂selfDualMeasure ψ

def iwM (ψ : AddChar F Circle) : Measure (GL (Fin 2) F) :=
  Measure.map (fun q : (Fˣ × Fˣ × GL (Fin 2) F) × F => uni2 q.2 * hI q.1)
    (((mIw ψ).withDensity wE).prod (selfDualMeasure ψ))

theorem measurable_Phi :
    Measurable (fun q : (Fˣ × Fˣ × GL (Fin 2) F) × F => uni2 q.2 * hI q.1) :=
  ((continuous_unipotentGL2.comp continuous_snd).mul
    ((GlobalTheory.CompanionTheory.LocalTestVectors.continuous_iwPt (F := F)).comp continuous_fst)).measurable

theorem wE_eq (p : Fˣ × Fˣ × GL (Fin 2) F) : wE p = ((modulus (p.1 : F) : ENNReal))⁻¹ := by
  have h : (0 : ℝ) < (modulus (p.1 : F) : ℝ) := by exact_mod_cast modulus_pos p.1.ne_zero
  rw [wE, wR, ENNReal.ofReal_inv_of_pos h, ENNReal.ofReal_coe_nnreal]

theorem measurable_wE : Measurable (wE (F := F)) := by
  have h : wE (F := F) = fun p => ((modulus (p.1 : F) : ENNReal))⁻¹ := funext wE_eq
  rw [h]
  exact (measurable_modulus.comp (Units.continuous_val.measurable.comp measurable_fst)).coe_nnreal_ennreal.inv

theorem measurable_integrand {f : GL (Fin 2) F → ENNReal} (hf : Measurable f) :
    Measurable (fun q : (Fˣ × Fˣ × GL (Fin 2) F) × F => wE q.1 * f (uni2 q.2 * hI q.1)) :=
  (measurable_wE.comp measurable_fst).mul (hf.comp measurable_Phi)

theorem measurable_Hf (ψ : AddChar F Circle) {f : GL (Fin 2) F → ENNReal} (hf : Measurable f) :
    Measurable (Hf ψ f) :=
  (measurable_integrand hf).lintegral_prod_right'

theorem finite_restrict (ψ : AddChar F Circle) : IsFiniteMeasure ((LFS.hG ψ).restrict (K2 F)) := by
  haveI : (LFS.hG ψ).IsHaarMeasure := by unfold LFS.hG; infer_instance
  exact ⟨by rw [Measure.restrict_apply_univ]; exact (GLnLocal.isCompact_integralGL F 2).measure_lt_top⟩

attribute [local instance] finite_restrict

instance (ψ : AddChar F Circle) : SFinite (mIw ψ) := by unfold mIw; infer_instance

instance (ψ : AddChar F Circle) : SFinite (iwM ψ) := by unfold iwM; infer_instance

theorem lintegral_iwM (ψ : AddChar F Circle) {f : GL (Fin 2) F → ENNReal} (hf : Measurable f) :
    ∫⁻ g, f g ∂iwM ψ = ∫⁻ p, Hf ψ f p ∂mIw ψ := by
  have h1 : Measurable fun q : (Fˣ × Fˣ × GL (Fin 2) F) × F => f (uni2 q.2 * hI q.1) :=
    hf.comp measurable_Phi
  rw [iwM, lintegral_map hf measurable_Phi, lintegral_prod _ h1.aemeasurable,
    lintegral_withDensity_eq_lintegral_mul _ measurable_wE h1.lintegral_prod_right']
  refine lintegral_congr fun p => ?_
  simp only [Pi.mul_apply, Hf]
  exact (lintegral_const_mul _ (h1.comp measurable_prodMk_left)).symm

theorem haar_inst (ψ : AddChar F Circle) : (LFS.hG ψ).IsHaarMeasure := by
  unfold LFS.hG; infer_instance

attribute [local instance] haar_inst

theorem right_inst (ψ : AddChar F Circle) : (LFS.hG ψ).IsMulRightInvariant :=
  Measures.isMulRightInvariant_GL F 2 _

attribute [local instance] right_inst

theorem mp_restrict_right (ψ : AddChar F Circle) {k : GL (Fin 2) F} (hk : k ∈ GLnLocal.integralGL F 2) :
    MeasurePreserving (· * k) ((LFS.hG ψ).restrict (K2 F)) ((LFS.hG ψ).restrict (K2 F)) := by
  have h := (measurePreserving_mul_right (LFS.hG ψ) k).restrict_preimage
    (GLnLocal.isOpen_integralGL F 2).measurableSet
  have e : (· * k) ⁻¹' ((GLnLocal.integralGL F 2 : Subgroup (GL (Fin 2) F)) : Set (GL (Fin 2) F)) =
      (GLnLocal.integralGL F 2 : Set (GL (Fin 2) F)) := by
    ext g
    exact Subgroup.mul_mem_cancel_right _ hk
  rw [e] at h
  exact h

theorem mp_restrict_left (ψ : AddChar F Circle) {k : GL (Fin 2) F} (hk : k ∈ GLnLocal.integralGL F 2) :
    MeasurePreserving (k * ·) ((LFS.hG ψ).restrict (K2 F)) ((LFS.hG ψ).restrict (K2 F)) := by
  have h := (measurePreserving_mul_left (LFS.hG ψ) k).restrict_preimage
    (GLnLocal.isOpen_integralGL F 2).measurableSet
  have e : (k * ·) ⁻¹' ((GLnLocal.integralGL F 2 : Subgroup (GL (Fin 2) F)) : Set (GL (Fin 2) F)) =
      (GLnLocal.integralGL F 2 : Set (GL (Fin 2) F)) := by
    ext g
    exact Subgroup.mul_mem_cancel_left _ hk
  rw [e] at h
  exact h

theorem iwM_right (ψ : AddChar F Circle) {k : GL (Fin 2) F} (hk : k ∈ GLnLocal.integralGL F 2) :
    (iwM ψ).map (· * k) = iwM ψ := by
  refine Measure.ext_of_lintegral _ fun f hf => ?_
  have hτ : MeasurePreserving (fun p : Fˣ × Fˣ × GL (Fin 2) F => (p.1, p.2.1, p.2.2 * k))
      (mIw ψ) (mIw ψ) := by
    unfold mIw
    exact (MeasurePreserving.id _).prod ((MeasurePreserving.id _).prod (mp_restrict_right ψ hk))
  rw [lintegral_map hf (measurable_mul_const k), lintegral_iwM ψ (f := fun a => f (a * k)) (hf.comp (measurable_mul_const k)),
    lintegral_iwM ψ hf, ← hτ.lintegral_comp (measurable_Hf ψ hf)]
  refine lintegral_congr fun p => ?_
  simp only [Hf, Function.comp]
  refine lintegral_congr fun x => ?_
  have e : uni2 x * hI p * k = uni2 x * hI (p.1, p.2.1, p.2.2 * k) := by
    simp only [hI, mul_assoc]
  rw [e]
  rfl

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] in
theorem unipotent_mul_unipotent_add (x y : F) : (uni2 y * uni2 x : GL (Fin 2) F) = uni2 (y + x) := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [uni2, Matrix.mul_apply, Fin.sum_univ_two, add_comm]

theorem iwM_left_uni (ψ : AddChar F Circle) (y : F) :
    (iwM ψ).map (uni2 y * ·) = iwM ψ := by
  refine Measure.ext_of_lintegral _ fun f hf => ?_
  rw [lintegral_map hf (measurable_const_mul _),
    lintegral_iwM ψ (f := fun a => f (uni2 y * a)) (hf.comp (measurable_const_mul _)),
    lintegral_iwM ψ hf]
  refine lintegral_congr fun p => ?_
  simp only [Hf, Function.comp]
  have e : ∀ x : F, uni2 y * (uni2 x * hI p) = uni2 (y + x) * hI p := fun x => by
    rw [← mul_assoc, unipotent_mul_unipotent_add]
  simp_rw [e]
  exact lintegral_add_left_eq_self (fun x => wE p * f (uni2 x * hI p)) y

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] in
theorem diagonal_mul_unipotent (s t : Fˣ) (x : F) :
    (dg2 s t * uni2 x : GL (Fin 2) F) = uni2 (((s * t⁻¹ : Fˣ) : F) * x) * dg2 s t := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [uni2, dg2, Matrix.mul_apply, Fin.sum_univ_two]
  field_simp

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] in
theorem diagonal_mul_diagonal_alt (s t c d : Fˣ) : (dg2 s t * dg2 c d : GL (Fin 2) F) = dg2 (s * c) (t * d) := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [dg2, Matrix.mul_apply, Fin.sum_univ_two]

theorem iwM_left_dg (ψ : AddChar F Circle) (s t : Fˣ) :
    (iwM ψ).map (dg2 s t * ·) = iwM ψ := by
  refine Measure.ext_of_lintegral _ fun f hf => ?_
  set a₀ : Fˣ := s * t⁻¹ with ha₀
  have hτ : MeasurePreserving (fun p : Fˣ × Fˣ × GL (Fin 2) F => (a₀ * p.1, t * p.2.1, p.2.2))
      (mIw ψ) (mIw ψ) := by
    unfold mIw
    exact (measurePreserving_mul_left _ a₀).prod
      ((measurePreserving_mul_left _ t).prod (MeasurePreserving.id _))
  rw [lintegral_map hf (measurable_const_mul _),
    lintegral_iwM ψ (f := fun a => f (dg2 s t * a)) (hf.comp (measurable_const_mul _)),
    lintegral_iwM ψ hf, ← hτ.lintegral_comp (measurable_Hf ψ hf)]
  refine lintegral_congr fun p => ?_
  have e : ∀ x : F, dg2 s t * (uni2 x * hI p) =
      uni2 ((a₀ : F) * x) * hI (a₀ * p.1, t * p.2.1, p.2.2) := fun x => by
    have e1 : dg2 s t * hI p = hI (a₀ * p.1, t * p.2.1, p.2.2) := by
      have e0 : s * (p.1 * p.2.1) = a₀ * p.1 * (t * p.2.1) := by
        have h : a₀ * t = s := by rw [ha₀, inv_mul_cancel_right]
        rw [← h]
        ac_rfl
      simp only [hI]
      rw [← mul_assoc, diagonal_mul_diagonal_alt, e0]
    rw [← mul_assoc, diagonal_mul_unipotent, mul_assoc, e1]
  have hm0 : (modulus (a₀ : F) : ENNReal) ≠ 0 := ENNReal.coe_ne_zero.2 (modulus_ne_zero a₀.ne_zero)
  have hw : wE ((a₀ * p.1, t * p.2.1, p.2.2) : Fˣ × Fˣ × GL (Fin 2) F) =
      ((modulus (a₀ : F) : ENNReal))⁻¹ * wE p := by
    rw [wE_eq, wE_eq]
    simp only [Units.val_mul, modulus_mul, ENNReal.coe_mul]
    rw [ENNReal.mul_inv (Or.inl hm0) (Or.inl ENNReal.coe_ne_top)]
  simp only [Hf, Function.comp]
  simp_rw [e]
  rw [lintegral_comp_mul_left (selfDualMeasure ψ) a₀.ne_zero
    (fun x => wE p * f (uni2 x * hI (a₀ * p.1, t * p.2.1, p.2.2))), hw]
  simp_rw [mul_assoc]
  rw [lintegral_const_mul' _ _ (ENNReal.inv_ne_top.2 hm0)]

theorem iwM_coset (ψ : AddChar F Circle) (g : GL (Fin 2) F) :
    iwM ψ {h | g⁻¹ * h ∈ GLnLocal.integralGL F 2} = iwM ψ (GLnLocal.integralGL F 2 : Set (GL (Fin 2) F)) := by
  obtain ⟨x, m, n, κ, hκ, rfl⟩ := GlobalTheory.CompanionTheory.GIntIw.iwasawa_decomposition_gl_two F g
  set s : Fˣ := unifUnit F ^ m
  set t : Fˣ := unifUnit F ^ n
  have hK := (GLnLocal.isOpen_integralGL F 2).measurableSet
  have hinv : (uni2 x * dg2 s t * κ)⁻¹ = κ⁻¹ * (dg2 s⁻¹ t⁻¹ * uni2 (-x)) := by
    have h1 : (uni2 x : GL (Fin 2) F)⁻¹ = uni2 (-x) :=
      (eq_inv_of_mul_eq_one_left (GlobalTheory.CompanionTheory.LocalTestVectors.unipotent_neg_mul x)).symm
    have h2 : (dg2 s t : GL (Fin 2) F)⁻¹ = dg2 s⁻¹ t⁻¹ :=
      (eq_inv_of_mul_eq_one_left (GlobalTheory.CompanionTheory.LocalTestVectors.diag_inv_mul_alt s t)).symm
    rw [_root_.mul_inv_rev, _root_.mul_inv_rev, h1, h2]
  have hS : {h | (uni2 x * dg2 s t * κ)⁻¹ * h ∈ GLnLocal.integralGL F 2} =
      (uni2 (-x) * ·) ⁻¹' ((dg2 s⁻¹ t⁻¹ * ·) ⁻¹'
        (GLnLocal.integralGL F 2 : Set (GL (Fin 2) F))) := by
    ext h
    simp only [Set.mem_setOf_eq, Set.mem_preimage, SetLike.mem_coe]
    rw [hinv, mul_assoc, mul_assoc, Subgroup.mul_mem_cancel_left _ (inv_mem hκ)]
  rw [hS, ← Measure.map_apply (measurable_const_mul _) ((measurable_const_mul _) hK), iwM_left_uni,
    ← Measure.map_apply (measurable_const_mul _) hK, iwM_left_dg]

omit [MeasurableSpace F] [BorelSpace F] in
theorem unipotent_mem_integral_GL_iff (x : F) : uni2 x ∈ GLnLocal.integralGL F 2 ↔ x ∈ 𝒪[F] := by
  constructor
  · intro h
    have := ((GLnLocal.mem_integralGL_iff F 2).1 h).1 0 1
    simpa [uni2] using this
  · intro h
    have h' : -x ∈ 𝒪[F] := neg_mem h
    have e : (uni2 x : GL (Fin 2) F)⁻¹ = uni2 (-x) :=
      (eq_inv_of_mul_eq_one_left (GlobalTheory.CompanionTheory.LocalTestVectors.unipotent_neg_mul x)).symm
    rw [GLnLocal.mem_integralGL_iff, e]
    constructor <;> intro i j <;> fin_cases i <;> fin_cases j <;>
      simp [uni2, h, zero_mem, one_mem]

omit [MeasurableSpace F] [BorelSpace F] in
theorem hI_mem {p : Fˣ × Fˣ × GL (Fin 2) F} (hp : p.2.2 ∈ GLnLocal.integralGL F 2)
    (h1 : modulus (p.1 : F) = 1) (h2 : modulus (p.2.1 : F) = 1) :
    hI p ∈ GLnLocal.integralGL F 2 := by
  have h3 : modulus ((p.1 * p.2.1 : Fˣ) : F) = 1 := by
    rw [Units.val_mul, modulus_mul, h1, h2, one_mul]
  exact mul_mem (GlobalTheory.CompanionTheory.GIntIw.diag_unit_mem_integral_gl_two (modulus_eq_one_iff.1 h3).2
    (modulus_eq_one_iff.1 h2).2) hp

omit [MeasurableSpace F] [BorelSpace F] in
theorem mem_K_iff {p : Fˣ × Fˣ × GL (Fin 2) F} (hp : p.2.2 ∈ GLnLocal.integralGL F 2) (x : F) :
    uni2 x * hI p ∈ GLnLocal.integralGL F 2 ↔
      (modulus (p.1 : F) = 1 ∧ modulus (p.2.1 : F) = 1) ∧ x ∈ 𝒪[F] := by
  constructor
  · intro h
    have e : dg2 (p.1 * p.2.1) p.2.1 * p.2.2 = uni2 (-x) * (uni2 x * hI p) := by
      rw [← mul_assoc, GlobalTheory.CompanionTheory.LocalTestVectors.unipotent_neg_mul, one_mul]
      rfl
    obtain ⟨h1, h2⟩ := GlobalTheory.CompanionTheory.LocalTestVectors.modulus_of_decomp hp h e
    rw [Units.val_mul, modulus_mul, h2, mul_one] at h1
    refine ⟨⟨h1, h2⟩, ?_⟩
    exact (unipotent_mem_integral_GL_iff x).1 ((Subgroup.mul_mem_cancel_right _ (hI_mem hp h1 h2)).1 h)
  · rintro ⟨⟨h1, h2⟩, hx⟩
    exact mul_mem ((unipotent_mem_integral_GL_iff x).2 hx) (hI_mem hp h1 h2)

theorem iwM_K (ψ : AddChar F Circle) :
    iwM ψ (GLnLocal.integralGL F 2 : Set (GL (Fin 2) F)) =
      selfDualMeasure ψ (𝒪[F] : Set F) * LFS.hG ψ (GLnLocal.integralGL F 2 : Set (GL (Fin 2) F)) := by
  have hKm : MeasurableSet (GLnLocal.integralGL F 2 : Set (GL (Fin 2) F)) :=
    (GLnLocal.isOpen_integralGL F 2).measurableSet
  have hOm : MeasurableSet (𝒪[F] : Set F) := by
    have e : (𝒪[F] : Set F) = uni2 ⁻¹' (GLnLocal.integralGL F 2 : Set (GL (Fin 2) F)) := by
      ext x
      exact (unipotent_mem_integral_GL_iff x).symm
    rw [e]
    exact continuous_unipotentGL2.measurable hKm
  set U : Set Fˣ := {a | modulus (a : F) = 1} with hU
  have hUm : MeasurableSet U :=
    (measurable_modulus.comp Units.continuous_val.measurable) (measurableSet_singleton (1 : NNReal))
  have hU1 : multHaar F U = 1 := by
    have e : U = (unitFiltrationUnits F 0 : Set Fˣ) := by
      ext a
      constructor
      · intro h
        exact mem_unitFiltrationUnits_zero_iff_ord.2 (modulus_eq_one_iff.1 h).2
      · intro h
        exact modulus_eq_one_iff.2 ⟨a.ne_zero, mem_unitFiltrationUnits_zero_iff_ord.1 h⟩
    rw [e, multHaar_unitFiltrationUnits_zero]
  set T : Set (Fˣ × Fˣ × GL (Fin 2) F) :=
    U ×ˢ (U ×ˢ (GLnLocal.integralGL F 2 : Set (GL (Fin 2) F))) with hTdef
  have hT : MeasurableSet T := hUm.prod (hUm.prod hKm)
  have key : ∀ᵐ p ∂mIw ψ, Hf ψ ((GLnLocal.integralGL F 2 : Set (GL (Fin 2) F)).indicator 1) p =
      T.indicator (fun _ => selfDualMeasure ψ (𝒪[F] : Set F)) p := by
    filter_upwards [GlobalTheory.CompanionTheory.LocalTestVectors.ae_mem_maximal_compact ψ] with p hk
    have hk' : p.2.2 ∈ GLnLocal.integralGL F 2 := hk
    by_cases hp : p ∈ T
    · rw [Set.indicator_of_mem hp]
      have h1 : modulus (p.1 : F) = 1 := hp.1
      have h2 : modulus (p.2.1 : F) = 1 := hp.2.1
      have hw : wE p = 1 := by rw [wE_eq, h1]; simp
      have e : ∀ x, wE p * (GLnLocal.integralGL F 2 : Set (GL (Fin 2) F)).indicator 1 (uni2 x * hI p) =
          (𝒪[F] : Set F).indicator 1 x := by
        intro x
        rw [hw, one_mul]
        by_cases hx : x ∈ 𝒪[F]
        · rw [Set.indicator_of_mem (show x ∈ (𝒪[F] : Set F) from hx),
            Set.indicator_of_mem (show _ ∈ (GLnLocal.integralGL F 2 : Set (GL (Fin 2) F)) from
              (mem_K_iff hk' x).2 ⟨⟨h1, h2⟩, hx⟩)]
          rfl
        · rw [Set.indicator_of_notMem (show x ∉ (𝒪[F] : Set F) from hx),
            Set.indicator_of_notMem (show _ ∉ (GLnLocal.integralGL F 2 : Set (GL (Fin 2) F)) from
              fun h => hx ((mem_K_iff hk' x).1 h).2)]
      simp only [Hf, e]
      exact lintegral_indicator_one hOm
    · rw [Set.indicator_of_notMem hp]
      have e : ∀ x, wE p * (GLnLocal.integralGL F 2 : Set (GL (Fin 2) F)).indicator 1 (uni2 x * hI p) = 0 := by
        intro x
        rw [Set.indicator_of_notMem, mul_zero]
        intro h
        obtain ⟨⟨h1, h2⟩, -⟩ := (mem_K_iff hk' x).1 h
        exact hp ⟨h1, h2, hk'⟩
      simp only [Hf, e, lintegral_zero]
  rw [← lintegral_indicator_one hKm, lintegral_iwM ψ (measurable_one.indicator hKm),
    lintegral_congr_ae key, lintegral_indicator_const hT]
  congr 1
  rw [hTdef]
  unfold mIw
  rw [Measure.prod_prod, Measure.prod_prod, hU1, one_mul, one_mul, Measure.restrict_apply hKm]
  simp [K2]

end Loc

end GlobalTheory.CompanionTheory.IwaHaar

open GlobalTheory.CompanionTheory.IwaHaar in

theorem GlobalTheory.CompanionTheory.IwaHaar.main : ForS fun F _ _ _ _ _ _ ψ => ∃ c : ENNReal, c ≠ 0 ∧ c ≠ ⊤ ∧
    ∀ f : GL (Fin 2) F → ENNReal, Measurable f →
      ∫⁻ p, ∫⁻ x, ENNReal.ofReal (wR p) * f (uni2 x * hI p) ∂selfDualMeasure ψ ∂mIw ψ =
        c * ∫⁻ g, f g ∂LFS.hG ψ := by
  intro F _ _ _ _ _ _ ψ _
  haveI := haar_inst ψ
  haveI := right_inst ψ
  haveI := finite_restrict ψ
  haveI : SecondCountableTopology (GL (Fin 2) F) := GlobalTheory.CompanionTheory.LocalTestVectors.secondCountable_GL2
  have hO : selfDualMeasure ψ (𝒪[F] : Set F) ≠ 0 := by
    rw [selfDualMeasure_integers]
    exact ENNReal.coe_ne_zero.2 (selfDualMeasure_coeff_ne_zero ψ)
  have hT : selfDualMeasure ψ (𝒪[F] : Set F) ≠ ⊤ := by
    rw [selfDualMeasure_integers]
    exact ENNReal.coe_ne_top
  refine ⟨_, hO, hT, fun f hf => ?_⟩
  have hM : iwM ψ = selfDualMeasure ψ (𝒪[F] : Set F) • LFS.hG ψ := by
    refine measure_eq_of_coset (GLnLocal.integralGL F 2) (GLnLocal.isOpen_integralGL F 2)
      ((LFS.hG ψ).restrict (K2 F)) ?_ (ae_restrict_mem (GLnLocal.isOpen_integralGL F 2).measurableSet)
      (fun k hk => (mp_restrict_left ψ hk).map_eq) _ _ (fun k hk => iwM_right ψ hk) ?_ ?_
    · rw [Measure.restrict_apply_univ]
      exact ((GLnLocal.isOpen_integralGL F 2).measure_pos _ ⟨1, one_mem _⟩).ne'
    · intro k hk
      rw [Measure.map_smul, map_mul_right_eq_self]
    · intro g
      rw [iwM_coset, iwM_K, Measure.smul_apply, smul_eq_mul]
      congr 1
      exact (measure_preimage_mul (LFS.hG ψ) g⁻¹ _).symm
  have := lintegral_iwM ψ hf
  rw [hM, lintegral_smul_measure, smul_eq_mul] at this
  exact this.symm.trans rfl
