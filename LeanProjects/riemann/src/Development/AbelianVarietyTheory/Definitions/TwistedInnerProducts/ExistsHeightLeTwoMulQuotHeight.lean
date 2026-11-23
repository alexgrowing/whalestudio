import Mathlib
import Formalism.LocalToGlobal.BesselHermitianTheta.TiedSmooth
import Development.AbelianVarietyTheory.Definitions.Foundations.OfInfProjInfMulOfFinProjFin
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.QuotIntegrableIffCutoff

noncomputable section

namespace GlobalTheory.Grow

open scoped TensorProduct NNReal ENNReal Topology
open NumberField IsDedekindDomain MeasureTheory Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG GlobalTheory.AdelicU

theorem continuous_of_le_mul {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {q h : G → ℝ}
    (hh : Tendsto h (𝓝 1) (𝓝 1)) (hpos : ∀ k, 0 < h k) (hinv : ∀ k, h k⁻¹ = h k)
    (hq : ∀ g k, q (g * k) ≤ q g * h k) : Continuous q := by
  refine continuous_iff_continuousAt.2 fun g => ?_
  have h1 : Tendsto (fun x => h (g⁻¹ * x)) (𝓝 g) (𝓝 1) :=
    hh.comp (Continuous.tendsto' (by fun_prop) g 1 (inv_mul_cancel g))
  have h2 : Tendsto (fun x => q g * h (g⁻¹ * x)) (𝓝 g) (𝓝 (q g)) := by simpa using h1.const_mul (q g)
  have h3 : Tendsto (fun x => q g / h (g⁻¹ * x)) (𝓝 g) (𝓝 (q g)) := by
    have := (tendsto_const_nhds (x := q g)).div h1 one_ne_zero
    rwa [div_one] at this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le h3 h2 (fun x => ?_) fun x => ?_
  · have := hq x (g⁻¹ * x)⁻¹
    rw [hinv, mul_inv_rev, inv_inv, mul_inv_cancel_left] at this
    exact (div_le_iff₀ (hpos _)).2 this
  · simpa using hq g (g⁻¹ * x)

section GeneralLinearIntegers

variable (F : Type) [Field F] [NumberField F] {E : Type} [Field E] [NumberField E] [Algebra F E]

theorem eventually_absFin_tmul_le_one (x : E) :
    ∀ᶠ a in 𝓝 (0 : AF F), ∀ v, absFin F v (compFin F E v (a ⊗ₜ[F] x)) ≤ 1 := by
  obtain ⟨y, c, rfl⟩ : ∃ (y : 𝓞 E) (c : F), x = c • (y : E) := by
    obtain ⟨m, hm, hi⟩ := ((IsFractionRing.isAlgebraic_iff ℤ ℚ E).2
      (Algebra.IsAlgebraic.isAlgebraic x)).exists_integral_multiple
    refine ⟨⟨_, hi⟩, (m : F)⁻¹, ?_⟩
    change _ = (m : F)⁻¹ • (m • x)
    rw [← Int.cast_smul_eq_zsmul F, inv_smul_smul₀ (by exact_mod_cast hm)]
  have ho : IsOpen {a : Af F | ∀ v, a v ∈ v.adicCompletionIntegers F} :=
    RestrictedProduct.isOpen_forall_mem
      (A := fun v : HeightOneSpectrum (𝓞 F) => (v.adicCompletionIntegers F : Set (v.adicCompletion F)))
      fun _ => Valued.isOpen_valuationSubring _
  have hs : Continuous (sndA F) := continuous_snd
  have hc : Continuous fun a : AF F => sndA F (algebraMap F (AF F) c * a) :=
    hs.comp (continuous_const.mul continuous_id)
  have h1 : {a : Af F | ∀ v, a v ∈ v.adicCompletionIntegers F} ∈ 𝓝 (0 : Af F) :=
    ho.mem_nhds fun v => zero_mem (v.adicCompletionIntegers F)
  refine Eventually.mono (hc.tendsto' 0 0 (by rw [mul_zero, map_zero]) h1) fun a ha v => ?_
  rw [← TensorProduct.smul_tmul, Algebra.smul_def]
  refine (absFin_tmul_le F v (evFin F v (algebraMap F (AF F) c * a)) y).trans ?_
  exact Valued.toNormedField.norm_le_one_iff.2 (ha v)

theorem eventually_absFin_le_one_nhds :
    ∀ᶠ z in 𝓝 (0 : AF F ⊗[F] E), ∀ v, absFin F v (compFin F E v z) ≤ 1 := by
  have : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  have : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
  have : IsTopologicalRing (AF F ⊗[F] E) := IsModuleTopology.isTopologicalRing (AF F) _
  let b := Module.finBasis F E
  let e := (Algebra.TensorProduct.basis (AF F) b).equivFun
  have h1 : Continuous e := IsModuleTopology.continuous_of_linearMap e.toLinearMap
  have h2 : ∀ i, ∀ᶠ z in 𝓝 (0 : AF F ⊗[F] E), ∀ v, absFin F v (compFin F E v (e z i ⊗ₜ[F] b i)) ≤ 1 := fun i =>
    (Continuous.tendsto' ((continuous_apply i).comp h1) 0 0 (by simp)).eventually
      (eventually_absFin_tmul_le_one F (b i))
  refine (eventually_all.2 h2).mono fun z hz v => ?_
  have h3 : z = ∑ i, e z i ⊗ₜ[F] b i := by
    conv_lhs => rw [← (Algebra.TensorProduct.basis (AF F) b).sum_equivFun z]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [e, TensorProduct.smul_tmul']
  rw [h3, map_sum]
  exact absFin_sum_le F v _ _ fun i _ => hz i v

theorem continuous_infEmb_compInf (w : InfinitePlace F) (τ : EmbOver E w) :
    Continuous fun z : AF F ⊗[F] E => infEmb τ (compInf F E w z) := by
  have : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  have : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
  have : IsTopologicalRing (AF F ⊗[F] E) := IsModuleTopology.isTopologicalRing (AF F) _
  let b := Module.finBasis F E
  let e := (Algebra.TensorProduct.basis (AF F) b).equivFun
  have h1 : Continuous e := IsModuleTopology.continuous_of_linearMap e.toLinearMap
  have h2 : (fun z : AF F ⊗[F] E => infEmb τ (compInf F E w z)) =
      fun z => ∑ i, InfinitePlace.Completion.extensionEmbedding w ((e z i).1 w) * τ.1 (b i) := by
    funext z
    have h3 : z = ∑ i, e z i ⊗ₜ[F] b i := by
      conv_lhs => rw [← (Algebra.TensorProduct.basis (AF F) b).sum_equivFun z]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp [e, TensorProduct.smul_tmul']
    conv_lhs => rw [h3, map_sum, map_sum]
    rfl
  rw [h2]
  refine continuous_finsetSum _ fun i _ => Continuous.mul ?_ continuous_const
  exact (InfinitePlace.Completion.isometry_extensionEmbedding w).continuous.comp
    ((continuous_apply w).comp (continuous_fst.comp ((continuous_apply i).comp h1)))

variable {n : Type} [Fintype n] [DecidableEq n]

theorem continuous_opNorm : Continuous (opNorm : Matrix n n ℂ → ℝ≥0) :=
  continuous_nnnorm.comp
    (Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ)).toAlgEquiv.toLinearEquiv.toLinearMap.continuous_of_finiteDimensional

theorem continuous_htInf (w : InfinitePlace F) :
    Continuous fun g : GL n (AF F ⊗[F] E) => htInf F w (bc (compInf F E w) g) := by
  have h : Continuous fun y : Matrix n n (AF F ⊗[F] E) => normInf F w (y.map (compInf F E w)) := by
    classical
    exact Continuous.finset_sup_apply (s := Finset.univ)
      (f := fun (τ : EmbOver E w) (y : Matrix n n (AF F ⊗[F] E)) => opNorm ((y.map (compInf F E w)).map (infEmb τ)))
      fun τ _ => continuous_opNorm.comp (continuous_id.matrix_map (continuous_infEmb_compInf F w τ))
  exact continuous_const.max ((h.comp Units.continuous_val).max (h.comp Units.continuous_coe_inv))

theorem eventually_htFin_eq_one :
    ∀ᶠ g in 𝓝 (1 : GL n (AF F ⊗[F] E)), ∀ v, htFin F v (bc (compFin F E v) g) = 1 := by
  have : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  have : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
  have : IsTopologicalRing (AF F ⊗[F] E) := IsModuleTopology.isTopologicalRing (AF F) _
  have h : ∀ᶠ y in 𝓝 (1 : Matrix n n (AF F ⊗[F] E)), ∀ v, normFin F v (y.map (compFin F E v)) ≤ 1 := by
    have h1 : ∀ i j, ∀ᶠ y in 𝓝 (1 : Matrix n n (AF F ⊗[F] E)),
        ∀ v, absFin F v (compFin F E v ((y - 1) i j)) ≤ 1 := fun i j =>
      (Continuous.tendsto' (f := fun y : Matrix n n (AF F ⊗[F] E) => (y - 1) i j)
        ((continuous_id.sub continuous_const).matrix_elem i j) 1 0 (by simp)).eventually
        (eventually_absFin_le_one_nhds F)
    refine (eventually_all.2 fun i => eventually_all.2 (h1 i)).mono fun y hy v => (normFin_le_iff F v).2 fun i j => ?_
    have e : (y.map (compFin F E v)) i j = compFin F E v ((y - 1) i j) + (1 : Matrix n n (Fv F v ⊗[F] E)) i j := by
      by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
    rw [e]
    exact (absFin_add_le F v _ _).trans (max_le (hy i j v) ((absFin_le_normFin F v _ i j).trans (normFin_one_le F v)))
  have h1 := (Units.continuous_val.tendsto' (1 : GL n (AF F ⊗[F] E)) 1 rfl).eventually h
  have h2 := (Units.continuous_coe_inv.tendsto' (1 : GL n (AF F ⊗[F] E)) 1 rfl).eventually h
  exact (h1.and h2).mono fun g hg v => htOf_eq_one.2 ⟨hg.1 v, hg.2 v⟩

theorem continuous_heightGL : Continuous (heightGL F : GL n (AF F ⊗[F] E) → ℝ≥0) := by
  have : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  have : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
  have : IsTopologicalRing (AF F ⊗[F] E) := IsModuleTopology.isTopologicalRing (AF F) _
  have h1 : Continuous fun g : GL n (AF F ⊗[F] E) => ∏ w, htInf F w (bc (compInf F E w) g) :=
    continuous_finsetProd _ fun w _ => continuous_htInf F w
  have h2 : Tendsto (heightGL F : GL n (AF F ⊗[F] E) → ℝ≥0) (𝓝 1) (𝓝 1) := by
    refine (h1.tendsto' 1 1 ?_).congr' ((eventually_htFin_eq_one F).mono fun g hg => ?_)
    · exact Finset.prod_eq_one fun w _ => ((heightGL_eq_one_iff F).1 (heightGL_one F)).1 w
    · simp [heightGL, hg]
  refine continuous_induced_rng.2 (continuous_of_le_mul (q := fun g => (heightGL F g : ℝ)) (h := fun g => (heightGL F g : ℝ))
    (NNReal.tendsto_coe.2 h2) (fun k => ?_) (fun k => by rw [heightGL_inv]) fun g k => ?_)
  · exact_mod_cast zero_lt_one.trans_le (one_le_heightGL F k)
  · exact_mod_cast heightGL_mul_le F g k

theorem htInf_le_heightGL (g : GL n (AF F ⊗[F] E)) (w : InfinitePlace F) :
    htInf F w (bc (compInf F E w) g) ≤ heightGL F g :=
  (Finset.single_le_prod' (f := fun w => htInf F w (bc (compInf F E w) g)) (fun _ _ => one_le_htOf _ _)
    (Finset.mem_univ w)).trans (le_mul_of_one_le_right' (one_le_finprod' fun _ => one_le_htOf _ _))

example : 2 ≤ heightGL F (Matrix.GeneralLinearGroup.scalar (Fin 1)
    (Units.map (inclR (F := F) (AF F) : E →+* _).toMonoidHom (Units.mk0 (2 : E) two_ne_zero))) := by
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  obtain ⟨τ⟩ : Nonempty (EmbOver E w) := inferInstance
  refine le_trans ?_ (((normInf_le_iff F w).1 (le_htOf _ _) τ).trans (htInf_le_heightGL F _ w))
  refine le_of_eq_of_le ?_ (le_of_eq (congrArg opNorm (a₁ := (2 : ℂ) • 1) ?_))
  · unfold opNorm
    rw [map_smul, map_one, nnnorm_smul]
    simp
  · ext i j
    obtain rfl := Subsingleton.elim i j
    change _ = infEmb τ (compInf F E w (Matrix.scalar (Fin 1) (inclR (F := F) (AF F) (2 : E)) i i))
    rw [Matrix.scalar_apply, Matrix.diagonal_apply_eq, map_ofNat, map_ofNat, map_ofNat]
    simp

end GeneralLinearIntegers

section Quot

variable {G : Type} [Group G] [MeasurableSpace G] {R : Subgroup G}

def IsQuotIntL1 (μR : Measure R) (μG : Measure G) (f : G → ℂ) (z : ℂ) : Prop :=
  ∃ F : G → ℂ, Integrable F μG ∧ (∀ h, Integrable (fun r : R => F (r * h)) μR) ∧
    (∀ h, f h = ∫ r : R, F (r * h) ∂μR) ∧ z = ∫ g, F g ∂μG

variable {μR : Measure R} {μG : Measure G} {f f' : G → ℂ} {z z' : ℂ}

theorem IsQuotIntL1.zero : IsQuotIntL1 μR μG 0 0 :=
  ⟨0, integrable_zero _ _ _, fun _ => integrable_zero _ _ _, fun _ => by simp, by simp⟩

theorem IsQuotIntL1.add (h : IsQuotIntL1 μR μG f z) (h' : IsQuotIntL1 μR μG f' z') :
    IsQuotIntL1 μR μG (f + f') (z + z') := by
  obtain ⟨F, h1, h2, h3, h4⟩ := h
  obtain ⟨F', h1', h2', h3', h4'⟩ := h'
  exact ⟨F + F', h1.add h1', fun x => (h2 x).add (h2' x),
    fun x => by rw [Pi.add_apply, h3, h3', ← integral_add (h2 x) (h2' x)]; rfl,
    by rw [h4, h4', ← integral_add h1 h1']; rfl⟩

theorem IsQuotIntL1.smul (c : ℂ) (h : IsQuotIntL1 μR μG f z) : IsQuotIntL1 μR μG (c • f) (c * z) := by
  obtain ⟨F, h1, h2, h3, h4⟩ := h
  exact ⟨c • F, h1.smul c, fun x => (h2 x).const_mul c,
    fun x => by rw [Pi.smul_apply, h3, smul_eq_mul, ← integral_const_mul]; rfl,
    by rw [h4, ← integral_const_mul]; rfl⟩

theorem IsQuotIntL1.conj (h : IsQuotIntL1 μR μG f z) :
    IsQuotIntL1 μR μG (fun g => starRingEnd ℂ (f g)) (starRingEnd ℂ z) := by
  obtain ⟨F, h1, h2, h3, h4⟩ := h
  exact ⟨fun g => starRingEnd ℂ (F g), (RCLike.conjCLE (K := ℂ)).toContinuousLinearMap.integrable_comp h1,
    fun x => (RCLike.conjCLE (K := ℂ)).toContinuousLinearMap.integrable_comp (h2 x),
    fun x => by simp only [h3, integral_conj], by rw [h4, integral_conj]⟩

theorem IsQuotIntL1.mul_right [MeasurableMul G] [μG.IsMulRightInvariant] (h : IsQuotIntL1 μR μG f z) (k : G) :
    IsQuotIntL1 μR μG (fun g => f (g * k)) z := by
  obtain ⟨F, h1, h2, h3, h4⟩ := h
  exact ⟨fun g => F (g * k), h1.comp_mul_right k, fun x => by simpa only [mul_assoc] using h2 (x * k),
    fun x => by simpa only [mul_assoc] using h3 (x * k), by rw [h4, integral_mul_right_eq_self]⟩

theorem IsQuotIntL1.left [MeasurableMul R] [μR.IsMulRightInvariant] (h : IsQuotIntL1 μR μG f z) {s : G} (hs : s ∈ R)
    (x : G) : f (s * x) = f x := by
  obtain ⟨F, -, -, h3, -⟩ := h
  rw [h3, h3, ← integral_mul_right_eq_self (μ := μR) (fun r : R => F (r * x)) ⟨s, hs⟩]
  simp [mul_assoc]

theorem integrable_of_lintegral_eq_one {α : Type} [MeasurableSpace α] {μ : Measure α} {b : α → ℝ≥0} (hm : Measurable b)
    (h : ∫⁻ x, b x ∂μ = 1) : Integrable (fun x => (b x : ℝ)) μ ∧ ∫ x, (b x : ℝ) ∂μ = 1 := by
  have hi : Integrable (fun x => (b x : ℝ)) μ :=
    integrable_toReal_of_lintegral_ne_top (f := fun x => (b x : ℝ≥0∞)) hm.coe_nnreal_ennreal.aemeasurable
      (by rw [h]; exact ENNReal.one_ne_top)
  exact ⟨hi, ENNReal.ofReal_eq_one.1 ((lintegral_coe_eq_integral b hi).symm.trans h)⟩

variable [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G] [BorelSpace G]

open GlobalTheory.Tw in

theorem IsQuotIntL1.cutoff [SFinite μG] [μG.IsMulLeftInvariant] [SFinite μR] [μR.IsInvInvariant]
    (h : IsQuotIntL1 μR μG f z) {β : G → ℝ≥0} (hβ : IsCosetCutoff R μR β) :
    Integrable (fun x => (β x : ℝ) • f x) μG ∧ z = ∫ x, (β x : ℝ) • f x ∂μG := by
  obtain ⟨F, h1, h2, h3, h4⟩ := h
  have hc : Measurable fun p : R × G => (p.1 : G) * p.2 :=
    (measurable_subtype_coe.comp measurable_fst).mul measurable_snd
  have hc' : Measurable fun p : R × G => ((p.1⁻¹ : R) : G) * p.2 :=
    (measurable_subtype_coe.comp measurable_fst.inv).mul measurable_snd
  have hb : ∀ x, Integrable (fun t : R => (β ((t⁻¹ : R) * x) : ℝ)) μR ∧ ∫ t : R, (β ((t⁻¹ : R) * x) : ℝ) ∂μR = 1 :=
    fun x => integrable_of_lintegral_eq_one (hβ.1.comp (hc'.comp measurable_prodMk_right))
      (by rw [lintegral_inv_eq_self (μ := μR) (fun t : R => (β (t * x) : ℝ≥0∞)), hβ.2])
  have hb' := fun x => (hb x).2
  have hT : MeasurePreserving (fun p : R × G => (p.1, (p.1 : G) * p.2)) (μR.prod μG) (μR.prod μG) :=
    (MeasurePreserving.id μR).skew_product hc (Eventually.of_forall fun r => map_mul_left_eq_self μG (r : G))
  have hm : AEStronglyMeasurable (fun p : R × G => (β ((p.1⁻¹ : R) * p.2) : ℝ) • F p.2) (μR.prod μG) :=
    (hβ.1.comp hc').coe_nnreal_real.aestronglyMeasurable.smul h1.1.comp_snd
  have hI : Integrable (fun p : R × G => (β ((p.1⁻¹ : R) * p.2) : ℝ) • F p.2) (μR.prod μG) := by
    refine (integrable_prod_iff' hm).2 ⟨Eventually.of_forall fun x => (hb x).1.smul_const (F x), ?_⟩
    simpa only [norm_smul, integral_mul_const, hb', one_mul, Real.norm_of_nonneg (NNReal.coe_nonneg _)] using h1.norm
  have hI' : Integrable (fun p : R × G => (β p.2 : ℝ) • F (p.1 * p.2)) (μR.prod μG) := by
    simpa [Function.comp_def] using (hT.integrable_comp hm).2 hI
  have e : ∀ x, ∫ r : R, (β x : ℝ) • F (r * x) ∂μR = (β x : ℝ) • f x := fun x => by rw [integral_smul, h3]
  refine ⟨by simpa only [e] using hI'.integral_prod_right, ?_⟩
  have e1 := integral_prod_symm _ hI
  have e2 := integral_prod_symm _ hI'
  have e3 : ∫ p : R × G, (β p.2 : ℝ) • F (p.1 * p.2) ∂μR.prod μG =
      ∫ p : R × G, (β ((p.1⁻¹ : R) * p.2) : ℝ) • F p.2 ∂μR.prod μG := by
    have := integral_map hT.aemeasurable (f := fun p : R × G => (β ((p.1⁻¹ : R) * p.2) : ℝ) • F p.2)
      (by rwa [hT.map_eq])
    rw [hT.map_eq] at this
    rw [this]
    simp
  simp only [e] at e2
  simp only [integral_smul_const, hb', one_smul] at e1
  rw [h4, ← e1, ← e3, e2]

variable [LocallyCompactSpace G] [T2Space G] [SFinite μG] [μG.IsMulLeftInvariant] [μR.IsHaarMeasure] [μR.IsInvInvariant]

theorem IsQuotIntL1.unique (hR : IsClosed (R : Set G)) (h : IsQuotIntL1 μR μG f z) (h' : IsQuotIntL1 μR μG f z') :
    z = z' := by
  obtain ⟨β, -, hβ⟩ := GlobalTheory.Tw.exists_isCosetCutoff (μT := μR) hR
  have : LocallyCompactSpace R := hR.locallyCompactSpace
  have : SecondCountableTopology R := TopologicalSpace.Subtype.secondCountableTopology (R : Set G)
  rw [(h.cutoff hβ).2, (h'.cutoff hβ).2]

open GlobalTheory.Tw in

theorem isQuotIntL1_iff (hR : IsClosed (R : Set G)) (hm : Measurable f) :
    IsQuotIntL1 μR μG f z ↔
      (∀ s ∈ R, ∀ x, f (s * x) = f x) ∧ QuotIntegrable R μG μR f ∧ z = quotInt R μG μR f := by
  obtain ⟨β, -, hβ⟩ := exists_isCosetCutoff (μT := μR) hR
  have : LocallyCompactSpace R := hR.locallyCompactSpace
  have : SecondCountableTopology R := TopologicalSpace.Subtype.secondCountableTopology (R : Set G)
  have : μR.IsMulRightInvariant := by rw [← Measure.inv_eq_self μR]; infer_instance
  constructor
  · intro h
    have hl : ∀ s ∈ R, ∀ x, f (s * x) = f x := fun s hs => h.left hs
    exact ⟨hl, (quotIntegrable_iff_cutoff hR hβ hm hl).2 (h.cutoff hβ).1,
      by rw [quotInt_eq_cutoff hR hβ hm hl, (h.cutoff hβ).2]⟩
  · rintro ⟨hl, hi, rfl⟩
    have hb := fun x => integrable_of_lintegral_eq_one (μ := μR) (b := fun t : R => β (t * x))
      (hβ.1.comp (measurable_subtype_coe.mul_const x)) (hβ.2 x)
    have hb' := fun x => (hb x).2
    refine ⟨fun x => (β x : ℝ) • f x, (quotIntegrable_iff_cutoff hR hβ hm hl).1 hi, fun x => ?_, fun x => ?_,
      quotInt_eq_cutoff hR hβ hm hl⟩
    · simpa only [hl _ (Subtype.property _)] using (hb x).1.smul_const (f x)
    · simp only [hl _ (Subtype.property _), integral_smul_const, hb', one_smul]

end Quot

section Unitary

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (V W : HSp D)

def height (g : GA D V) : ℝ := heightGL D.host.F (Formalism.L2.Theta.matHom V g)

theorem one_le_height (g : GA D V) : 1 ≤ height V g := by
  unfold height; exact_mod_cast one_le_heightGL _ _

theorem height_pos (g : GA D V) : 0 < height V g := zero_lt_one.trans_le (one_le_height V g)

@[simp] theorem height_one : height V 1 = 1 := by
  unfold height; rw [map_one, heightGL_one, NNReal.coe_one]

@[simp] theorem height_inv (g : GA D V) : height V g⁻¹ = height V g := by
  unfold height; rw [map_inv, heightGL_inv]

theorem height_mul_le (g h : GA D V) : height V (g * h) ≤ height V g * height V h := by
  unfold height; rw [map_mul]; exact_mod_cast heightGL_mul_le _ _ _

theorem htInf_le_height (g : GA D V) (w : InfinitePlace D.host.F) :
    (htInf D.host.F w (bc (compInf D.host.F D.host.E w) (Formalism.L2.Theta.matHom V g)) : ℝ) ≤ height V g := by
  unfold height; exact_mod_cast htInf_le_heightGL _ _ w

theorem continuous_height : Continuous (height V) :=
  NNReal.continuous_coe.comp ((continuous_heightGL _).comp continuous_subtype_val)

theorem exists_height_le_of_isCompact {K : Set (GA D V)} (hK : IsCompact K) : ∃ C, ∀ g ∈ K, height V g ≤ C := by
  obtain ⟨C, hC⟩ := hK.bddAbove_image (continuous_height V).continuousOn
  exact ⟨C, fun g hg => hC ⟨g, hg, rfl⟩⟩

def quotHeight (g : GA D V) : ℝ := ⨅ γ : GQ V, height V (γ * g)

theorem quotHeight_le (g : GA D V) {γ : GA D V} (hγ : γ ∈ GQ V) : quotHeight V g ≤ height V (γ * g) :=
  ciInf_le (f := fun γ : GQ V => height V (γ * g)) ⟨1, by rintro _ ⟨_, rfl⟩; exact one_le_height V _⟩ ⟨γ, hγ⟩

theorem quotHeight_le_height (g : GA D V) : quotHeight V g ≤ height V g := by
  simpa using quotHeight_le V g (one_mem _)

theorem le_quotHeight_iff {g : GA D V} {c : ℝ} : c ≤ quotHeight V g ↔ ∀ γ ∈ GQ V, c ≤ height V (γ * g) :=
  ⟨fun h _ hγ => h.trans (quotHeight_le V g hγ), fun h => le_ciInf fun γ => h γ γ.2⟩

theorem one_le_quotHeight (g : GA D V) : 1 ≤ quotHeight V g := (le_quotHeight_iff V).2 fun _ _ => one_le_height V _

theorem quotHeight_pos (g : GA D V) : 0 < quotHeight V g := zero_lt_one.trans_le (one_le_quotHeight V g)

theorem quotHeight_left {γ : GA D V} (hγ : γ ∈ GQ V) (g : GA D V) : quotHeight V (γ * g) = quotHeight V g := by
  refine le_antisymm ((le_quotHeight_iff V).2 fun δ hδ => ?_) ((le_quotHeight_iff V).2 fun δ hδ => ?_)
  · simpa [mul_assoc] using quotHeight_le V (γ * g) (mul_mem hδ (inv_mem hγ))
  · simpa [mul_assoc] using quotHeight_le V g (mul_mem hδ hγ)

theorem quotHeight_of_mem {γ : GA D V} (hγ : γ ∈ GQ V) : quotHeight V γ = 1 :=
  le_antisymm (by simpa using quotHeight_le V γ (inv_mem hγ)) (one_le_quotHeight V γ)

theorem quotHeight_mul_le (g h : GA D V) : quotHeight V (g * h) ≤ quotHeight V g * height V h := by
  rw [← div_le_iff₀ (height_pos V h)]
  refine (le_quotHeight_iff V).2 fun γ hγ => (div_le_iff₀ (height_pos V h)).2 ?_
  exact (quotHeight_le V _ hγ).trans (by rw [← mul_assoc]; exact height_mul_le V _ _)

theorem continuous_quotHeight : Continuous (quotHeight V) :=
  continuous_of_le_mul ((continuous_height V).tendsto' 1 1 (height_one V)) (height_pos V) (height_inv V)
    (quotHeight_mul_le V)

theorem exists_height_le_two_mul_quotHeight (g : GA D V) : ∃ γ ∈ GQ V, height V (γ * g) ≤ 2 * quotHeight V g := by
  by_contra! h
  have := (le_quotHeight_iff V).2 fun γ hγ => (h γ hγ).le
  linarith [quotHeight_pos V g]

variable {X : Type} [NormedAddCommGroup X]

def ModGrowthExp (A : ℕ) (f : GA D V → X) : Prop := ∃ C : ℝ, ∀ g, ‖f g‖ ≤ C * height V g ^ A

def ModGrowth (f : GA D V → X) : Prop := ∃ (C : ℝ) (A : ℕ), ∀ g, ‖f g‖ ≤ C * height V g ^ A

def ModGrowth₂ (f : GA D V → GA D W → X) : Prop :=
  ∃ (C : ℝ) (A : ℕ), ∀ g h, ‖f g h‖ ≤ C * (height V g * height W h) ^ A

def UnifModGrowth (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (φ : GA D V → ℂ) : Prop :=
  ∃ A : ℕ, ∀ l : List (D.what₂.Tau × Matrix (Fin V.rank) (Fin V.rank) ℂ), (∀ p ∈ l, p.2 ∈ lieAt V p.1) →
    ModGrowthExp V A (l.foldr (fun p f => Rder θ V p.1 p.2 f) φ)

variable {V W}

theorem modGrowth_iff_exp {f : GA D V → X} : ModGrowth V f ↔ ∃ A, ModGrowthExp V A f := exists_comm

theorem nonneg_of_growth {f : GA D V → X} {C : ℝ} {A : ℕ} (h : ∀ g, ‖f g‖ ≤ C * height V g ^ A) : 0 ≤ C := by
  simpa using (norm_nonneg _).trans (h 1)

theorem ModGrowthExp.mono {f : GA D V → X} {A B : ℕ} (h : ModGrowthExp V A f) (hAB : A ≤ B) : ModGrowthExp V B f := by
  obtain ⟨C, hC⟩ := h
  exact ⟨C, fun g => (hC g).trans
    (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (one_le_height V g) hAB) (nonneg_of_growth hC))⟩

theorem ModGrowthExp.add {f f' : GA D V → X} {A : ℕ} (h : ModGrowthExp V A f) (h' : ModGrowthExp V A f') :
    ModGrowthExp V A (f + f') := by
  obtain ⟨C, hC⟩ := h
  obtain ⟨C', hC'⟩ := h'
  exact ⟨C + C', fun g => (norm_add_le _ _).trans (by rw [add_mul]; exact add_le_add (hC g) (hC' g))⟩

theorem ModGrowthExp.mul {f f' : GA D V → ℂ} {A B : ℕ} (h : ModGrowthExp V A f) (h' : ModGrowthExp V B f') :
    ModGrowthExp V (A + B) (f * f') := by
  obtain ⟨C, hC⟩ := h
  obtain ⟨C', hC'⟩ := h'
  refine ⟨C * C', fun g => ?_⟩
  rw [Pi.mul_apply, norm_mul, pow_add, mul_mul_mul_comm]
  exact mul_le_mul (hC g) (hC' g) (norm_nonneg _) ((norm_nonneg _).trans (hC g))

theorem ModGrowthExp.translate {f : GA D V → X} {A : ℕ} (h : ModGrowthExp V A f) (a b : GA D V) :
    ModGrowthExp V A fun g => f (a * g * b) := by
  obtain ⟨C, hC⟩ := h
  refine ⟨C * (height V a * height V b) ^ A, fun g => (hC _).trans ?_⟩
  rw [mul_assoc C, ← mul_pow]
  refine mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (height_pos V _).le ?_ _) (nonneg_of_growth hC)
  calc height V (a * g * b) ≤ height V a * height V g * height V b :=
        (height_mul_le V _ _).trans (mul_le_mul_of_nonneg_right (height_mul_le V _ _) (height_pos V b).le)
    _ = _ := by ring

theorem norm_le_quotHeight_pow {f : GA D V → X} (hf : ∀ γ ∈ GQ V, ∀ g, f (γ * g) = f g) {C : ℝ} {A : ℕ}
    (h : ∀ g, ‖f g‖ ≤ C * height V g ^ A) (g : GA D V) : ‖f g‖ ≤ C * 2 ^ A * quotHeight V g ^ A := by
  obtain ⟨γ, hγ, h2⟩ := exists_height_le_two_mul_quotHeight V g
  rw [← hf γ hγ g, mul_assoc, ← mul_pow]
  exact (h _).trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (height_pos V _).le h2 _) (nonneg_of_growth h))

theorem ModGrowth.of_bounded {f : GA D V → X} {C : ℝ} (h : ∀ g, ‖f g‖ ≤ C) : ModGrowth V f :=
  ⟨C, 0, by simpa using h⟩

theorem ModGrowth.of_le {Y : Type} [NormedAddCommGroup Y] {f : GA D V → X} {f' : GA D V → Y} (h : ModGrowth V f)
    (hle : ∀ g, ‖f' g‖ ≤ ‖f g‖) : ModGrowth V f' := by
  obtain ⟨C, A, hC⟩ := h
  exact ⟨C, A, fun g => (hle g).trans (hC g)⟩

theorem ModGrowth.add {f f' : GA D V → X} (h : ModGrowth V f) (h' : ModGrowth V f') : ModGrowth V (f + f') := by
  obtain ⟨A, hA⟩ := modGrowth_iff_exp.1 h
  obtain ⟨B, hB⟩ := modGrowth_iff_exp.1 h'
  exact modGrowth_iff_exp.2 ⟨max A B, (hA.mono (le_max_left _ _)).add (hB.mono (le_max_right _ _))⟩

theorem ModGrowth.mul {f f' : GA D V → ℂ} (h : ModGrowth V f) (h' : ModGrowth V f') : ModGrowth V (f * f') := by
  obtain ⟨A, hA⟩ := modGrowth_iff_exp.1 h
  obtain ⟨B, hB⟩ := modGrowth_iff_exp.1 h'
  exact modGrowth_iff_exp.2 ⟨A + B, hA.mul hB⟩

theorem ModGrowth.translate {f : GA D V → X} (h : ModGrowth V f) (a b : GA D V) :
    ModGrowth V fun g => f (a * g * b) := by
  obtain ⟨A, hA⟩ := modGrowth_iff_exp.1 h
  exact modGrowth_iff_exp.2 ⟨A, hA.translate a b⟩

theorem ModGrowth₂.right {f : GA D V → GA D W → X} (h : ModGrowth₂ V W f) (g : GA D V) : ModGrowth W (f g) := by
  obtain ⟨C, A, hC⟩ := h
  exact ⟨C * height V g ^ A, A, fun h => by rw [mul_assoc, ← mul_pow]; exact hC g h⟩

theorem ModGrowth₂.swap {f : GA D V → GA D W → X} (h : ModGrowth₂ V W f) : ModGrowth₂ W V fun h g => f g h := by
  obtain ⟨C, A, hC⟩ := h
  exact ⟨C, A, fun h g => by rw [mul_comm (height W h)]; exact hC g h⟩

theorem ModGrowth₂.left {f : GA D V → GA D W → X} (h : ModGrowth₂ V W f) (k : GA D W) : ModGrowth V fun g => f g k :=
  h.swap.right k

variable (V)

def RapidDec (Φ : GA D V → X) : Prop :=
  (∀ γ ∈ GQ V, ∀ g, Φ (γ * g) = Φ g) ∧ Continuous Φ ∧ ∀ N : ℕ, ∃ C : ℝ, ∀ g, ‖Φ g‖ * quotHeight V g ^ N ≤ C

def decaySize (N : ℕ) (Φ : GA D V → X) : ℝ≥0∞ := ⨆ g, ENNReal.ofReal (‖Φ g‖ * quotHeight V g ^ N)

theorem rapidDec_exp_neg : RapidDec V fun g => (Real.exp (-quotHeight V g) : ℂ) := by
  refine ⟨fun γ hγ g => by simp only [quotHeight_left V hγ],
    Complex.continuous_ofReal.comp (Real.continuous_exp.comp (continuous_quotHeight V).neg),
    fun N => ⟨N.factorial, fun g => ?_⟩⟩
  have h := Real.pow_div_factorial_le_exp _ (quotHeight_pos V g).le N
  rw [div_le_iff₀ (by positivity)] at h
  rw [Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le, Real.exp_neg, inv_mul_le_iff₀ (Real.exp_pos _)]
  exact h

variable {V}

theorem decaySize_le_iff {N : ℕ} {Φ : GA D V → X} {C : ℝ} (hC : 0 ≤ C) :
    decaySize V N Φ ≤ ENNReal.ofReal C ↔ ∀ g, ‖Φ g‖ * quotHeight V g ^ N ≤ C := by
  simp only [decaySize, iSup_le_iff, ENNReal.ofReal_le_ofReal_iff hC]

theorem rapidDec_iff_decaySize {Φ : GA D V → X} :
    RapidDec V Φ ↔ (∀ γ ∈ GQ V, ∀ g, Φ (γ * g) = Φ g) ∧ Continuous Φ ∧ ∀ N, decaySize V N Φ ≠ ∞ := by
  refine and_congr_right fun _ => and_congr_right fun _ => forall_congr' fun N => ⟨?_, fun h => ?_⟩
  · rintro ⟨C, hC⟩
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top (iSup_le fun g => ENNReal.ofReal_le_ofReal (hC g))
  · exact ⟨_, (decaySize_le_iff ENNReal.toReal_nonneg).1 (ENNReal.ofReal_toReal h).ge⟩

theorem RapidDec.left {Φ : GA D V → X} (h : RapidDec V Φ) {γ : GA D V} (hγ : γ ∈ GQ V) (g : GA D V) :
    Φ (γ * g) = Φ g := h.1 γ hγ g

theorem RapidDec.continuous {Φ : GA D V → X} (h : RapidDec V Φ) : Continuous Φ := h.2.1

theorem RapidDec.decay {Φ : GA D V → X} (h : RapidDec V Φ) (N : ℕ) : ∃ C : ℝ, ∀ g, ‖Φ g‖ * quotHeight V g ^ N ≤ C :=
  h.2.2 N

theorem RapidDec.bounded {Φ : GA D V → X} (h : RapidDec V Φ) : ∃ C : ℝ, ∀ g, ‖Φ g‖ ≤ C := by
  simpa using h.decay 0

theorem RapidDec.of_cover {Φ : GA D V → X} (hl : ∀ γ ∈ GQ V, ∀ g, Φ (γ * g) = Φ g) (hc : Continuous Φ) {S : Set (GA D V)}
    (hS : ∀ g, ∃ γ ∈ GQ V, γ * g ∈ S) (h : ∀ N : ℕ, ∃ C : ℝ, ∀ g ∈ S, ‖Φ g‖ * height V g ^ N ≤ C) : RapidDec V Φ := by
  refine ⟨hl, hc, fun N => (h N).imp fun C hC g => ?_⟩
  obtain ⟨γ, hγ, hg⟩ := hS g
  rw [← hl γ hγ g]
  exact (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (quotHeight_pos V g).le (quotHeight_le V g hγ) N)
    (norm_nonneg _)).trans (hC _ hg)

theorem RapidDec.of_isCompact {Φ : GA D V → X} (hl : ∀ γ ∈ GQ V, ∀ g, Φ (γ * g) = Φ g) (hc : Continuous Φ)
    {K : Set (GA D V)} (hK : IsCompact K) (hS : ∀ g, ∃ γ ∈ GQ V, γ * g ∈ K) : RapidDec V Φ := by
  refine .of_cover hl hc hS fun N => ?_
  obtain ⟨C, hC⟩ := hK.bddAbove_image (hc.norm.mul ((continuous_height V).pow N)).continuousOn
  exact ⟨C, fun g hg => hC ⟨g, hg, rfl⟩⟩

theorem RapidDec.zero : RapidDec V (0 : GA D V → X) :=
  ⟨fun _ _ _ => rfl, continuous_const, fun _ => ⟨0, fun _ => by simp⟩⟩

theorem RapidDec.add {Φ Ψ : GA D V → X} (h : RapidDec V Φ) (h' : RapidDec V Ψ) : RapidDec V (Φ + Ψ) := by
  refine ⟨fun γ hγ g => by rw [Pi.add_apply, h.left hγ, h'.left hγ, Pi.add_apply], h.continuous.add h'.continuous,
    fun N => ?_⟩
  obtain ⟨C, hC⟩ := h.decay N
  obtain ⟨C', hC'⟩ := h'.decay N
  refine ⟨C + C', fun g => le_trans ?_ (add_le_add (hC g) (hC' g))⟩
  rw [← add_mul]
  exact mul_le_mul_of_nonneg_right (norm_add_le _ _) (pow_pos (quotHeight_pos V g) N).le

theorem RapidDec.of_le {Y : Type} [NormedAddCommGroup Y] {Φ : GA D V → X} {Ψ : GA D V → Y} (h : RapidDec V Φ)
    (hl : ∀ γ ∈ GQ V, ∀ g, Ψ (γ * g) = Ψ g) (hc : Continuous Ψ) (hle : ∀ g, ‖Ψ g‖ ≤ ‖Φ g‖) : RapidDec V Ψ :=
  ⟨hl, hc, fun N => (h.decay N).imp fun _ hC g =>
    (mul_le_mul_of_nonneg_right (hle g) (pow_pos (quotHeight_pos V g) N).le).trans (hC g)⟩

theorem RapidDec.conj {Φ : GA D V → ℂ} (h : RapidDec V Φ) : RapidDec V fun g => starRingEnd ℂ (Φ g) :=
  h.of_le (fun γ hγ g => by rw [h.left hγ]) (Complex.continuous_conj.comp h.continuous) fun g => (Complex.norm_conj _).le

theorem RapidDec.mul_right {Φ : GA D V → X} (h : RapidDec V Φ) (k : GA D V) : RapidDec V fun g => Φ (g * k) := by
  refine ⟨fun γ hγ g => by simp only [mul_assoc, h.left hγ], h.continuous.comp (continuous_mul_const k), fun N => ?_⟩
  obtain ⟨C, hC⟩ := h.decay N
  refine ⟨C * height V k ^ N, fun g => ?_⟩
  have h1 : quotHeight V g ≤ quotHeight V (g * k) * height V k := by simpa using quotHeight_mul_le V (g * k) k⁻¹
  calc ‖Φ (g * k)‖ * quotHeight V g ^ N ≤ ‖Φ (g * k)‖ * (quotHeight V (g * k) * height V k) ^ N :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (quotHeight_pos V g).le h1 N) (norm_nonneg _)
    _ = ‖Φ (g * k)‖ * quotHeight V (g * k) ^ N * height V k ^ N := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (hC _) (pow_pos (height_pos V k) N).le

theorem RapidDec.modGrowth_mul {f Φ : GA D V → ℂ} (h : RapidDec V Φ) (hf : ModGrowth V f)
    (hl : ∀ γ ∈ GQ V, ∀ g, f (γ * g) = f g) (hc : Continuous f) : RapidDec V (f * Φ) := by
  refine ⟨fun γ hγ g => by rw [Pi.mul_apply, h.left hγ, hl γ hγ, Pi.mul_apply], hc.mul h.continuous, fun N => ?_⟩
  obtain ⟨B, A, hB⟩ := hf
  obtain ⟨C, hC⟩ := h.decay (A + N)
  have hB0 := nonneg_of_growth hB
  refine ⟨B * 2 ^ A * C, fun g => ?_⟩
  calc ‖(f * Φ) g‖ * quotHeight V g ^ N = ‖f g‖ * (‖Φ g‖ * quotHeight V g ^ N) := by
        rw [Pi.mul_apply, norm_mul, mul_assoc]
    _ ≤ B * 2 ^ A * quotHeight V g ^ A * (‖Φ g‖ * quotHeight V g ^ N) :=
        mul_le_mul_of_nonneg_right (norm_le_quotHeight_pow hl hB g)
          (mul_nonneg (norm_nonneg _) (pow_pos (quotHeight_pos V g) N).le)
    _ = B * 2 ^ A * (‖Φ g‖ * quotHeight V g ^ (A + N)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (hC g) (by positivity)

theorem RapidDec.smul {Φ : GA D V → ℂ} (c : ℂ) (h : RapidDec V Φ) : RapidDec V (c • Φ) :=
  h.modGrowth_mul (f := fun _ => c) (.of_bounded fun _ => le_rfl) (fun _ _ _ => rfl) continuous_const

theorem RapidDec.integrableOn {Φ : GA D V → ℂ} (h : RapidDec V Φ) {μ : Measure (GA D V)} {S : Set (GA D V)}
    (hS : μ S ≠ ∞) : IntegrableOn Φ S μ := by
  obtain ⟨C, hC⟩ := h.bounded
  exact Measure.integrableOn_of_bounded hS h.continuous.aestronglyMeasurable (Eventually.of_forall hC)

example : ModGrowthExp V 1 (height V) := ⟨1, fun g => by simp [abs_of_pos (height_pos V g)]⟩

example : ∃ Φ : GA D V → ℂ, RapidDec V Φ ∧ Φ 1 = Real.exp (-1) :=
  ⟨_, rapidDec_exp_neg V, by simp only [quotHeight_of_mem V (one_mem _)]⟩

end Unitary

theorem isQuotIntL1_bot {G : Type} [Group G] [MeasurableSpace G] {μG : Measure G} {f : G → ℂ} {z : ℂ} :
    IsQuotIntL1 (R := ⊥) (Measure.dirac 1) μG f z ↔ Integrable f μG ∧ z = ∫ g, f g ∂μG := by
  have e : ∀ (F : G → ℂ) (h : G), (fun r : (⊥ : Subgroup G) => F (r * h)) = fun _ => F h := fun F h =>
    funext fun r => by rw [Subsingleton.elim r 1]; simp
  constructor
  · rintro ⟨F, h1, -, h3, h4⟩
    obtain rfl : f = F := funext fun h => by simp [h3, e]
    exact ⟨h1, h4⟩
  · rintro ⟨h1, h2⟩
    exact ⟨f, h1, fun h => by rw [e]; exact integrable_const _, fun h => by simp [e], h2⟩

example {G : Type} [Group G] [MeasurableSpace G] {R : Subgroup G} (μR : Measure R) (μG : Measure G)
    [IsProbabilityMeasure μR] [IsProbabilityMeasure μG] : IsQuotIntL1 μR μG 1 1 :=
  ⟨1, integrable_const _, fun _ => integrable_const _, fun _ => by simp, by simp⟩

end GlobalTheory.Grow

end
