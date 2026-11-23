import Mathlib
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.TopSing

noncomputable section

open MeasureTheory Set Filter Topology Matrix
open scoped NNReal

namespace PositivityTheory.Rg.Sw.AbsSt.Vac

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.AbsSt

instance m2SC (n : ℕ) : SecondCountableTopology (M2 n) :=
  inferInstanceAs (SecondCountableTopology (Fin n ⊕ Fin n → Fin n ⊕ Fin n → ℂ))

theorem kr_inv_val (n : ℕ) (k : KR n) : (((k : GR n) : GL (Fin n ⊕ Fin n) ℂ)⁻¹).val = (mR (k : GR n))ᴴ := by
  have hk : (mR (k : GR n))ᴴ * mR (k : GR n) = 1 := (show InK (mR (k : GR n)) from k.2).2
  have hu : mR (k : GR n) * (((k : GR n) : GL (Fin n ⊕ Fin n) ℂ)⁻¹).val = 1 := Units.mul_inv _
  calc (((k : GR n) : GL (Fin n ⊕ Fin n) ℂ)⁻¹).val
      = (mR (k : GR n))ᴴ * mR (k : GR n) * (((k : GR n) : GL (Fin n ⊕ Fin n) ℂ)⁻¹).val := by
        rw [hk, one_mul]
    _ = (mR (k : GR n))ᴴ := by rw [mul_assoc, hu, mul_one]

theorem kr_inducing (n : ℕ) : Topology.IsInducing (fun k : KR n => mR (k : GR n)) := by
  have hemb : Topology.IsInducing
      (fun k : KR n => Units.embedProduct _ ((k : GR n) : GL (Fin n ⊕ Fin n) ℂ)) :=
    Units.isEmbedding_embedProduct.isInducing.comp
      (Topology.IsInducing.subtypeVal.comp Topology.IsInducing.subtypeVal)
  refine Topology.IsInducing.of_comp (g := fun M : M2 n => (M, MulOpposite.op Mᴴ)) ?_ ?_ ?_
  · exact Units.continuous_val.comp (continuous_subtype_val.comp continuous_subtype_val)
  · exact continuous_id.prodMk (MulOpposite.continuous_op.comp continuous_id.matrix_conjTranspose)
  · convert hemb using 1
    funext k
    show (mR (k : GR n), MulOpposite.op (mR (k : GR n))ᴴ) =
      (((k : GR n) : GL (Fin n ⊕ Fin n) ℂ).val,
        MulOpposite.op (((k : GR n) : GL (Fin n ⊕ Fin n) ℂ)⁻¹).val)
    rw [kr_inv_val]
    rfl

instance krSC (n : ℕ) : SecondCountableTopology (KR n) := (kr_inducing n).secondCountableTopology

theorem spherical_section_ne_zero (hD : CayleyBlocksInvertible) {n : ℕ} (p q : ℕ) (e : ℤ) (g : GR n) : F0 p q e g ≠ 0 := by
  have hne : (mR g).det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).mp (Units.isUnit (g : GL (Fin n ⊕ Fin n) ℂ))).ne_zero
  unfold F0 f0
  exact mul_ne_zero (zpow_ne_zero _ hne) (mul_ne_zero (zpow_ne_zero _ (hD n g).1) (zpow_ne_zero _ (hD n g).2))

variable {m n : ℕ} {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {ε : Fin m → Bool} {c t : ℝ} {p q : ℕ} {e : ℤ} {sL : PX m n →ₗ[ℂ] (GR n → ℂ)}
  {ρ : GR n → PX m n →ₗ[ℂ] PX m n} {Pp Γ : Subgroup G} {ι : GR n →* G} {s₀ : ℂ} {Ht : G → ℝ≥0}
  {sec I : PX m n →ₗ[ℂ] (G → ℂ)} {Λ : Set ((G → ℂ) → ℂ)}

theorem continuous_arg (hιc : Continuous ι) {a b : GR n} {nb : (Fin n → Fin n → ℝ) → GR n} (hnbc : Continuous nb)
    (g : G) : Continuous (fun y : KR n × (Fin n → Fin n → ℝ) => g * ι ((y.1 : GR n) * a * nb y.2 * b)) := by
  have h1 : Continuous (fun y : KR n × (Fin n → Fin n → ℝ) => (y.1 : GR n) * a * nb y.2 * b) :=
    (((continuous_subtype_val.comp continuous_fst).mul continuous_const).mul (hnbc.comp continuous_snd)).mul
      continuous_const
  exact continuous_const.mul (hιc.comp h1)

private theorem integrable_integral_mul_of_continuous_uncurry [MeasurableSpace (KR n)] [BorelSpace (KR n)] [CompactSpace (KR n)]
    (μ : Measure (KR n)) [IsFiniteMeasure μ] (hD : CayleyBlocksInvertible) {ψ : (Fin n → Fin n → ℝ) → ℂ} (hψc : Continuous ψ)
    (hψs : HasCompactSupport ψ) (Φ : KR n → (Fin n → Fin n → ℝ) → ℂ) (hΦ : Continuous (Function.uncurry Φ)) :
    (∀ k : KR n, Integrable (fun x => Φ k x * ψ x)) ∧
    Continuous (fun k : KR n => ∫ x, Φ k x * ψ x) ∧
    Integrable (fun k : KR n => (F0 p q e (k : GR n))⁻¹ * ∫ x, Φ k x * ψ x) μ := by
  have hint : ∀ k : KR n, Integrable (fun x => Φ k x * ψ x) := fun k =>
    ((hΦ.comp (Continuous.prodMk continuous_const continuous_id)).mul hψc).integrable_of_hasCompactSupport
      hψs.mul_left
  have hcont : Continuous (fun k : KR n => ∫ x, Φ k x * ψ x) := by
    have h := continuous_parametric_integral_of_continuous (μ := (volume : Measure (Fin n → Fin n → ℝ)))
      (f := fun k x => Φ k x * ψ x) (hΦ.mul (hψc.comp continuous_snd)) hψs.isCompact
    refine h.congr fun k => ?_
    exact setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
      simp [image_eq_zero_of_notMem_tsupport hx]
  refine ⟨hint, hcont, ?_⟩
  have hF0 : Continuous (fun k : KR n => (F0 p q e (k : GR n))⁻¹) :=
    ((continuous_weight_factor hD p q e).comp continuous_subtype_val).inv₀ fun k => spherical_section_ne_zero hD p q e _
  exact (hF0.mul hcont).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

theorem top_integrable [MeasurableSpace (KR n)] [BorelSpace (KR n)] [CompactSpace (KR n)] (μ : Measure (KR n))
    [IsFiniteMeasure μ] (hD : CayleyBlocksInvertible) (hιc : Continuous ι) {a b : GR n} {nb : (Fin n → Fin n → ℝ) → GR n}
    (hnbc : Continuous nb) {ψ : (Fin n → Fin n → ℝ) → ℂ} (hψc : Continuous ψ) (hψs : HasCompactSupport ψ)
    (F : G → ℂ) (hF : Continuous F) (g : G) :
    (∀ k : KR n, Integrable (fun x => F (g * ι ((k : GR n) * a * nb x * b)) * ψ x)) ∧
    Continuous (fun k : KR n => ∫ x, F (g * ι ((k : GR n) * a * nb x * b)) * ψ x) ∧
    Integrable (fun k : KR n => (F0 p q e (k : GR n))⁻¹ * ∫ x, F (g * ι ((k : GR n) * a * nb x * b)) * ψ x) μ := by
  exact integrable_integral_mul_of_continuous_uncurry μ hD hψc hψs (fun k x => F (g * ι ((k : GR n) * a * nb x * b)))
    (hF.comp (continuous_arg hιc hnbc g))

theorem top_linear [MeasurableSpace (KR n)] [BorelSpace (KR n)] [CompactSpace (KR n)] (μ : Measure (KR n))
    [IsFiniteMeasure μ] (hD : CayleyBlocksInvertible) (hιc : Continuous ι) {a b : GR n} {nb : (Fin n → Fin n → ℝ) → GR n}
    (hnbc : Continuous nb) {ψ : (Fin n → Fin n → ℝ) → ℂ} (hψc : Continuous ψ) (hψs : HasCompactSupport ψ)
    (F F' : G → ℂ) (hF : Continuous F) (hF' : Continuous F') (a' : ℂ) (g : G) :
    Top μ ι p q e a b nb ψ (fun x => a' * F x + F' x) g = a' * Top μ ι p q e a b nb ψ F g + Top μ ι p q e a b nb ψ F' g := by
  obtain ⟨hi1, -, ho1⟩ := top_integrable (p := p) (q := q) (e := e) μ hD hιc hnbc hψc hψs F hF g
  obtain ⟨hi2, -, ho2⟩ := top_integrable (p := p) (q := q) (e := e) μ hD hιc hnbc hψc hψs F' hF' g
  have hin : ∀ k : KR n, ∫ x, (a' * F (g * ι ((k : GR n) * a * nb x * b)) + F' (g * ι ((k : GR n) * a * nb x * b))) * ψ x =
      a' * (∫ x, F (g * ι ((k : GR n) * a * nb x * b)) * ψ x) + ∫ x, F' (g * ι ((k : GR n) * a * nb x * b)) * ψ x := by
    intro k
    rw [← integral_const_mul, ← integral_add ((hi1 k).const_mul a') (hi2 k)]
    congr 1
    funext x
    ring
  unfold Top
  simp only [hin]
  rw [← integral_const_mul, ← integral_add (ho1.const_mul a') ho2]
  congr 1
  funext k
  ring

theorem top_hol [MeasurableSpace (KR n)] [BorelSpace (KR n)] [CompactSpace (KR n)] (μ : Measure (KR n))
    [IsFiniteMeasure μ] (hD : CayleyBlocksInvertible) (hHP : HolParam) (hιc : Continuous ι) {a b : GR n}
    {nb : (Fin n → Fin n → ℝ) → GR n} (hnbc : Continuous nb) {ψ : (Fin n → Fin n → ℝ) → ℂ} (hψc : Continuous ψ)
    (hψs : HasCompactSupport ψ) {U : Set ℂ} (hU : IsOpen U) (E : ℂ → G → ℂ)
    (hEc : ContinuousOn (fun y : ℂ × G => E y.1 y.2) (U ×ˢ univ)) (hEh : ∀ g, DifferentiableOn ℂ (fun z => E z g) U)
    (g : G) : DifferentiableOn ℂ (fun z => Top μ ι p q e a b nb ψ (E z) g) U := by
  have hK : IsCompact (tsupport ψ) := hψs
  haveI : IsFiniteMeasure ((volume : Measure (Fin n → Fin n → ℝ)).restrict (tsupport ψ)) :=
    isFiniteMeasure_restrict.mpr hK.measure_lt_top.ne
  have hF0 : Continuous (fun k : KR n => (F0 p q e (k : GR n))⁻¹) :=
    ((continuous_weight_factor hD p q e).comp continuous_subtype_val).inv₀ fun k => spherical_section_ne_zero hD p q e _
  have harg := continuous_arg (a := a) (b := b) hιc hnbc g
  have hC : IsCompact (univ ×ˢ tsupport ψ : Set (KR n × (Fin n → Fin n → ℝ))) := isCompact_univ.prod hK
  have hCc : (μ.prod ((volume : Measure (Fin n → Fin n → ℝ)).restrict (tsupport ψ)))
      (univ ×ˢ tsupport ψ : Set (KR n × (Fin n → Fin n → ℝ)))ᶜ = 0 := by
    have hc : (univ ×ˢ tsupport ψ : Set (KR n × (Fin n → Fin n → ℝ)))ᶜ = univ ×ˢ (tsupport ψ)ᶜ := by
      ext y
      simp
    rw [hc, Measure.prod_prod, Measure.restrict_apply' (isClosed_tsupport ψ).measurableSet,
      compl_inter_self, measure_empty, mul_zero]
  have hΦc : ContinuousOn (fun y : (KR n × (Fin n → Fin n → ℝ)) × ℂ =>
      (F0 p q e (y.1.1 : GR n))⁻¹ * (E y.2 (g * ι ((y.1.1 : GR n) * a * nb y.1.2 * b)) * ψ y.1.2))
      ((univ ×ˢ tsupport ψ) ×ˢ U) := by
    have h1 : ContinuousOn (fun y : (KR n × (Fin n → Fin n → ℝ)) × ℂ =>
        E y.2 (g * ι ((y.1.1 : GR n) * a * nb y.1.2 * b))) ((univ ×ˢ tsupport ψ) ×ˢ U) :=
      hEc.comp (continuous_snd.prodMk (harg.comp continuous_fst)).continuousOn
        (fun y hy => ⟨hy.2, mem_univ _⟩)
    exact (hF0.comp (continuous_fst.comp continuous_fst)).continuousOn.mul
      (h1.mul (hψc.comp (continuous_snd.comp continuous_fst)).continuousOn)
  have hΦd : ∀ y ∈ (univ ×ˢ tsupport ψ : Set (KR n × (Fin n → Fin n → ℝ))),
      DifferentiableOn ℂ (fun z => (F0 p q e (y.1 : GR n))⁻¹ * (E z (g * ι ((y.1 : GR n) * a * nb y.2 * b)) * ψ y.2)) U :=
    fun y _ => ((hEh _).mul_const (ψ y.2)).const_mul _
  obtain ⟨hdiff, -⟩ := hHP (KR n × (Fin n → Fin n → ℝ))
    (μ.prod ((volume : Measure (Fin n → Fin n → ℝ)).restrict (tsupport ψ))) (univ ×ˢ tsupport ψ) hC hCc U
    (fun y z => (F0 p q e (y.1 : GR n))⁻¹ * (E z (g * ι ((y.1 : GR n) * a * nb y.2 * b)) * ψ y.2)) hU hΦc hΦd
  refine hdiff.congr fun z hz => ?_
  have hcz : Continuous (fun y : KR n × (Fin n → Fin n → ℝ) =>
      (F0 p q e (y.1 : GR n))⁻¹ * (E z (g * ι ((y.1 : GR n) * a * nb y.2 * b)) * ψ y.2)) :=
    (hF0.comp continuous_fst).mul
      ((hEc.comp_continuous (continuous_const.prodMk harg) (fun y => ⟨hz, mem_univ _⟩)).mul
        (hψc.comp continuous_snd))
  have hint : Integrable (fun y : KR n × (Fin n → Fin n → ℝ) =>
      (F0 p q e (y.1 : GR n))⁻¹ * (E z (g * ι ((y.1 : GR n) * a * nb y.2 * b)) * ψ y.2))
      (μ.prod ((volume : Measure (Fin n → Fin n → ℝ)).restrict (tsupport ψ))) := by
    have hae : ∀ᵐ y ∂(μ.prod ((volume : Measure (Fin n → Fin n → ℝ)).restrict (tsupport ψ))),
        y ∈ (univ ×ˢ tsupport ψ : Set (KR n × (Fin n → Fin n → ℝ))) := ae_iff.2 hCc
    rw [← Measure.restrict_eq_self_of_ae_mem hae]
    exact hcz.continuousOn.integrableOn_compact hC
  rw [integral_prod _ hint]
  unfold Top
  refine integral_congr_ae (ae_of_all _ fun k => ?_)
  simp only
  rw [integral_const_mul, setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
    simp [image_eq_zero_of_notMem_tsupport hx]]

theorem continuous_hz_translate (hL : LocData ε c t p q e sL ρ) (hG : GlobData ε c sL ρ G Pp Γ ι s₀ Ht sec I Λ)
    (hD : CayleyBlocksInvertible) (z : ℂ) (g0 : G) : Continuous (fun w : GR n => hz Ht sec s₀ z (g0 * ι w)) := by
  obtain ⟨y, K, r, -, hs⟩ := hz_split hL hG g0
  simp_rw [hs z]
  have hyw : Continuous (fun w : GR n => y * w) := continuous_const.mul continuous_id
  refine continuous_const.mul (Continuous.mul ?_ ((continuous_weight_factor hD p q e).comp hyw))
  exact Continuous.cpow (Complex.continuous_ofReal.comp ((continuous_hLoc hD).comp hyw)) continuous_const
    fun w => Complex.ofReal_mem_slitPlane.mpr (hLoc_pos hD _)

theorem top_sum [MeasurableSpace (KR n)] [BorelSpace (KR n)] [CompactSpace (KR n)] (μ : Measure (KR n))
    [IsFiniteMeasure μ] (hL : LocData ε c t p q e sL ρ) (hG : GlobData ε c sL ρ G Pp Γ ι s₀ Ht sec I Λ) (hD : CayleyBlocksInvertible)
    (hιc : Continuous ι) {a b : GR n} {nb : (Fin n → Fin n → ℝ) → GR n} (hnbc : Continuous nb)
    {ψ : (Fin n → Fin n → ℝ) → ℂ} (hψc : Continuous ψ) (hψs : HasCompactSupport ψ) {cz : ℂ → ℂ}
    (hceig : ∀ (w : ℂ) (y : GR n), ∫ k : KR n, (F0 p q e (k : GR n))⁻¹ * (∫ x, ((hLoc (y * (k : GR n) * a * nb x * b) : ℂ) ^ w *
        F0 p q e (y * (k : GR n) * a * nb x * b)) * ψ x) ∂μ = cz w * ((hLoc y : ℂ) ^ w * F0 p q e y))
    (z : ℂ) (hmaj : ∀ C : Set G, IsCompact C → ∃ u : GlobalTheory.Eis.Cosets Pp Γ → ℝ, Summable u ∧ ∀ g ∈ C, ∀ j,
        ‖GlobalTheory.Eis.term Pp Γ (hz Ht sec s₀ z) g j‖ ≤ u j) (g : G) :
    Top μ ι p q e a b nb ψ (fun x => GlobalTheory.Eis.cosetSum Pp Γ (hz Ht sec s₀ z) x) g =
      cz (z - s₀) * GlobalTheory.Eis.cosetSum Pp Γ (hz Ht sec s₀ z) g := by
  classical
  have hK : IsCompact (tsupport ψ) := hψs
  have hw : Continuous (fun y : KR n × (Fin n → Fin n → ℝ) => ((y.1 : GR n) * a * nb y.2 * b)) :=
    (((continuous_subtype_val.comp continuous_fst).mul continuous_const).mul (hnbc.comp continuous_snd)).mul
      continuous_const
  have harg := continuous_arg (a := a) (b := b) hιc hnbc g
  have hC : IsCompact (insert g ((fun y : KR n × (Fin n → Fin n → ℝ) =>
      g * ι ((y.1 : GR n) * a * nb y.2 * b)) '' (univ ×ˢ tsupport ψ))) :=
    ((isCompact_univ.prod hK).image harg).insert g
  obtain ⟨u, hu, hub⟩ := hmaj _ hC
  haveI : Countable (Function.support u) := hu.countable_support.to_subtype
  have hmemC : ∀ (k : KR n) (x : Fin n → Fin n → ℝ), x ∈ tsupport ψ →
      g * ι ((k : GR n) * a * nb x * b) ∈ insert g ((fun y : KR n × (Fin n → Fin n → ℝ) =>
        g * ι ((y.1 : GR n) * a * nb y.2 * b)) '' (univ ×ˢ tsupport ψ)) :=
    fun k x hx => mem_insert_of_mem _ ⟨(k, x), ⟨mem_univ _, hx⟩, rfl⟩
  have hsumS : ∀ g' ∈ insert g ((fun y : KR n × (Fin n → Fin n → ℝ) =>
        g * ι ((y.1 : GR n) * a * nb y.2 * b)) '' (univ ×ˢ tsupport ψ)),
      GlobalTheory.Eis.cosetSum Pp Γ (hz Ht sec s₀ z) g' =
        ∑' j : Function.support u, GlobalTheory.Eis.term Pp Γ (hz Ht sec s₀ z) g' j := by
    intro g' hg'
    refine (tsum_subtype_eq_of_support_subset fun j hj => ?_).symm
    by_contra h
    have h2 := hub g' hg' j
    rw [Function.notMem_support.mp h] at h2
    exact hj (norm_le_zero_iff.mp h2)
  have hterm : ∀ j : GlobalTheory.Eis.Cosets Pp Γ, Continuous (Function.uncurry fun (k : KR n) (x : Fin n → Fin n → ℝ) =>
      GlobalTheory.Eis.term Pp Γ (hz Ht sec s₀ z) (g * ι ((k : GR n) * a * nb x * b)) j) := by
    intro j
    refine ((continuous_hz_translate hL hG hD z (((Quotient.out j : Γ) : G) * g)).comp hw).congr ?_
    rintro ⟨k, x⟩
    simp only [GlobalTheory.Eis.term, Function.comp_apply, Function.uncurry_apply_pair, mul_assoc]
  have hbd : ∀ (j : GlobalTheory.Eis.Cosets Pp Γ) (k : KR n) (x : Fin n → Fin n → ℝ),
      ‖GlobalTheory.Eis.term Pp Γ (hz Ht sec s₀ z) (g * ι ((k : GR n) * a * nb x * b)) j * ψ x‖ ≤ u j * ‖ψ x‖ := by
    intro j k x
    rw [norm_mul]
    by_cases hx : x ∈ tsupport ψ
    · exact mul_le_mul_of_nonneg_right (hub _ (hmemC k x hx) j) (norm_nonneg _)
    · simp [image_eq_zero_of_notMem_tsupport hx]
  have hI := fun j : Function.support u => integrable_integral_mul_of_continuous_uncurry (p := p) (q := q) (e := e) μ hD hψc hψs
    (fun (k : KR n) (x : Fin n → Fin n → ℝ) =>
      GlobalTheory.Eis.term Pp Γ (hz Ht sec s₀ z) (g * ι ((k : GR n) * a * nb x * b)) j) (hterm j)
  have hψi : Integrable (fun x => ‖ψ x‖) := hψc.norm.integrable_of_hasCompactSupport hψs.norm
  have hIb : ∀ (j : Function.support u) (k : KR n),
      ∫ x, ‖GlobalTheory.Eis.term Pp Γ (hz Ht sec s₀ z) (g * ι ((k : GR n) * a * nb x * b)) j * ψ x‖ ≤
        u j * ∫ x, ‖ψ x‖ := by
    intro j k
    rw [← integral_const_mul]
    exact integral_mono ((hI j).1 k).norm (hψi.const_mul _) fun x => hbd j k x
  have hin : ∀ k : KR n,
      (F0 p q e (k : GR n))⁻¹ * ∫ x, GlobalTheory.Eis.cosetSum Pp Γ (hz Ht sec s₀ z) (g * ι ((k : GR n) * a * nb x * b)) * ψ x =
        ∑' j : Function.support u, (F0 p q e (k : GR n))⁻¹ *
          ∫ x, GlobalTheory.Eis.term Pp Γ (hz Ht sec s₀ z) (g * ι ((k : GR n) * a * nb x * b)) j * ψ x := by
    intro k
    have hpt : ∀ x, GlobalTheory.Eis.cosetSum Pp Γ (hz Ht sec s₀ z) (g * ι ((k : GR n) * a * nb x * b)) * ψ x =
        ∑' j : Function.support u, GlobalTheory.Eis.term Pp Γ (hz Ht sec s₀ z) (g * ι ((k : GR n) * a * nb x * b)) j * ψ x := by
      intro x
      rw [tsum_mul_right]
      by_cases hx : x ∈ tsupport ψ
      · rw [hsumS _ (hmemC k x hx)]
      · simp [image_eq_zero_of_notMem_tsupport hx]
    rw [tsum_mul_left]
    congr 1
    simp_rw [hpt]
    refine (integral_tsum_of_summable_integral_norm (fun j => (hI j).1 k) ?_).symm
    exact Summable.of_nonneg_of_le (fun j => integral_nonneg fun x => norm_nonneg _) (fun j => hIb j k)
      ((hu.subtype _).mul_right _)
  obtain ⟨M, hM⟩ : ∃ M, ∀ k : KR n, ‖(F0 p q e (k : GR n))⁻¹‖ ≤ M := by
    have hF0 : Continuous (fun k : KR n => (F0 p q e (k : GR n))⁻¹) :=
      ((continuous_weight_factor hD p q e).comp continuous_subtype_val).inv₀ fun k => spherical_section_ne_zero hD p q e _
    obtain ⟨M, hM⟩ := isCompact_univ.exists_bound_of_continuousOn hF0.continuousOn
    exact ⟨M, fun k => hM k (mem_univ _)⟩
  have hj : ∀ j : Function.support u, ∫ k : KR n, (F0 p q e (k : GR n))⁻¹ *
      (∫ x, GlobalTheory.Eis.term Pp Γ (hz Ht sec s₀ z) (g * ι ((k : GR n) * a * nb x * b)) j * ψ x) ∂μ =
        cz (z - s₀) * GlobalTheory.Eis.term Pp Γ (hz Ht sec s₀ z) g j := by
    intro j
    have h := top_hz (a := a) (b := b) (nb := nb) (ψ := ψ) μ hL hG hceig z
      (((Quotient.out (j : GlobalTheory.Eis.Cosets Pp Γ) : Γ) : G) * g)
    unfold Top at h
    simp only [GlobalTheory.Eis.term, mul_assoc] at h ⊢
    exact h
  unfold Top
  simp only [hin]
  rw [← integral_tsum_of_summable_integral_norm (fun j => (hI j).2.2)]
  · simp only [hj, tsum_mul_left]
    rw [hsumS g (mem_insert _ _)]
  · refine Summable.of_nonneg_of_le (fun j => integral_nonneg fun k => norm_nonneg _) (fun j => ?_)
      ((((hu.subtype _).mul_right (∫ x, ‖ψ x‖)).mul_left M).mul_right (∫ k : KR n, (1 : ℝ) ∂μ))
    calc ∫ k, ‖(F0 p q e (k : GR n))⁻¹ *
          ∫ x, GlobalTheory.Eis.term Pp Γ (hz Ht sec s₀ z) (g * ι ((k : GR n) * a * nb x * b)) j * ψ x‖ ∂μ
        ≤ ∫ k : KR n, M * (u j * ∫ x, ‖ψ x‖) * 1 ∂μ := by
          refine integral_mono (hI j).2.2.norm (integrable_const _) fun k => ?_
          rw [norm_mul, mul_one]
          exact mul_le_mul (hM k) ((norm_integral_le_integral_norm _).trans (hIb j k)) (norm_nonneg _)
            ((norm_nonneg _).trans (hM k))
      _ = M * (u j * ∫ x, ‖ψ x‖) * ∫ k : KR n, (1 : ℝ) ∂μ := integral_const_mul _ _

end PositivityTheory.Rg.Sw.AbsSt.Vac
