import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LrActScalar
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DetConsColNeZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HformMulVecRight
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FibreFamilyHermitianQuadraticFormAtUnitProps
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FibreMeasureInvariantSupportedOrbitNeZeroStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitaryStabilizerAnisotropicVectorEquivComplemen
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwoStepPairMeasureFiniteOnCompacts
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousDistribHaarCharUnits
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TensorNiceRingArtinianReducedOpenUnits

open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal

noncomputable section

namespace GlobalTheory.GaugeEx.GramDensity

theorem lintegral_tup_two {S : Type} [MeasurableSpace S] (lam : Measure S) [SigmaFinite lam] (M : ℕ)
    (f : (Fin 2 → Fin M → S) → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ X, f X ∂(tupMeas lam 2 M) =
      ∫⁻ y, ∫⁻ z, f ![y 0, z] ∂(Measure.pi fun _ => lam) ∂(tupMeas lam 1 M) := by
  have h2 := (measurePreserving_finTwoArrow (Measure.pi fun _ : Fin M => lam)).symm
  have h1 := measurePreserving_funUnique (Measure.pi fun _ : Fin M => lam) (Fin 1)
  unfold tupMeas
  rw [← h2.lintegral_comp hf, lintegral_prod (fun a => f (MeasurableEquiv.finTwoArrow.symm a))
      (hf.comp h2.measurable).aemeasurable,
    ← h1.lintegral_comp_emb (MeasurableEquiv.measurableEmbedding _)]
  rfl

theorem continuousOn_integral_param {P X : Type} [TopologicalSpace P] [TopologicalSpace X] [T2Space X]
    [MeasurableSpace X] [OpensMeasurableSpace X] (N : Measure X) [IsFiniteMeasureOnCompacts N]
    {C : Set P} (hC : IsCompact C) (Ψ Ψ' : P → X → X)
    (hΨ : ContinuousOn (Function.uncurry Ψ) (C ×ˢ Set.univ))
    (hΨ' : ContinuousOn (Function.uncurry Ψ') (C ×ˢ Set.univ))
    (hinv : ∀ p ∈ C, ∀ x, Ψ' p (Ψ p x) = x) (φ : X → ℝ) (hφ : Continuous φ)
    (hs : HasCompactSupport φ) :
    ContinuousOn (fun p => ∫ x, φ (Ψ p x) ∂N) C ∧ ∀ p ∈ C, Integrable (fun x => φ (Ψ p x)) N := by
  have hk : IsCompact (Function.uncurry Ψ' '' (C ×ˢ tsupport φ)) :=
    (hC.prod hs).image_of_continuousOn (hΨ'.mono (Set.prod_mono le_rfl (Set.subset_univ _)))
  have hz : ∀ p x, p ∈ C → x ∉ Function.uncurry Ψ' '' (C ×ˢ tsupport φ) → φ (Ψ p x) = 0 := by
    intro p x hp hx
    by_contra h
    exact hx ⟨(p, Ψ p x), ⟨hp, subset_tsupport _ h⟩, hinv p hp x⟩
  refine ⟨continuousOn_integral_of_compact_support (f := fun p x => φ (Ψ p x)) hk
    (hφ.comp_continuousOn hΨ) hz, fun p hp => ?_⟩
  have hc : Continuous fun x => φ (Ψ p x) := by
    refine hφ.comp ?_
    have := hΨ.comp_continuous (f := fun x => (p, x)) (by fun_prop) (fun x => ⟨hp, trivial⟩)
    exact this
  exact hc.integrable_of_hasCompactSupport (HasCompactSupport.intro hk fun x hx => hz p x hp hx)

theorem isOpen_isUnit {R : Type} [CommRing R] [TopologicalSpace R] (h : IsOpenUnits R) :
    IsOpen {u : R | IsUnit u} := (IsOpenUnits.isOpenEmbedding_unitsVal (M := R)).isOpen_range

theorem continuousOn_ringInverse {R : Type} [CommRing R] [TopologicalSpace R] (h : IsOpenUnits R) :
    ContinuousOn (Ring.inverse : R → R) {u : R | IsUnit u} := by
  rintro _ ⟨u, rfl⟩
  refine ContinuousAt.continuousWithinAt ?_
  rw [← (IsOpenUnits.isOpenEmbedding_unitsVal (M := R)).continuousAt_iff]
  have : (Ring.inverse : R → R) ∘ (Units.val : Rˣ → R) = fun u => ((u⁻¹ : Rˣ) : R) := by
    funext u; simp
  rw [this]
  exact Units.continuous_coe_inv.continuousAt

theorem exists_root {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [MeasurableSpace R] [BorelSpace R] (h : Nice R) {β : R} (hβ : IsUnit β) :
    ∃ (W : Set R) (ρ : R → R), IsOpen W ∧ β ∈ W ∧ Measurable ρ ∧ ContinuousOn ρ W ∧ ρ β = 1 ∧
      ∀ b ∈ W, IsUnit (ρ b) ∧ ρ b * ρ b * β = b := by
  classical
  obtain ⟨-, -, ho, U, hU, h1, s, hs, hs1, hss⟩ := h
  obtain ⟨v, rfl⟩ := hβ
  set W : Set R := (fun b => b * ((v⁻¹ : Rˣ) : R)) ⁻¹' U ∩ {u | IsUnit u} with hW
  have hWo : IsOpen W := (hU.preimage (by fun_prop)).inter (isOpen_isUnit ho)
  have hc : ContinuousOn (fun b => s (b * ((v⁻¹ : Rˣ) : R))) W :=
    hs.comp (by fun_prop) fun b hb => hb.1
  have hv : (v : R) ∈ W := ⟨by simpa using h1, v.isUnit⟩
  refine ⟨W, W.piecewise (fun b => s (b * ((v⁻¹ : Rˣ) : R))) (fun _ => 0), hWo, hv,
    hc.measurable_piecewise continuousOn_const hWo.measurableSet,
    hc.congr fun b hb => Set.piecewise_eq_of_mem _ _ _ hb, ?_, fun b hb => ?_⟩
  · rw [Set.piecewise_eq_of_mem _ _ _ hv]; simpa using hs1
  · rw [Set.piecewise_eq_of_mem _ _ _ hb]
    have e := hss _ hb.1
    refine ⟨?_, by rw [e]; simp⟩
    have : IsUnit (s (b * ((v⁻¹ : Rˣ) : R)) * s (b * ((v⁻¹ : Rˣ) : R))) := by
      rw [e]; exact IsUnit.mul hb.2 (Units.isUnit _)
    exact isUnit_of_mul_isUnit_left this

theorem measurable_modu (S : Type) [CommRing S] [TopologicalSpace S] [IsTopologicalRing S] [T2Space S]
    [LocallyCompactSpace S] [SecondCountableTopology S] [MeasurableSpace S] [BorelSpace S]
    (h : IsOpenUnits S) : Measurable (modu S) := by
  classical
  have hc := (GlobalTheory.GaugeEx.modu_basic S).2.2.2 h
  have := hc.measurable_piecewise (g := fun _ => 0) continuousOn_const (isOpen_isUnit h).measurableSet
  convert this using 1
  funext u
  by_cases hu : IsUnit u
  · simp [Set.piecewise, hu]
  · simp [Set.piecewise, modu, hu]

theorem lintegral_scale {S : Type} [CommRing S] [TopologicalSpace S] [IsTopologicalRing S] [T2Space S]
    [LocallyCompactSpace S] [SecondCountableTopology S] [MeasurableSpace S] [BorelSpace S]
    (lam : Measure S) (hl : lam.IsAddHaarMeasure) {u : S} (hu : IsUnit u) (G : S → ℝ≥0∞) :
    ∫⁻ t, G t ∂lam = (modu S u : ℝ≥0∞) * ∫⁻ t, G (u * t) ∂lam := by
  have e := ((GlobalTheory.GaugeEx.modu_basic S).1 u hu).2 lam hl
  obtain ⟨v, rfl⟩ := hu
  have hm : MeasurableEmbedding (fun z : S => (v : S) * z) :=
    (Homeomorph.smul v).measurableEmbedding
  conv_lhs => rw [e]
  rw [lintegral_smul_measure, hm.lintegral_map]
  rfl

def psi {S : Type} [CommRing S] {M : ℕ} (r t r' : S) (X : Fin 2 → Fin M → S) : Fin 2 → Fin M → S :=
  ![r • X 0, t • X 0 + r' • X 1]

theorem continuous_psi {S : Type} [CommRing S] [TopologicalSpace S] [IsTopologicalRing S] {M : ℕ} :
    Continuous fun p : (S × S × S) × (Fin 2 → Fin M → S) => psi p.1.1 p.1.2.1 p.1.2.2 p.2 := by
  refine continuous_pi fun a => ?_
  fin_cases a
  · simp only [psi, Fin.zero_eta, Matrix.cons_val_zero]; fun_prop
  · simp only [psi, Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero]; fun_prop

theorem psi_inv {S : Type} [CommRing S] {M : ℕ} {r t r' k k' : S} (h : k * r = 1) (h' : k' * r' = 1)
    (X : Fin 2 → Fin M → S) : psi k (-(k' * t * k)) k' (psi r t r' X) = X := by
  funext a i
  fin_cases a
  · simp [psi, ← mul_assoc, h]
  · simp only [psi, Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul]
    linear_combination (-(k' * t * X 0 i)) * h + X 1 i * h'

theorem psi_one {S : Type} [CommRing S] {M : ℕ} (X : Fin 2 → Fin M → S) : psi 1 0 1 X = X := by
  funext a
  fin_cases a <;> simp [psi]

section Main

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
  (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R] [T2Space R]
  [LocallyCompactSpace R] [SecondCountableTopology R] [MeasurableSpace R] [BorelSpace R]

omit [T2Space R] [LocallyCompactSpace R] [SecondCountableTopology R] [MeasurableSpace R] [BorelSpace R] in
theorem continuous_pairOf {M : ℕ} (J : Matrix (Fin (M + 1)) (Fin (M + 1)) E)
    (B : Matrix (Fin (M + 1)) (Fin M) E) (y : Fin 1 → Fin (M + 1) → (R ⊗[F] E)) (g : HA R σ J) :
    Continuous (pairOf R σ J B y g) := by
  refine continuous_pi fun a => ?_
  fin_cases a
  · exact continuous_const
  · have h0 : Continuous fun y' : Fin 1 → Fin M → (R ⊗[F] E) => (B.map (inclR R)).mulVec (y' 0) :=
      continuous_const.matrix_mulVec (continuous_apply 0)
    have h1 : Continuous fun y' : Fin 1 → Fin M → (R ⊗[F] E) =>
        ((HA.mat R σ J g : GL (Fin (M + 1)) (R ⊗[F] E)) : Matrix (Fin (M + 1)) (Fin (M + 1)) (R ⊗[F] E)).mulVec
          ((B.map (inclR R)).mulVec (y' 0)) := continuous_const.matrix_mulVec h0
    exact h1

theorem twoStep_param {M : ℕ} {J : Matrix (Fin (M + 1)) (Fin (M + 1)) E} {x : Fin 1 → Fin (M + 1) → E}
    {B : Matrix (Fin (M + 1)) (Fin M) E} {m : Measure (Fin 1 → Fin (M + 1) → (R ⊗[F] E))}
    {m' : Measure (Fin 1 → Fin M → (R ⊗[F] E))} {N : Measure (Fin 2 → Fin (M + 1) → (R ⊗[F] E))}
    [SFinite m'] [SFinite N] (h : TwoStep R σ J x B m m' N) {T : Type} [MeasurableSpace T]
    (τ : Measure T) [SFinite τ] (K : T × (Fin 2 → Fin (M + 1) → (R ⊗[F] E)) → ℝ≥0∞) (hK : Measurable K)
    (s : (Fin 1 → Fin (M + 1) → (R ⊗[F] E)) → HA R σ J) (hs : IsSec R σ J x s) :
    ∫⁻ y, ∫⁻ t, ∫⁻ y', K (t, pairOf R σ J B y (s y) y') ∂m' ∂τ ∂m = ∫⁻ t, ∫⁻ X, K (t, X) ∂N ∂τ := by
  rw [lintegral_lintegral_swap (f := fun t X => K (t, X)) hK.aemeasurable,
    h (fun X => ∫⁻ t, K (t, X) ∂τ) hK.lintegral_prod_left' s hs]
  refine lintegral_congr fun y => ?_
  exact lintegral_lintegral_swap (f := fun t y' => K (t, pairOf R σ J B y (s y) y'))
    (hK.comp (measurable_fst.prodMk
      ((continuous_pairOf σ R J B y (s y)).measurable.comp measurable_snd))).aemeasurable

variable (F E) in

def wt (M : ℕ) (r : R) : ℝ≥0 := modu (R ⊗[F] E) (algebraMap R (R ⊗[F] E) r ^ M) * (modu R (r * r))⁻¹

omit [T2Space R] [LocallyCompactSpace R] [SecondCountableTopology R] [MeasurableSpace R] [BorelSpace R] in
theorem continuous_alg : Continuous (algebraMap R (R ⊗[F] E)) := by
  have : (algebraMap R (R ⊗[F] E) : R → (R ⊗[F] E)) = fun r => r • (1 : (R ⊗[F] E)) := by
    funext r; rw [Algebra.algebraMap_eq_smul_one]
  rw [this]
  fun_prop

theorem measurable_wt (h : Nice R) (M : ℕ) : Measurable (wt F E R M) := by
  have h1 := measurable_modu (R ⊗[F] E) (nice_tensor F E R h).2.2
  have h2 := measurable_modu R h.2.2.1
  have h3 := (continuous_alg (F := F) (E := E) R).measurable
  unfold wt
  exact (h1.comp (h3.pow_const M)).mul (h2.comp (measurable_id.mul measurable_id)).inv

theorem continuousOn_wt (h : Nice R) (M : ℕ) : ContinuousOn (wt F E R M) {r | IsUnit r} := by
  have h1 := (modu_basic (R ⊗[F] E)).2.2.2 (nice_tensor F E R h).2.2
  have h2 := (modu_basic R).2.2.2 h.2.2.1
  have h3 := continuous_alg (F := F) (E := E) R
  unfold wt
  refine ContinuousOn.mul (h1.comp (h3.pow M).continuousOn fun r hr => (IsUnit.map _ hr).pow M)
    (ContinuousOn.inv₀ (h2.comp (continuous_id.mul continuous_id).continuousOn
      fun r hr => IsUnit.mul hr hr) fun r hr => ((modu_basic R).1 _ (IsUnit.mul hr hr)).1.ne')

theorem wt_one (M : ℕ) : wt F E R M 1 = 1 := by
  rw [wt, map_one, one_pow, one_mul, (modu_basic (R ⊗[F] E)).2.2.1, (modu_basic R).2.2.1, inv_one, one_mul]

theorem inner_integral (hσ : IsCMExt F E σ) (hR : Nice R) {M : ℕ}
    {J : Matrix (Fin (M + 1)) (Fin (M + 1)) E} {x : Fin 1 → Fin (M + 1) → E} {a : F}
    {B : Matrix (Fin (M + 1)) (Fin M) E} {J' : Matrix (Fin M) (Fin M) E} (hst : StepData σ J x a B J')
    {lam : Measure (R ⊗[F] E)} {ν : Measure R} (hl : lam.IsAddHaarMeasure) (hν : ν.IsAddHaarMeasure)
    {γ : R} (hγ : IsUnit γ) {m' : Measure (Fin 1 → Fin M → (R ⊗[F] E))}
    (hm' : FibAt R σ J' (tupMeas lam 1 M) ν γ m') (hgc : Continuous (gram3 R σ J))
    {n : (R ⊗[F] E) → R}
    (hn : ∀ (g : HA R σ J) (y : Fin 1 → Fin (M + 1) → (R ⊗[F] E)) (y' : Fin 1 → Fin M → (R ⊗[F] E)) (r r' : R) (t : (R ⊗[F] E)),
      g • ratTup (F := F) R x = y →
      gram3 R σ J ![algebraMap R (R ⊗[F] E) r • y 0, t • y 0 + algebraMap R (R ⊗[F] E) r' • pairOf R σ J B y g y' 1] =
        (r * r * algebraMap F R a, algebraMap R (R ⊗[F] E) (r * algebraMap F R a) * t, n t + r' * r' * qR R σ J' (y' 0)))
    {W : Set R} {ρ : R → R} (hW : MeasurableSet W) (hρ : ∀ b ∈ W, IsUnit (ρ b) ∧ ρ b * ρ b * γ = b)
    (φ : (Fin 2 → Fin (M + 1) → (R ⊗[F] E)) → ℝ≥0∞) (hφ : Measurable φ)
    {S : Set (R × (R ⊗[F] E) × R)} (hS : MeasurableSet S) (r b : R) (hb : r * r * algebraMap F R a = b) (u : (R ⊗[F] E))
    (hu : algebraMap R (R ⊗[F] E) (r * algebraMap F R a) * u = 1) (hSW : ∀ t d, (b, t, d) ∈ S → d - n (u * t) ∈ W)
    (g : HA R σ J) (y : Fin 1 → Fin (M + 1) → (R ⊗[F] E)) (hy : g • ratTup (F := F) R x = y) :
    ∫⁻ z, (gram3 R σ J ⁻¹' S).indicator φ ![algebraMap R (R ⊗[F] E) r • y 0, z] ∂(Measure.pi fun _ => lam) =
      (modu (R ⊗[F] E) (inclR R (consCol x B).det) : ℝ≥0∞) * ((modu (R ⊗[F] E) u : ℝ≥0∞) *
      ∫⁻ t, ∫⁻ d, ∫⁻ y', S.indicator 1 (b, t, d) * (wt F E R M (ρ (d - n (u * t))) : ℝ≥0∞) *
        φ (psi (algebraMap R (R ⊗[F] E) r) (u * t) (algebraMap R (R ⊗[F] E) (ρ (d - n (u * t)))) (pairOf R σ J B y g y')) ∂m' ∂ν ∂lam) := by
  have hFi : Measurable ((gram3 R σ J ⁻¹' S).indicator φ) := hφ.indicator (hgc.measurable hS)
  have hc2 : ∀ v : Fin (M + 1) → (R ⊗[F] E), Continuous fun z : Fin (M + 1) → (R ⊗[F] E) => ![v, z] := by
    intro v
    refine continuous_pi fun a => ?_
    fin_cases a
    · exact continuous_const
    · exact continuous_id
  rw [Subst.subst F E σ hσ R hR M J x a B J' hst lam hl g y hy
    (fun z => (gram3 R σ J ⁻¹' S).indicator φ ![algebraMap R (R ⊗[F] E) r • y 0, z]) (hFi.comp (hc2 _).measurable),
    lintegral_scale lam hl (IsUnit.of_mul_eq_one_right _ hu)]
  congr 2
  refine lintegral_congr fun t => ?_
  have hut : algebraMap R (R ⊗[F] E) (r * algebraMap F R a) * (u * t) = t := by rw [← mul_assoc, hu, one_mul]
  rw [Polar.polar F E σ R hR M J' lam ν γ m' hl hν hγ hm' W ρ hW hρ
    (fun y' => (gram3 R σ J ⁻¹' S).indicator φ
      ![algebraMap R (R ⊗[F] E) r • y 0, (u * t) • y 0 + pairOf R σ J B y g y' 1])
    (hFi.comp ((hc2 _).comp (continuous_const.add
      ((continuous_apply 1).comp (continuous_pairOf σ R J B y g)))).measurable) ?_]
  · rw [← lintegral_indicator hW, ← lintegral_sub_right_eq_self _ (n (u * t))]
    refine lintegral_congr fun d => ?_
    by_cases hd : d - n (u * t) ∈ W
    · rw [Set.indicator_of_mem hd, ← lintegral_const_mul' _ _ ENNReal.coe_ne_top]
      have hq : ∀ᵐ y' ∂m', qR R σ J' (y' 0) = γ :=
        (FibBasic.fibAt_basic F E σ R hR M J' _ ν γ m' hν hγ hm').1
      refine lintegral_congr_ae (hq.mono fun y' hy' => ?_)
      have e1 : pairOf R σ J B y g (algebraMap R (R ⊗[F] E) (ρ (d - n (u * t))) • y') 1 =
          algebraMap R (R ⊗[F] E) (ρ (d - n (u * t))) • pairOf R σ J B y g y' 1 := by
        simp [pairOf, Matrix.mulVec_smul]
      have e2 := hn g y y' r (ρ (d - n (u * t))) (u * t) hy
      rw [hb, hut, hy', (hρ _ hd).2, add_sub_cancel] at e2
      simp only [e1]
      by_cases hm : (b, t, d) ∈ S
      · rw [Set.indicator_of_mem hm, Set.indicator_of_mem (by rw [Set.mem_preimage, e2]; exact hm)]
        simp only [Pi.one_apply, one_mul]
        rfl
      · rw [Set.indicator_of_notMem hm, Set.indicator_of_notMem (by rw [Set.mem_preimage, e2]; exact hm)]
        simp
    · rw [Set.indicator_of_notMem hd, Set.indicator_of_notMem fun hm => hd (hSW t d hm)]
      simp
  · intro y' hy'
    refine Set.indicator_of_notMem (fun hm => hy' ?_) _
    have e2 := hn g y y' r 1 (u * t) hy
    rw [hb, hut, map_one, one_smul, one_mul, one_mul] at e2
    rw [Set.mem_preimage, e2] at hm
    simpa using hSW _ _ hm

end Main

set_option maxHeartbeats 1600000 in

theorem gram_density : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R] [T2Space R] [LocallyCompactSpace R] [SecondCountableTopology R] [MeasurableSpace R] [BorelSpace R], Nice R → ∀ (M : ℕ) (J : Matrix (Fin (M + 1)) (Fin (M + 1)) E) (x : Fin 1 → Fin (M + 1) → E) (a : F) (B : Matrix (Fin (M + 1)) (Fin M) E) (J' : Matrix (Fin M) (Fin M) E) (y : Fin 1 → Fin M → E) (c : F) (lam : Measure (R ⊗[F] E)) (ν : Measure R) (m : Measure (Fin 1 → Fin (M + 1) → R ⊗[F] E)) (m' : Measure (Fin 1 → Fin M → R ⊗[F] E)) (N : Measure (Fin 2 → Fin (M + 1) → R ⊗[F] E)), StepData σ J x a B J' → c ≠ 0 → hE σ J' (y 0) (y 0) = algebraMap F E c → lam.IsAddHaarMeasure → ν.IsAddHaarMeasure → FibAt R σ J (tupMeas lam 1 (M + 1)) ν (algebraMap F R a) m → FibAt R σ J' (tupMeas lam 1 M) ν (algebraMap F R c) m' → TwoStep R σ J x B m m' N → ∀ φ : (Fin 2 → Fin (M + 1) → R ⊗[F] E) → ℝ, Continuous φ → HasCompactSupport φ → (∀ X, 0 ≤ φ X) → ∃ (U : Set (R × (R ⊗[F] E) × R)) (D : R × (R ⊗[F] E) × R → ℝ), IsOpen U ∧ (algebraMap F R a, 0, algebraMap F R c) ∈ U ∧ ContinuousOn D U ∧ (∀ t ∈ U, 0 ≤ D t) ∧ (∀ S ⊆ U, MeasurableSet S → ∫⁻ X in gram3 R σ J ⁻¹' S, ENNReal.ofReal (φ X) ∂(tupMeas lam 2 (M + 1)) = ∫⁻ t in S, ENNReal.ofReal (D t) ∂(ν.prod (lam.prod ν))) ∧ D (algebraMap F R a, 0, algebraMap F R c) = (modu (R ⊗[F] E) (inclR R ((consCol x B).det / algebraMap F E a)) : ℝ) * ∫ X, φ X ∂N := by
  intro F E _ _ _ _ _ σ hσ R _ _ _ _ _ _ _ _ _ hR M J x a B J' y₀ c lam ν m m' N hst hc hy₀ hl hν hm hm'
    hN φ hφ hφs hφ0
  classical
  have hα : IsUnit (algebraMap F R a) := (IsUnit.mk0 a hst.2.1).map _
  have hγ : IsUnit (algebraMap F R c) := (IsUnit.mk0 c hc).map _
  obtain ⟨W₁, ρ₁, hW₁, hαW, -, hρ₁c, hρ₁1, hρ₁⟩ := exists_root hR hα
  obtain ⟨W₂, ρ₂, hW₂, hγW, hρ₂m, hρ₂c, hρ₂1, hρ₂⟩ := exists_root hR hγ
  obtain ⟨hgc, n, hnc, hn0, hn⟩ := GramPair.gram_pair F E σ hσ R M J x a B J' hst
  have horb := (GlobalTheory.T.fibreMeasure_invariant_supported_orbit_ne_zero F E σ hσ R hR _ J x a lam ν m hst.1 hst.2.1 hst.2.2.1 hl hν hm).2.1
  have hinv' := (GlobalTheory.T.fibreMeasure_invariant_supported_orbit_ne_zero F E σ hσ R hR _ J' y₀ c lam ν m' hst.2.2.2.2.2 hc hy₀ hl hν hm').1
  haveI hfm := (FibBasic.fibAt_basic F E σ R hR _ J _ ν _ m hν hα hm).2.1
  haveI hfm' := (FibBasic.fibAt_basic F E σ R hR _ J' _ ν _ m' hν hγ hm').2.1
  haveI hfN := twoStep_finite_on_compacts F E σ hσ R hR M J x a B J' m m' N hst horb hfm hfm' hinv' hN
  have hdet := (GlobalTheory.FrameStep.frameStep F E σ hσ R M J x a B J' hst).1
  have hι := continuous_alg (F := F) (E := E) R
  have hri := continuousOn_ringInverse hR.2.2.1
  set α := algebraMap F R a with hαdef
  set γ := algebraMap F R c with hγdef
  set u : R → (R ⊗[F] E) := fun b => algebraMap R (R ⊗[F] E) (Ring.inverse (ρ₁ b * α)) with hudef
  have hu : ∀ b ∈ W₁, algebraMap R (R ⊗[F] E) (ρ₁ b * α) * u b = 1 := fun b hb => by
    rw [hudef, ← map_mul, Ring.mul_inverse_cancel _ ((hρ₁ b hb).1.mul hα), map_one]
  have huc : ContinuousOn u W₁ :=
    hι.comp_continuousOn (hri.comp (hρ₁c.mul continuousOn_const) fun b hb => (hρ₁ b hb).1.mul hα)
  set e : R × (R ⊗[F] E) × R → R := fun T => T.2.2 - n (u T.1 * T.2.1) with hedef
  have htc : ContinuousOn (fun T : R × (R ⊗[F] E) × R => u T.1 * T.2.1) (Prod.fst ⁻¹' W₁) :=
    (huc.comp continuousOn_fst fun T hT => hT).mul (by fun_prop)
  have hec : ContinuousOn e (Prod.fst ⁻¹' W₁) :=
    ContinuousOn.sub (by fun_prop) (hnc.comp_continuousOn htc)
  have he0 : e (α, 0, γ) = γ := by simp [hedef, hn0]
  have hU₀ : IsOpen (Prod.fst ⁻¹' W₁ ∩ e ⁻¹' W₂) :=
    hec.isOpen_inter_preimage (hW₁.preimage continuous_fst) hW₂
  obtain ⟨C, hC, hbase, hCU⟩ := exists_compact_subset hU₀ (x := (α, 0, γ))
    ⟨hαW, by rw [Set.mem_preimage, he0]; exact hγW⟩
  have hC1 : C ⊆ Prod.fst ⁻¹' W₁ := fun T hT => (hCU hT).1
  have hr₁ : ContinuousOn (fun T : R × (R ⊗[F] E) × R => ρ₁ T.1) C :=
    hρ₁c.comp continuousOn_fst fun T hT => hC1 hT
  have hr₂ : ContinuousOn (fun T : R × (R ⊗[F] E) × R => ρ₂ (e T)) C :=
    hρ₂c.comp (hec.mono hC1) fun T hT => (hCU hT).2
  have hu₁ : ∀ T ∈ C, IsUnit (ρ₁ T.1) := fun T hT => (hρ₁ _ (hC1 hT)).1
  have hu₂ : ∀ T ∈ C, IsUnit (ρ₂ (e T)) := fun T hT => (hρ₂ _ (hCU hT).2).1
  have hpsi : ∀ A : R × (R ⊗[F] E) × R → (R ⊗[F] E) × (R ⊗[F] E) × (R ⊗[F] E), ContinuousOn A C → ContinuousOn
      (Function.uncurry fun T (X : Fin 2 → Fin (M + 1) → (R ⊗[F] E)) => psi (A T).1 (A T).2.1 (A T).2.2 X)
      (C ×ˢ Set.univ) := fun A hA =>
    continuous_psi.comp_continuousOn
      ((hA.comp continuousOn_fst fun p hp => hp.1).prodMk continuousOn_snd)
  have hk₁ := hι.comp_continuousOn (hri.comp hr₁ hu₁)
  have hk₂ := hι.comp_continuousOn (hri.comp hr₂ hu₂)
  obtain ⟨hIc, hIi⟩ := continuousOn_integral_param N hC
    (fun T X => psi (algebraMap R (R ⊗[F] E) (ρ₁ T.1)) (u T.1 * T.2.1) (algebraMap R (R ⊗[F] E) (ρ₂ (e T))) X)
    (fun T X => psi (algebraMap R (R ⊗[F] E) (Ring.inverse (ρ₁ T.1)))
      (-(algebraMap R (R ⊗[F] E) (Ring.inverse (ρ₂ (e T))) * (u T.1 * T.2.1) * algebraMap R (R ⊗[F] E) (Ring.inverse (ρ₁ T.1))))
      (algebraMap R (R ⊗[F] E) (Ring.inverse (ρ₂ (e T)))) X)
    (hpsi _ ((hι.comp_continuousOn hr₁).prodMk ((htc.mono hC1).prodMk (hι.comp_continuousOn hr₂))))
    (hpsi _ (hk₁.prodMk (((hk₂.mul (htc.mono hC1)).mul hk₁).neg.prodMk hk₂)))
    (fun T hT X => psi_inv (by rw [← map_mul, Ring.inverse_mul_cancel _ (hu₁ T hT), map_one])
      (by rw [← map_mul, Ring.inverse_mul_cancel _ (hu₂ T hT), map_one]) X) φ hφ hφs
  set p₀ : ℝ≥0 := modu (R ⊗[F] E) (inclR R (consCol x B).det) with hp₀
  set w : R × (R ⊗[F] E) × R → ℝ≥0 := fun T =>
    wt F E R (M + 1) (ρ₁ T.1) * (p₀ * (modu (R ⊗[F] E) (u T.1) * wt F E R M (ρ₂ (e T)))) with hwdef
  have hwc : ContinuousOn w C :=
    ((continuousOn_wt R hR _).comp hr₁ hu₁).mul (continuousOn_const.mul
      ((((modu_basic (R ⊗[F] E)).2.2.2 (nice_tensor F E R hR).2.2).comp
        (huc.comp continuousOn_fst fun T hT => hC1 hT)
        fun T hT => IsUnit.of_mul_eq_one_right _ (hu _ (hC1 hT))).mul
        ((continuousOn_wt R hR _).comp hr₂ hu₂)))
  have hDc : ContinuousOn (fun T => (w T : ℝ) *
      ∫ X, φ (psi (algebraMap R (R ⊗[F] E) (ρ₁ T.1)) (u T.1 * T.2.1) (algebraMap R (R ⊗[F] E) (ρ₂ (e T))) X) ∂N) C :=
    (NNReal.continuous_coe.comp_continuousOn hwc).mul hIc
  refine ⟨interior C, _, isOpen_interior, hbase, hDc.mono interior_subset,
    fun T _ => mul_nonneg (w T).2 (integral_nonneg fun X => hφ0 _), fun S hSC hS => ?_, ?_⟩
  · have hSC' : S ⊆ C := hSC.trans interior_subset
    have hφm : Measurable fun X => ENNReal.ofReal (φ X) := hφ.measurable.ennreal_ofReal
    have hFi := hφm.indicator (hgc.measurable hS)
    have hc2 : Continuous fun p : (Fin 1 → Fin (M + 1) → (R ⊗[F] E)) × (Fin (M + 1) → (R ⊗[F] E)) => ![p.1 0, p.2] := by
      refine continuous_pi fun a => ?_
      fin_cases a
      · have h0 : Continuous fun p : (Fin 1 → Fin (M + 1) → (R ⊗[F] E)) × (Fin (M + 1) → (R ⊗[F] E)) => p.1 0 :=
          (continuous_apply 0).comp continuous_fst
        exact h0
      · exact continuous_snd
    obtain ⟨s, hs⟩ : ∃ s, IsSec R σ J x s :=
      ⟨fun y => if h : ∃ g : HA R σ J, g • ratTup (F := F) R x = y then h.choose else 1,
        fun y h => by simp only [dif_pos h]; exact h.choose_spec⟩
    rw [← lintegral_indicator (hgc.measurable hS), lintegral_tup_two lam _ _ hFi,
      Polar.polar F E σ R hR _ J lam ν α m hl hν hα hm W₁ ρ₁ hW₁.measurableSet hρ₁
        (fun y => ∫⁻ z, (gram3 R σ J ⁻¹' S).indicator (fun X => ENNReal.ofReal (φ X)) ![y 0, z]
          ∂(Measure.pi fun _ => lam))
        (hFi.comp hc2.measurable).lintegral_prod_right' ?_,
      ← lintegral_indicator hS, lintegral_prod _ ((aemeasurable_indicator_iff hS).2
        ((hDc.mono hSC').aemeasurable hS).ennreal_ofReal),
      ← lintegral_indicator hW₁.measurableSet]
    · refine lintegral_congr fun b => ?_
      by_cases hb : b ∈ W₁
      swap
      · rw [Set.indicator_of_notMem hb]
        refine ((lintegral_congr fun p => ?_).trans lintegral_zero).symm
        exact Set.indicator_of_notMem (fun h => hb (hC1 (hSC' h))) _
      rw [Set.indicator_of_mem hb]
      set K : ((R ⊗[F] E) × R) × (Fin 2 → Fin (M + 1) → (R ⊗[F] E)) → ℝ≥0∞ := fun p =>
        S.indicator 1 (b, p.1.1, p.1.2) * (wt F E R M (ρ₂ (p.1.2 - n (u b * p.1.1))) : ℝ≥0∞) *
          ENNReal.ofReal (φ (psi (algebraMap R (R ⊗[F] E) (ρ₁ b)) (u b * p.1.1) (algebraMap R (R ⊗[F] E) (ρ₂ (p.1.2 - n (u b * p.1.1)))) p.2))
        with hKdef
      have hem : Measurable fun p : ((R ⊗[F] E) × R) × (Fin 2 → Fin (M + 1) → (R ⊗[F] E)) =>
          ρ₂ (p.1.2 - n (u b * p.1.1)) := hρ₂m.comp (Continuous.measurable (by fun_prop))
      have hK : Measurable K :=
        (((measurable_one.indicator hS).comp (measurable_const.prodMk measurable_fst)).mul
          ((measurable_wt R hR M).comp hem).coe_nnreal_ennreal).mul
          (hφm.comp (continuous_psi.measurable.comp ((measurable_const.prodMk
            ((measurable_fst.fst.const_mul (u b)).prodMk (hι.measurable.comp hem))).prodMk
            measurable_snd)))
      have h1 : ∀ᵐ y ∂m, ∫⁻ z, (gram3 R σ J ⁻¹' S).indicator (fun X => ENNReal.ofReal (φ X))
          ![algebraMap R (R ⊗[F] E) (ρ₁ b) • y 0, z] ∂(Measure.pi fun _ => lam) = (p₀ : ℝ≥0∞) * ((modu (R ⊗[F] E) (u b) : ℝ≥0∞) *
            ∫⁻ t, ∫⁻ y', K (t, pairOf R σ J B y (s y) y') ∂m' ∂(lam.prod ν)) := by
        have h0 : ∀ᵐ y ∂m, ∃ g : HA R σ J, g • ratTup (F := F) R x = y := horb
        refine h0.mono fun y hy => ?_
        rw [inner_integral σ R hσ hR hst hl hν hγ hm' hgc hn hW₂.measurableSet hρ₂ _ hφm hS (ρ₁ b) b
          (hρ₁ b hb).2 (u b) (hu b hb) (fun t d h => (hCU (hSC' h)).2) (s y) y (hs y hy),
          lintegral_prod (fun t => ∫⁻ y', K (t, pairOf R σ J B y (s y) y') ∂m')
            (hK.comp (measurable_fst.prodMk ((continuous_pairOf σ R J B y (s y)).measurable.comp
              measurable_snd))).lintegral_prod_right'.aemeasurable]
      refine (congrArg (_ * ·) (lintegral_congr_ae h1)).trans ?_
      rw [lintegral_const_mul' _ _ ENNReal.coe_ne_top, lintegral_const_mul' _ _ ENNReal.coe_ne_top,
        twoStep_param σ R hN (lam.prod ν) K hK s hs, ← lintegral_const_mul' _ _ ENNReal.coe_ne_top,
        ← lintegral_const_mul' _ _ ENNReal.coe_ne_top, ← lintegral_const_mul' _ _ ENNReal.coe_ne_top]
      refine lintegral_congr fun p => ?_
      by_cases hp : (b, p) ∈ S
      · have hp' : (b, p.1, p.2) ∈ S := hp
        rw [Set.indicator_of_mem hp, ENNReal.ofReal_mul (NNReal.coe_nonneg (w (b, p))), ENNReal.ofReal_coe_nnreal,
          ofReal_integral_eq_lintegral_ofReal (hIi _ (hSC' hp)) (ae_of_all _ fun X => hφ0 _)]
        simp only [hKdef, Set.indicator_of_mem hp', Pi.one_apply, one_mul]
        rw [lintegral_const_mul' _ _ ENNReal.coe_ne_top]
        simp only [hwdef, hedef, wt, ENNReal.coe_mul, mul_assoc]
      · have hp' : (b, p.1, p.2) ∉ S := hp
        rw [Set.indicator_of_notMem hp]
        simp [hKdef, Set.indicator_of_notMem hp']
    · intro y hy
      refine (lintegral_congr fun z => ?_).trans lintegral_zero
      refine Set.indicator_of_notMem (fun h => hy ?_) _
      have h1 : gram3 R σ J ![y 0, z] ∈ S := h
      exact hC1 (hSC' h1)
  · have ha : (algebraMap F E a) ≠ 0 := by simpa using hst.2.1
    have hia : inclR R (algebraMap F E a) = algebraMap R (R ⊗[F] E) α := by
      rw [hαdef, ← IsScalarTower.algebraMap_apply]
      exact (Algebra.TensorProduct.includeRight : E →ₐ[F] (R ⊗[F] E)).commutes a
    have huα : u α = inclR R (algebraMap F E a)⁻¹ := by
      have h1 := hu α hαW
      rw [hρ₁1, one_mul, ← hia] at h1
      rw [← one_mul (u α), ← map_one (inclR R), ← inv_mul_cancel₀ ha, map_mul, mul_assoc, h1, mul_one]
    simp only [hwdef, he0, hρ₁1, hρ₂1, wt_one, map_one, mul_zero, psi_one, one_mul, mul_one, huα]
    rw [div_eq_mul_inv, map_mul, (modu_basic (R ⊗[F] E)).2.1 _ _ ((IsUnit.mk0 _ hdet).map _)
      ((IsUnit.mk0 _ (inv_ne_zero ha)).map _)]

end GlobalTheory.GaugeEx.GramDensity
