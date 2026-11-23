import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ExistsIsHaarMeasureSUJ
open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Dec GlobalTheory.DSId GlobalTheory.DSSU
open scoped InnerProductSpace ENNReal

noncomputable section

namespace GlobalTheory.SqIntSU

variable {n : ℕ}

def circleBorelMS : MeasurableSpace Circle := borel Circle

attribute [local instance] circleBorelMS

theorem circleBorelSpace : BorelSpace Circle := ⟨rfl⟩

attribute [local instance] circleBorelSpace

theorem circle_star_mul (z : Circle) : star (z : ℂ) * z = 1 := by
  rw [Complex.star_def, Complex.conj_mul', Circle.norm_coe]
  norm_num

theorem circle_mul_star (z : Circle) : (z : ℂ) * star (z : ℂ) = 1 := by
  rw [mul_comm]
  exact circle_star_mul z

section Scal

variable (ε : Fin n → Bool)

def unitScalar (z : Circle) : UJ ε :=
  ⟨⟨(z : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ), star (z : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ),
    by rw [smul_mul_smul_comm, circle_mul_star, Matrix.one_mul, one_smul],
    by rw [smul_mul_smul_comm, circle_star_mul, Matrix.one_mul, one_smul]⟩, by
    show ((z : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ))ᴴ * Jm ε * ((z : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)) = Jm ε
    simp only [Matrix.conjTranspose_smul, Matrix.conjTranspose_one, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.one_mul, Matrix.mul_one, smul_smul, circle_star_mul, circle_mul_star, one_smul]⟩

theorem umat_unitScalar (z : Circle) : umat (unitScalar ε z) = (z : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) := rfl

theorem unitScalar_comm (z : Circle) (g : UJ ε) : unitScalar ε z * g = g * unitScalar ε z := by
  apply Subtype.ext
  apply Units.ext
  show umat (unitScalar ε z) * umat g = umat g * umat (unitScalar ε z)
  rw [umat_unitScalar, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul, Matrix.mul_one]

theorem unitScalar_mul (a b : Circle) : unitScalar ε (a * b) = unitScalar ε a * unitScalar ε b := by
  apply Subtype.ext
  apply Units.ext
  show ((a * b : Circle) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) =
    ((a : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)) * ((b : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ))
  rw [Circle.coe_mul, smul_mul_smul_comm, Matrix.one_mul]

theorem unitScalar_one : unitScalar ε 1 = 1 := by
  apply Subtype.ext
  apply Units.ext
  show ((1 : Circle) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) = 1
  rw [Circle.coe_one, one_smul]

theorem continuous_unitScalar : Continuous (unitScalar ε) := by
  apply Continuous.subtype_mk
  rw [Units.continuous_iff]
  constructor
  · show Continuous fun z : Circle => (z : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)
    fun_prop
  · show Continuous fun z : Circle => star (z : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)
    fun_prop

theorem isClosed_special : IsClosed (SUJ ε : Set (UJ ε)) :=
  isClosed_eq (Units.continuous_val.comp continuous_subtype_val).matrix_det continuous_const

theorem locallyCompact_special : LocallyCompactSpace (SUJ ε) :=
  (isClosed_special ε).isClosedEmbedding_subtypeVal.locallyCompactSpace

attribute [local instance] locallyCompact_special

theorem secondCountable_special : SecondCountableTopology (SUJ ε) :=
  Topology.IsInducing.subtypeVal.secondCountableTopology

attribute [local instance] secondCountable_special

theorem sigmaCompact_special : SigmaCompactSpace (SUJ ε) :=
  sigmaCompactSpace_of_locallyCompact_secondCountable

attribute [local instance] sigmaCompact_special

def scalarMul : Circle × SUJ ε →* UJ ε where
  toFun p := unitScalar ε p.1 * (p.2 : UJ ε)
  map_one' := by
    show unitScalar ε 1 * 1 = 1
    rw [unitScalar_one, one_mul]
  map_mul' := by
    rintro ⟨a, g⟩ ⟨b, h⟩
    show unitScalar ε (a * b) * ((g * h : SUJ ε) : UJ ε) = unitScalar ε a * (g : UJ ε) * (unitScalar ε b * (h : UJ ε))
    calc unitScalar ε (a * b) * ((g * h : SUJ ε) : UJ ε) = unitScalar ε a * (unitScalar ε b * (g : UJ ε)) * (h : UJ ε) := by
          rw [Subgroup.coe_mul, unitScalar_mul]
          simp only [mul_assoc]
      _ = unitScalar ε a * ((g : UJ ε) * unitScalar ε b) * (h : UJ ε) := by rw [unitScalar_comm ε b (g : UJ ε)]
      _ = unitScalar ε a * (g : UJ ε) * (unitScalar ε b * (h : UJ ε)) := by simp only [mul_assoc]

theorem scalarMul_apply (z : Circle) (g : SUJ ε) : scalarMul ε (z, g) = unitScalar ε z * (g : UJ ε) := rfl

theorem continuous_scalarMul : Continuous (scalarMul ε) :=
  ((continuous_unitScalar ε).comp continuous_fst).mul (continuous_subtype_val.comp continuous_snd)

theorem norm_det_umat (g : UJ ε) : ‖(umat g).det‖ = 1 := by
  have hg : (umat g)ᴴ * Jm ε * umat g = Jm ε := g.2
  have h := congrArg Matrix.det hg
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose] at h
  have hJ : (Jm ε).det ≠ 0 := by
    have h1 := congrArg Matrix.det (Jm_mul_self ε)
    rw [Matrix.det_mul, Matrix.det_one] at h1
    exact left_ne_zero_of_mul_eq_one h1
  have h2 : star (umat g).det * (umat g).det = 1 := by
    have h3 : (star (umat g).det * (umat g).det) * (Jm ε).det = 1 * (Jm ε).det := by
      rw [one_mul]
      calc (star (umat g).det * (umat g).det) * (Jm ε).det = star (umat g).det * (Jm ε).det * (umat g).det := by ring
        _ = (Jm ε).det := h
    exact mul_right_cancel₀ hJ h3
  rw [Complex.star_def, Complex.conj_mul'] at h2
  have h4 : ‖(umat g).det‖ ^ 2 = 1 := by exact_mod_cast h2
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 h4

theorem scalarMul_surjective (hn : 0 < n) : Function.Surjective (scalarMul ε) := by
  intro u
  obtain ⟨ζ, hζ⟩ := IsAlgClosed.exists_pow_nat_eq (umat u).det hn
  have hnorm : ‖ζ‖ = 1 := by
    have h1 : ‖ζ‖ ^ n = 1 := by rw [← norm_pow, hζ, norm_det_umat]
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hn.ne').1 h1
  let z : Circle := ⟨ζ, by simpa [Submonoid.unitSphere] using hnorm⟩
  have hz : (z : ℂ) = ζ := rfl
  refine ⟨(z, ⟨(unitScalar ε z)⁻¹ * u, ?_⟩), ?_⟩
  · show (star (z : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) * umat u).det = 1
    rw [Matrix.smul_mul, Matrix.one_mul, Matrix.det_smul, Fintype.card_fin, ← hζ, ← hz, ← mul_pow,
      circle_star_mul, one_pow]
  · rw [scalarMul_apply]
    exact mul_inv_cancel_left _ _

theorem scalarMul_proper : Filter.Tendsto (scalarMul ε) (Filter.cocompact _) (Filter.cocompact _) := by
  refine (Filter.hasBasis_cocompact.tendsto_iff Filter.hasBasis_cocompact).2 fun C hC => ?_
  refine ⟨scalarMul ε ⁻¹' C, ?_, fun x hx => hx⟩
  let W : Set (UJ ε) := (fun p : Circle × UJ ε => (unitScalar ε p.1)⁻¹ * p.2) '' (Set.univ ×ˢ C)
  have hW : IsCompact W := (isCompact_univ.prod hC).image
    (((continuous_unitScalar ε).comp continuous_fst).inv.mul continuous_snd)
  have hT : IsCompact ((Subtype.val : SUJ ε → UJ ε) ⁻¹' W) :=
    (isClosed_special ε).isClosedEmbedding_subtypeVal.isCompact_preimage hW
  refine (isCompact_univ.prod hT).of_isClosed_subset (hC.isClosed.preimage (continuous_scalarMul ε)) ?_
  rintro ⟨z, g⟩ hzg
  refine ⟨trivial, ⟨(z, scalarMul ε (z, g)), ⟨trivial, hzg⟩, ?_⟩⟩
  show (unitScalar ε z)⁻¹ * (unitScalar ε z * (g : UJ ε)) = g
  exact inv_mul_cancel_left _ _

def circleHaar : Measure Circle := Measure.haarMeasure ⊤

theorem circleHaar_isHaar : circleHaar.IsHaarMeasure := by
  unfold circleHaar
  infer_instance

attribute [local instance] circleHaar_isHaar

theorem circleHaar_univ : circleHaar Set.univ = 1 := by
  have h := Measure.haarMeasure_self (G := Circle) (K₀ := ⊤)
  rwa [TopologicalSpace.PositiveCompacts.coe_top] at h

theorem circleHaar_finite : IsFiniteMeasure circleHaar := CompactSpace.isFiniteMeasure

attribute [local instance] circleHaar_finite

theorem lintegral_eq (hn : 0 < n) (μ : Measure (SUJ ε)) (hμ : μ.IsHaarMeasure) :
    ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ∞ ∧ ∀ F : UJ ε → ℝ≥0∞, Measurable F →
      (∀ (z : Circle) (g : UJ ε), F (unitScalar ε z * g) = F g) →
      ∫⁻ g, F g ∂(muG ε) = c * ∫⁻ g, F (g : UJ ε) ∂μ := by
  haveI : SFinite μ := inferInstance
  haveI : (circleHaar.prod μ).IsHaarMeasure := Measure.prod.instIsHaarMeasure _ _
  haveI hν : (Measure.map (scalarMul ε) (circleHaar.prod μ)).IsHaarMeasure :=
    Measure.isHaarMeasure_map _ (scalarMul ε) (continuous_scalarMul ε) (scalarMul_surjective ε hn) (scalarMul_proper ε)
  set ν := Measure.map (scalarMul ε) (circleHaar.prod μ) with hνdef
  have hmu : muG ε = (muG ε).haarScalarFactor ν • ν := Measure.isMulLeftInvariant_eq_smul (muG ε) ν
  refine ⟨((muG ε).haarScalarFactor ν : ℝ≥0∞), ?_, ENNReal.coe_ne_top, fun F hF hinv => ?_⟩
  · exact ENNReal.coe_ne_zero.2 (Measure.haarScalarFactor_pos_of_isHaarMeasure (muG ε) ν).ne'
  have hint : ∫⁻ g, F g ∂ν = ∫⁻ g, F (g : UJ ε) ∂μ := by
    rw [hνdef, lintegral_map hF (continuous_scalarMul ε).measurable,
      lintegral_prod (fun p => F (scalarMul ε p)) (hF.comp (continuous_scalarMul ε).measurable).aemeasurable]
    simp only [scalarMul_apply, hinv]
    rw [lintegral_const, circleHaar_univ, mul_one]
  conv_lhs => rw [hmu]
  rw [lintegral_smul_measure, ENNReal.smul_def, smul_eq_mul, hint]

end Scal

end GlobalTheory.SqIntSU

noncomputable section

namespace GlobalTheory.SqIntSU

attribute [local instance] circleBorelMS circleBorelSpace locallyCompact_special secondCountable_special sigmaCompact_special

theorem memLp_two_iff_lintegral {X : Type} [MeasurableSpace X] [TopologicalSpace X] [OpensMeasurableSpace X]
    [SecondCountableTopologyEither X ℂ] (μ : Measure X) (f : X → ℂ) (hf : Continuous f) :
    MemLp f 2 μ ↔ ∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) ∂μ < ∞ := by
  have h := eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (μ := μ) (f := f) (p := 2) two_ne_zero
    ENNReal.ofNat_ne_top
  simp only [ENNReal.toReal_ofNat] at h
  exact ⟨fun hm => h.1 hm.2, fun hl => ⟨hf.aestronglyMeasurable, h.2 hl⟩⟩

theorem sqInt_iff : ∀ (n : ℕ), 1 ≤ n → ∀ (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (m : ℤ) (π' π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)),
    Ext ε m π' π → IsURepOn (UJset ε) π → (IsSqIntOn ε π ↔ IsSqIntS ε π') := by
  intro n hn ε H _ _ m π' π hE hU
  have hn0 : 0 < n := hn
  have hcont : ∀ v w : H, Continuous (fun g : UJ ε => ⟪w, π (umat g) v⟫_ℂ) := by
    intro v w
    have h1 : Continuous (fun g : UJ ε => π (umat g) v) :=
      (hU.2.2 v).comp_continuous (Units.continuous_val.comp continuous_subtype_val) (fun g => g.2)
    exact continuous_const.inner h1
  have hone : (1 : Matrix (Fin n) (Fin n) ℂ) ∈ SUset ε :=
    ⟨show (1 : Matrix (Fin n) (Fin n) ℂ)ᴴ * Jm ε * 1 = Jm ε by simp, Matrix.det_one⟩
  have hsu : ∀ g : SUJ ε, π' (umat g.1) = π (umat g.1) := by
    intro g
    have h := hE 1 (by simp) (umat g.1) ⟨g.1.2, g.2⟩
    simpa using h.symm
  have hπ1 : π' 1 = 1 := by
    have h := hE 1 (by simp) 1 hone
    simp only [one_smul, _root_.one_zpow] at h
    rw [← h, hU.1.1]
  have hscal : ∀ (z : Circle) (g : UJ ε) (v w : H),
      ‖⟪w, π (umat (unitScalar ε z * g)) v⟫_ℂ‖ₑ ^ (2 : ℝ) = ‖⟪w, π (umat g) v⟫_ℂ‖ₑ ^ (2 : ℝ) := by
    intro z g v w
    have h1 : umat (unitScalar ε z * g) = umat (unitScalar ε z) * umat g := rfl
    have hz : π (umat (unitScalar ε z)) = ((z : ℂ) ^ m) • (1 : H →L[ℂ] H) := by
      have h := hE z (Circle.norm_coe z) 1 hone
      rw [umat_unitScalar, h, hπ1]
    rw [h1, hU.1.2 _ (unitScalar ε z).2 _ g.2, hz]
    congr 1
    rw [← ofReal_norm_eq_enorm, ← ofReal_norm_eq_enorm]
    congr 1
    simp [inner_smul_right, norm_zpow, Circle.norm_coe]
  have hmeas : ∀ v w : H, Measurable (fun g : UJ ε => ‖⟪w, π (umat g) v⟫_ℂ‖ₑ ^ (2 : ℝ)) :=
    fun v w => ((hcont v w).measurable.enorm).pow_const _
  have key : ∀ (μ : Measure (SUJ ε)), μ.IsHaarMeasure → ∀ v w : H,
      ((∫⁻ g, ‖⟪w, π (umat g) v⟫_ℂ‖ₑ ^ (2 : ℝ) ∂(muG ε)) < ∞ ↔
        (∫⁻ g, ‖⟪w, π (umat (g : UJ ε)) v⟫_ℂ‖ₑ ^ (2 : ℝ) ∂μ) < ∞) := by
    intro μ hμ v w
    obtain ⟨c, hc0, hct, hc⟩ := lintegral_eq ε hn0 μ hμ
    rw [hc _ (hmeas v w) (fun z g => hscal z g v w)]
    constructor
    · intro h
      exact ENNReal.lt_top_of_mul_ne_top_right h.ne hc0
    · intro h
      exact ENNReal.mul_lt_top hct.lt_top h
  have hS : ∀ v w : H, (fun g : SUJ ε => ⟪w, π' (umat g.1) v⟫_ℂ) = fun g : SUJ ε => ⟪w, π (umat (g : UJ ε)) v⟫_ℂ := by
    intro v w
    funext g
    rw [hsu g]
  constructor
  · intro h μ hμ v w
    rw [hS v w, memLp_two_iff_lintegral _ (fun g : SUJ ε => ⟪w, π (umat (g : UJ ε)) v⟫_ℂ) ((hcont v w).comp continuous_subtype_val)]
    have h' := (memLp_two_iff_lintegral _ _ (hcont v w)).1 (h v w)
    exact (key μ hμ v w).1 h'
  · intro h v w
    have hμ : (Measure.haar : Measure (SUJ ε)).IsHaarMeasure := inferInstance
    have h' := h Measure.haar hμ v w
    rw [hS v w, memLp_two_iff_lintegral _ (fun g : SUJ ε => ⟪w, π (umat (g : UJ ε)) v⟫_ℂ) ((hcont v w).comp continuous_subtype_val)] at h'
    show MemLp (fun g : UJ ε => ⟪w, π (umat g) v⟫_ℂ) 2 (muG ε)
    rw [memLp_two_iff_lintegral _ _ (hcont v w)]
    exact (key _ hμ v w).2 h'

end GlobalTheory.SqIntSU
