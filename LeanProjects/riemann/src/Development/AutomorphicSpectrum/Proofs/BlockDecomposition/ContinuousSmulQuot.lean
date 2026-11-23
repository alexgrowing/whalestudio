import Mathlib
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.HermitianCellMeasures.CellAbs

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace GlobalTheory.CompanionTheory.RswCellInv

open PositivityTheory.Rg.Rsw.Cell

variable {G : Type} [Group G] [TopologicalSpace G]

theorem mk_inv_mul' {P : Subgroup G} {p : G} (hp : p ∈ P) (g : G) :
    (QuotientGroup.mk (p * g)⁻¹ : G ⧸ P) = QuotientGroup.mk g⁻¹ := by
  rw [QuotientGroup.eq]
  simpa using hp

theorem mk_inv_rp' {P : Subgroup G} (q : G ⧸ P) : (QuotientGroup.mk (rp q)⁻¹ : G ⧸ P) = q := by
  simp [rp]

theorem rp_mk_inv {P : Subgroup G} (g : G) :
    ∃ p ∈ P, rp (QuotientGroup.mk g⁻¹ : G ⧸ P) = p * g := by
  have hmem : rp (QuotientGroup.mk g⁻¹ : G ⧸ P) * g⁻¹ ∈ P := by
    have := mk_inv_rp' (QuotientGroup.mk g⁻¹ : G ⧸ P)
    rw [QuotientGroup.eq] at this
    simpa using this
  exact ⟨_, hmem, by simp⟩

theorem mk_inv_rp_mul {P : Subgroup G} (q : G ⧸ P) (x : G) :
    (QuotientGroup.mk (rp q * x)⁻¹ : G ⧸ P) = x⁻¹ • q := by
  conv_rhs => rw [← mk_inv_rp' q]
  rw [mul_inv_rev]
  rfl

theorem density_rp {P : Subgroup G} {h : G → ℝ} {mu : (G → ℂ) → ℂ} (S : Setup P h mu) (x g : G) :
    h (rp (QuotientGroup.mk g⁻¹ : G ⧸ P) * x) / h (rp (QuotientGroup.mk g⁻¹ : G ⧸ P)) =
      h (g * x) / h g := by
  obtain ⟨p, hp, e⟩ := rp_mk_inv (P := P) g
  rw [e]
  have h1 := (S.pos (p * g)).ne'
  have h2 := (S.pos g).ne'
  rw [div_eq_div_iff h1 h2]
  have := S.law p hp g (g * x)
  rw [mul_assoc]
  linarith

theorem sec_translate {P : Subgroup G} {h : G → ℝ} {mu : (G → ℂ) → ℂ} [ContinuousMul G] (S : Setup P h mu)
    {f : G → ℂ} (hf : Sec P h f) (x : G) : Sec P h (fun g => f (g * x)) := by
  refine ⟨hf.1.comp (continuous_mul_right x), fun p hp g => ?_⟩
  have h1 := hf.2 p hp (g * x)
  have h2 : ((h (p * g) : ℂ)) * h (g * x) = h g * h (p * (g * x)) := by
    exact_mod_cast S.law p hp g (g * x)
  have h3 : (h (g * x) : ℂ) ≠ 0 := by exact_mod_cast (S.pos _).ne'
  apply mul_right_cancel₀ h3
  show f (p * g * x) * (h g : ℂ) * (h (g * x) : ℂ) = f (g * x) * (h (p * g) : ℂ) * (h (g * x) : ℂ)
  rw [mul_assoc p g x]
  linear_combination (h g : ℂ) * h1 - f (g * x) * h2

variable [IsTopologicalGroup G]

theorem sec_of_real {P : Subgroup G} {h : G → ℝ} (hc : Continuous h) {F : G ⧸ P → ℝ} (hF : Continuous F) :
    Sec P h (fun g => ((F (QuotientGroup.mk g⁻¹) : ℝ) : ℂ) * (h g : ℂ)) := by
  refine ⟨?_, fun p hp g => ?_⟩
  · have : Continuous fun g : G => (QuotientGroup.mk g⁻¹ : G ⧸ P) :=
      QuotientGroup.continuous_mk.comp continuous_inv
    exact (Complex.continuous_ofReal.comp (hF.comp this)).mul (Complex.continuous_ofReal.comp hc)
  · simp only [mk_inv_mul' hp]
    ring

theorem continuous_density {P : Subgroup G} {h : G → ℝ} {mu : (G → ℂ) → ℂ} (S : Setup P h mu) (x : G) :
    Continuous fun q : G ⧸ P => h (rp q * x) / h (rp q) := by
  have hq : IsQuotientMap fun g : G => (QuotientGroup.mk g⁻¹ : G ⧸ P) :=
    (QuotientGroup.isOpenQuotientMap_mk (N := P)).isQuotientMap.comp (Homeomorph.inv G).isQuotientMap
  rw [hq.continuous_iff]
  have : ((fun q : G ⧸ P => h (rp q * x) / h (rp q)) ∘ fun g : G => (QuotientGroup.mk g⁻¹ : G ⧸ P)) =
      fun g => h (g * x) / h g := by
    funext g
    exact density_rp S x g
  rw [this]
  exact (S.cont.comp (continuous_mul_right x)).div S.cont fun g => (S.pos g).ne'

theorem continuous_smul_quot {P : Subgroup G} (x : G) : Continuous fun q : G ⧸ P => x • q := by
  rw [(QuotientGroup.isOpenQuotientMap_mk (N := P)).isQuotientMap.continuous_iff]
  exact QuotientGroup.continuous_mk.comp (continuous_mul_left x)

theorem compact_quot' {P : Subgroup G}
    (hco : ∃ C : Set G, IsCompact C ∧ ∀ g, ∃ q ∈ P, ∃ c ∈ C, g = q * c) : CompactSpace (G ⧸ P) := by
  obtain ⟨C, hC, hcov⟩ := hco
  have hK : IsCompact ((fun g : G => (QuotientGroup.mk g⁻¹ : G ⧸ P)) '' C) :=
    hC.image (QuotientGroup.continuous_mk.comp continuous_inv)
  refine ⟨?_⟩
  convert hK using 1
  symm
  refine Set.eq_univ_of_forall fun x => ?_
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective x
  obtain ⟨q, hq, c, hc, hqc⟩ := hcov y⁻¹
  refine ⟨c, hc, ?_⟩
  have : y = (q * c)⁻¹ := by rw [← hqc, inv_inv]
  rw [this, QuotientGroup.eq]
  simpa using hq

theorem integral_translate {P : Subgroup G} [MeasurableSpace (G ⧸ P)] {h : G → ℝ} {mu : (G → ℂ) → ℂ}
    (S : Setup P h mu) {ν : Measure (G ⧸ P)} (hR : Repr P h mu ν) {x : G} (hx : Inv P h mu x)
    {F : G ⧸ P → ℝ} (hF : Continuous F) :
    ∫ q, h (rp q * x) / h (rp q) * F (x⁻¹ • q) ∂ν = ∫ q, F q ∂ν := by
  have hs := sec_of_real (P := P) S.cont hF
  have h1 := (hR.2 _ hs).2
  have h2 := (hR.2 _ (sec_translate S hs x)).2
  have h3 := hx _ hs
  rw [h1, h2] at h3
  have e1 : ∀ q : G ⧸ P, (((F (QuotientGroup.mk (rp q)⁻¹) : ℝ) : ℂ) * (h (rp q) : ℂ)) / (h (rp q) : ℂ) =
      ((F q : ℝ) : ℂ) := fun q => by
    have : (h (rp q) : ℂ) ≠ 0 := by exact_mod_cast (S.pos _).ne'
    rw [mk_inv_rp', mul_div_cancel_right₀ _ this]
  have e2 : ∀ q : G ⧸ P, (((F (QuotientGroup.mk (rp q * x)⁻¹) : ℝ) : ℂ) * (h (rp q * x) : ℂ)) / (h (rp q) : ℂ) =
      ((h (rp q * x) / h (rp q) * F (x⁻¹ • q) : ℝ) : ℂ) := fun q => by
    rw [mk_inv_rp_mul]
    push_cast
    ring
  simp only [e1, e2] at h3
  rw [integral_complex_ofReal, integral_complex_ofReal] at h3
  exact_mod_cast h3

theorem inv_measure [T2Space G] [SecondCountableTopology G] (P : Subgroup G) [MeasurableSpace (G ⧸ P)]
    [BorelSpace (G ⧸ P)] (h : G → ℝ) (mu : (G → ℂ) → ℂ) (S : Setup P h mu) (ν : Measure (G ⧸ P))
    (hR : Repr P h mu ν) (x : G) (hx : Inv P h mu x) :
    (ν.withDensity fun q => ENNReal.ofReal (h (rp q * x) / h (rp q))).map (fun q => x⁻¹ • q) = ν := by
  have : IsClosed (P : Set G) := S.closed
  have : CompactSpace (G ⧸ P) := compact_quot' S.cocpt
  have : IsFiniteMeasure ν := hR.1
  have hj := continuous_density S x
  have hsm := continuous_smul_quot (P := P) x⁻¹
  have hjm : Measurable fun q : G ⧸ P => ENNReal.ofReal (h (rp q * x) / h (rp q)) :=
    ENNReal.measurable_ofReal.comp hj.measurable
  have hjnn : ∀ q : G ⧸ P, 0 ≤ h (rp q * x) / h (rp q) := fun q => (div_pos (S.pos _) (S.pos _)).le
  have hfin : IsFiniteMeasure (ν.withDensity fun q => ENNReal.ofReal (h (rp q * x) / h (rp q))) :=
    isFiniteMeasure_withDensity_ofReal
      (hj.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)).2
  have hfin' : IsFiniteMeasure
      ((ν.withDensity fun q => ENNReal.ofReal (h (rp q * x) / h (rp q))).map (fun q => x⁻¹ • q)) :=
    Measure.isFiniteMeasure_map _ _
  refine ext_of_forall_integral_eq_of_IsFiniteMeasure fun f => ?_
  rw [integral_map hsm.aemeasurable f.continuous.aestronglyMeasurable,
    integral_withDensity_eq_integral_toReal_smul hjm (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  have := integral_translate S hR hx f.continuous
  rw [← this]
  refine integral_congr_ae (ae_of_all _ fun q => ?_)
  simp only [ENNReal.toReal_ofReal (hjnn q), smul_eq_mul]

theorem invM : InvM := by
  intro G _ _ _ _ _ _ P _ _ h mu S ν hR x hx
  refine ⟨continuous_density S x, fun F hF => ?_⟩
  have hsm := continuous_smul_quot (P := P) x⁻¹
  have hjm : Measurable fun q : G ⧸ P => ENNReal.ofReal (h (rp q * x) / h (rp q)) :=
    ENNReal.measurable_ofReal.comp (continuous_density S x).measurable
  have key : ∫⁻ q, F q ∂((ν.withDensity fun q => ENNReal.ofReal (h (rp q * x) / h (rp q))).map
      (fun q => x⁻¹ • q)) = ∫⁻ q, F q ∂ν := by rw [inv_measure P h mu S ν hR x hx]
  rw [lintegral_map hF hsm.measurable,
    lintegral_withDensity_eq_lintegral_mul ν hjm
      (show Measurable fun a => F (x⁻¹ • a) from hF.comp hsm.measurable)] at key
  rw [← key]
  refine lintegral_congr fun q => ?_
  simp only [Pi.mul_apply, mul_comm]

end GlobalTheory.CompanionTheory.RswCellInv

end
