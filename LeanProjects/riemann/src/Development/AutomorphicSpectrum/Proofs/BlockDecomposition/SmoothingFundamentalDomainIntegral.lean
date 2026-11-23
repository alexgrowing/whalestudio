import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.AllLeaves
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UfamConst
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HaarRightInvariantTotallyComplexStatement
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DiscreteAutomorphicRepGLLocalComponentIsUnitaris
open scoped ENNReal
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology Polynomial
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs GlobalTheory.CompanionTheory.Conc
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.AutomorphicForm
open scoped Pointwise

noncomputable section

namespace GlobalTheory.CompanionTheory.Conc

theorem lintegral_sq_le_of_average {G Y : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] [TopologicalSpace Y] [MeasurableSpace Y]
    [OpensMeasurableSpace Y] (μ : Measure G) [SFinite μ] [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant]
    (Γ : Subgroup G) [Countable Γ] (F : Set G) (hF : IsFundamentalDomain Γ F μ)
    (ν : Measure Y) (b : Y → ℝ≥0∞) (hb : Measurable b) (hmass : ∫⁻ y, b y ∂ν = 1)
    (k : Y → G) (hk : Continuous k) (f : G → ℂ) (hf : Continuous f)
    (hinv : ∀ γ ∈ Γ, ∀ g, f (γ * g) = f g) (s : G → ℂ)
    (hs : ∀ x, ‖s x‖ₑ ≤ ∫⁻ y, b y * ‖f (x * k y)‖ₑ ∂ν) :
    ∫⁻ x in F, ‖s x‖ₑ ^ 2 ∂μ ≤ ∫⁻ x in F, ‖f x‖ₑ ^ 2 ∂μ := by
  set p := ν.withDensity b with hp
  haveI : IsProbabilityMeasure p := ⟨by rw [hp, withDensity_apply _ MeasurableSet.univ]; simpa using hmass⟩
  have hm : ∀ x, Continuous fun y => f (x * k y) := fun x => hf.comp (continuous_const.mul hk)
  have hsq : ∀ {X : Type _} [MeasurableSpace X] (m : Measure X) (g : X → ℂ),
      eLpNorm g 2 m ^ 2 = ∫⁻ x, ‖g x‖ₑ ^ 2 ∂m := by
    intro X _ m g
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top,
      ENNReal.toReal_ofNat, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    norm_num [ENNReal.rpow_two]
  have hpt : ∀ x, ‖s x‖ₑ ^ 2 ≤ ∫⁻ y, ‖f (x * k y)‖ₑ ^ 2 ∂p := by
    intro x
    have h1 : ∫⁻ y, b y * ‖f (x * k y)‖ₑ ∂ν = ∫⁻ y, ‖f (x * k y)‖ₑ ∂p := by
      rw [hp, lintegral_withDensity_eq_lintegral_mul ν hb (hm x).measurable.enorm]
      rfl
    have h2 := eLpNorm_le_eLpNorm_of_exponent_le (p := 1) (q := 2) (μ := p) (by norm_num)
      (hm x).measurable.aestronglyMeasurable
    rw [eLpNorm_one_eq_lintegral_enorm] at h2
    rw [← hsq p]
    exact pow_le_pow_left' ((hs x).trans (h1.le.trans h2)) 2
  have hΓ : ∀ (γ : Γ) (x : G), ‖f (γ • x)‖ₑ ^ 2 = ‖f x‖ₑ ^ 2 := fun γ x => by
    rw [Subgroup.smul_def, smul_eq_mul, hinv _ γ.2]
  have htr : ∀ h : G, ∫⁻ x in F, ‖f (x * h)‖ₑ ^ 2 ∂μ = ∫⁻ x in F, ‖f x‖ₑ ^ 2 ∂μ := by
    intro h
    have hF' : IsFundamentalDomain Γ (MulOpposite.op h • F) μ := hF.smul_of_comm _
    have e1 := (measurePreserving_mul_right μ h).setLIntegral_comp_preimage_emb
      (MeasurableEquiv.mulRight h).measurableEmbedding (fun z => ‖f z‖ₑ ^ 2) (MulOpposite.op h • F)
    have e2 : (fun x => x * h) ⁻¹' (MulOpposite.op h • F) = F := by
      ext x
      simp [Set.mem_smul_set_iff_inv_smul_mem]
    rw [e2] at e1
    rw [e1]
    exact hF'.setLIntegral_eq hF _ hΓ
  have hjoint : Measurable (Function.uncurry fun (x : G) (y : Y) => ‖f (x * k y)‖ₑ ^ 2) :=
    ((hf.comp (continuous_fst.mul (hk.comp continuous_snd))).measurable.enorm).pow_const 2
  calc ∫⁻ x in F, ‖s x‖ₑ ^ 2 ∂μ ≤ ∫⁻ x in F, ∫⁻ y, ‖f (x * k y)‖ₑ ^ 2 ∂p ∂μ := lintegral_mono hpt
    _ = ∫⁻ y, ∫⁻ x in F, ‖f (x * k y)‖ₑ ^ 2 ∂μ ∂p := lintegral_lintegral_swap hjoint.aemeasurable
    _ = ∫⁻ _y, ∫⁻ x in F, ‖f x‖ₑ ^ 2 ∂μ ∂p := lintegral_congr fun y => htr (k y)
    _ = ∫⁻ x in F, ‖f x‖ₑ ^ 2 ∂μ := by simp

theorem sm_sq_mass_le : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (N : ℕ) [MeasurableSpace (GA E N)] [BorelSpace (GA E N)] (μ : Measure (GA E N)) [μ.IsHaarMeasure] [MeasurableSpace (archGroup E N)] [BorelSpace (archGroup E N)] (ν : Measure (archGroup E N)) [ν.IsHaarMeasure] (F : Set (GA E N)) (β : archGroup E N → ℝ), IsFundamentalDomain (latticeGL E N) F μ → Ker ν β →
  ∀ f : GA E N → ℂ, Continuous f → (∀ γ ∈ latticeGL E N, ∀ g, f (γ * g) = f g) →
  ∫⁻ x in F, ‖sm ν β f x‖ₑ ^ 2 ∂μ ≤ ∫⁻ x in F, ‖f x‖ₑ ^ 2 ∂μ := by
  intro E _ _ _ N _ _ μ _ _ _ ν _ F β hF hβ f hf hinv
  haveI : Countable (latticeGL E N) := GlobalTheory.DiscreteUnit.countable_latticeGL
  haveI : SecondCountableTopology (GA E N) := GlobalTheory.CuspRep.CuspidalL2GL.secondCountableTopology_GA E N
  haveI : LocallyCompactSpace (GA E N) := GlobalTheory.CuspRep.CuspidalL2GL.locallyCompactSpace_GA E N
  haveI : μ.IsMulRightInvariant := GlobalTheory.T.haar_right_invariant_totally_complex E N μ
  refine lintegral_sq_le_of_average μ (latticeGL E N) F hF ν (fun y => ENNReal.ofReal (β y))
    hβ.cont.measurable.ennreal_ofReal ?_ (infEmb E N) continuous_infEmb f hf hinv (sm ν β f) ?_
  · rw [← ofReal_integral_eq_lintegral_ofReal
      (hβ.cont.integrable_of_hasCompactSupport hβ.cpt) (Eventually.of_forall hβ.nonneg), hβ.mass]
    simp
  · intro x
    refine (enorm_integral_le_lintegral_enorm _).trans (le_of_eq (lintegral_congr fun y => ?_))
    rw [enorm_mul]
    congr 1
    rw [← ofReal_norm_eq_enorm, Complex.norm_real, Real.norm_of_nonneg (hβ.nonneg y)]

end GlobalTheory.CompanionTheory.Conc

end
