import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.ColumnConjugationMeasure
import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.SameSatakeOfProjection
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFiniteMeasureQuotMeasure

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec PositivityTheory.jumpWindows PositivityTheory.RgJS
open GroundTheory.Automorphic GroundTheory.Automorphic.FourierWhittaker GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.Spherical
open scoped ENNReal ComplexConjugate InnerProductSpace
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.CuspRep.CuspidalL2GL

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.AdelicQuotientData

namespace QORT

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {k : ℕ}

omit [IsTotallyComplex E] in
theorem la_ratGL_inj : Function.Injective (ratGL E k) := by
  intro a b e
  ext i j
  have h1 := congrArg (fun g : GA E k => (g : Matrix (Fin k) (Fin k) (Ad E)) i j) e
  exact (algebraMap E (Ad E)).injective h1

theorem la_rat_sum (hN3 : N3) {β : GA E k → ℝ≥0∞} (hβ : IsWt (nuB E k k) β) (x : GA E k) :
    ∑' γ : GL (Fin k) E, β (ratGL E k γ * x) = 1 := by
  rw [← (hN3 E k).2.2.1 (fun h => β (h * x)) (hβ.1.comp (measurable_mul_const x))]
  exact hβ.2 x

theorem la_band_rat (hD0 : D0) (γ : GL (Fin k) E) (x : GA E k) :
    ratGL E k γ * x ∈ band E k ↔ x ∈ band E k := by
  obtain ⟨-, hmul, -, hrat, -⟩ := hD0 E k
  simp only [band, Set.mem_ofPred_eq, hmul, hrat, one_mul]

theorem la_dt_pow (hD0 : D0) (n : ℤ) (g : GA E k) :
    Dt (splitCentre E k 1 ^ n * g) = Real.exp (k * Module.finrank ℚ E * n) * Dt g := by
  obtain ⟨-, hmul, -, -, -, -, hsc, -⟩ := hD0 E k
  rw [← splitCentre_intCast, hmul, hsc]

theorem la_unique (hD0 : D0) (hk : 1 ≤ k) (g : GA E k) :
    ∃! n : ℤ, splitCentre E k 1 ^ n * g ∈ band E k := by
  obtain ⟨hpos, -, -, -, -, -, hsc, -⟩ := hD0 E k
  have hc : (0 : ℝ) < k * Module.finrank ℚ E := by
    have : 0 < Module.finrank ℚ E := Module.finrank_pos
    have hk' : (0 : ℝ) < k := by exact_mod_cast hk
    positivity
  have key : ∀ n : ℤ, splitCentre E k 1 ^ n * g ∈ band E k ↔
      Real.log (Dt g) + n • ((k : ℝ) * Module.finrank ℚ E) ∈ Set.Ico 0 (0 + (k : ℝ) * Module.finrank ℚ E) := by
    intro n
    simp only [band, Set.mem_ofPred_eq, la_dt_pow hD0, hsc, Set.mem_Ico, zero_add, zsmul_eq_mul, mul_one]
    have hD := hpos g
    rw [show Real.exp (k * Module.finrank ℚ E * n) * Dt g = Real.exp (Real.log (Dt g) + n * (k * Module.finrank ℚ E)) by
      rw [Real.exp_add, Real.exp_log hD]; ring_nf]
    rw [← Real.exp_zero, Real.exp_le_exp, Real.exp_lt_exp]
  obtain ⟨n, hn, hu⟩ := existsUnique_add_zsmul_mem_Ico hc (Real.log (Dt g)) 0
  exact ⟨n, (key n).2 hn, fun m hm => hu m ((key m).1 hm)⟩

theorem la_mem (γ : GL (Fin k) E) (n : ℤ) : ratGL E k γ * splitCentre E k 1 ^ n ∈ latticeGL E k :=
  mul_mem (ratGL_mem_latticeGL γ) (zpow_mem_latticeGL n)

theorem la_bij (hD0 : D0) (hk : 1 ≤ k) :
    Function.Bijective fun p : GL (Fin k) E × ℤ => (⟨_, la_mem p.1 p.2⟩ : latticeGL E k) := by
  obtain ⟨-, hmul, -, hrat, -, -, hsc, -⟩ := hD0 E k
  have hc : (0 : ℝ) < k * Module.finrank ℚ E := by
    have : 0 < Module.finrank ℚ E := Module.finrank_pos
    have hk' : (0 : ℝ) < k := by exact_mod_cast hk
    positivity
  refine ⟨fun ⟨γ, n⟩ ⟨γ', m⟩ e => ?_, fun l => ?_⟩
  · have e' : ratGL E k γ * splitCentre E k 1 ^ n = ratGL E k γ' * splitCentre E k 1 ^ m := congrArg Subtype.val e
    have hd := congrArg Dt e'
    simp only [hmul, hrat, one_mul, ← splitCentre_intCast, hsc] at hd
    have hnm : n = m := by
      have := Real.exp_injective hd
      have h2 : (n : ℝ) = m := by
        have := mul_left_cancel₀ hc.ne' this
        exact this
      exact_mod_cast h2
    subst hnm
    have := la_ratGL_inj (mul_right_cancel e')
    subst this
    rfl
  · obtain ⟨γ, n, e⟩ := mem_latticeGL_iff.1 l.2
    exact ⟨(γ, n), Subtype.ext e⟩

theorem lattice_sum (hD0 : D0) (hN3 : N3) (hk : 1 ≤ k) {β : GA E k → ℝ≥0∞} (hβ : IsWt (nuB E k k) β)
    (g : GA E k) : ∑' l : latticeGL E k, (band E k).indicator β ((l : GA E k) * g) = 1 := by
  rw [← (Equiv.ofBijective _ (la_bij hD0 hk)).tsum_eq]
  simp only [Equiv.ofBijective_apply]
  rw [ENNReal.tsum_prod (f := fun (γ : GL (Fin k) E) (n : ℤ) =>
    (band E k).indicator β (ratGL E k γ * splitCentre E k 1 ^ n * g)), ENNReal.tsum_comm]
  have h1 : ∀ n : ℤ, ∑' γ : GL (Fin k) E, (band E k).indicator β (ratGL E k γ * splitCentre E k 1 ^ n * g) =
      (band E k).indicator 1 (splitCentre E k 1 ^ n * g) := by
    intro n
    simp_rw [mul_assoc]
    set x := splitCentre E k 1 ^ n * g
    by_cases hx : x ∈ band E k
    · rw [Set.indicator_of_mem hx, Pi.one_apply, ← la_rat_sum hN3 hβ x]
      exact tsum_congr fun γ => Set.indicator_of_mem ((la_band_rat hD0 γ x).2 hx) _
    · rw [Set.indicator_of_notMem hx]
      simp only [Set.indicator_of_notMem (fun h => hx ((la_band_rat hD0 _ x).1 h)), tsum_zero]
  simp only [h1]
  obtain ⟨n0, hn0, hu⟩ := la_unique hD0 hk g
  rw [tsum_eq_single n0 fun m hm => Set.indicator_of_notMem (fun h => hm (hu m h)) _,
    Set.indicator_of_mem hn0, Pi.one_apply]

theorem band_eq (hQ2 : Q2) (hD0 : D0) (hN3 : N3) (hk : 1 ≤ k) (μ : Measure (GA E k)) [μ.IsHaarMeasure]
    {β : GA E k → ℝ≥0∞} (hβ : IsWt (nuB E k k) β) (Φ : GA E k → ℂ) (hm : Measurable Φ)
    (hl : LeftInv (latticeGL E k) Φ) (hi : IntegrableOn Φ (stdDom (latticeGL E k)) μ) :
    ∫ g in band E k, Φ g ∂μ.withDensity β = ∫ g in stdDom (latticeGL E k), Φ g ∂μ := by
  have hcont : Continuous (Dt : GA E k → ℝ) := (hD0 E k).2.2.1
  have hband : MeasurableSet (band E k) :=
    (hcont.measurable measurableSet_Ici).inter (hcont.measurable measurableSet_Iio)
  have hD := measurableSet_stdDom (latticeGL E k)
  have hL : MeasurableSet (latticeGL E k : Set (GA E k)) :=
    (Subgroup.isClosed_of_discrete (H := latticeGL E k)).measurableSet
  let ν : Measure (GA E k) := Measure.sum fun l : latticeGL E k => Measure.dirac (l : GA E k)
  have hsum : ∀ f : GA E k → ℝ≥0∞, Measurable f → ∫⁻ x, f x ∂ν = ∑' l : latticeGL E k, f l := fun f hf => by
    simp only [ν, lintegral_sum_measure, lintegral_dirac' _ hf]
  have hmap : Measure.map (fun h => h⁻¹) ν = ν := by
    refine Measure.ext fun s hs => ?_
    rw [Measure.map_apply measurable_inv hs, Measure.sum_apply _ (measurable_inv hs), Measure.sum_apply _ hs]
    simp only [Measure.dirac_apply' _ (measurable_inv hs), Measure.dirac_apply' _ hs]
    rw [← (Equiv.inv (latticeGL E k)).tsum_eq]
    refine tsum_congr fun l => ?_
    have e : ((Equiv.inv (latticeGL E k) l : latticeGL E k) : GA E k) = (l : GA E k)⁻¹ := rfl
    rw [e]
    by_cases hl : (l : GA E k) ∈ s
    · rw [Set.indicator_of_mem hl, Set.indicator_of_mem (by rw [Set.mem_preimage, inv_inv]; exact hl)]
      rfl
    · rw [Set.indicator_of_notMem hl, Set.indicator_of_notMem (by rw [Set.mem_preimage, inv_inv]; exact hl)]
  have hae : ∀ᵐ h ∂ν, h ∈ (latticeGL E k : Set (GA E k)) := by
    rw [ae_iff]
    change ν (latticeGL E k : Set (GA E k))ᶜ = 0
    rw [Measure.sum_apply _ hL.compl]
    simp only [Measure.dirac_apply' _ hL.compl]
    exact ENNReal.tsum_eq_zero.2 fun l =>
      Set.indicator_of_notMem (fun hc : (l : GA E k) ∈ (latticeGL E k : Set (GA E k))ᶜ => hc l.2) _
  have hwt : IsWt ν ((stdDom (latticeGL E k)).indicator 1) := by
    refine ⟨measurable_one.indicator hD, fun g => ?_⟩
    rw [hsum (fun h => (stdDom (latticeGL E k)).indicator 1 (h * g))
      ((measurable_one.indicator hD).comp (measurable_mul_const g))]
    obtain ⟨γ, hγ, hu⟩ := existsUnique_stdDom (latticeGL E k) g
    rw [tsum_eq_single γ]
    · simp [Set.indicator_of_mem hγ]
    · intro l hl
      exact Set.indicator_of_notMem (fun h => hl (hu l h)) _
  have hone : ∀ g, ∫⁻ r, ∫⁻ h, (band E k).indicator β (r⁻¹ * h * g) ∂ν ∂Measure.dirac (1 : GA E k) = 1 := by
    intro g
    rw [lintegral_dirac]
    simp only [inv_one, one_mul]
    rw [hsum (fun h => (band E k).indicator β (h * g)) ((hβ.1.indicator hband).comp (measurable_mul_const g))]
    exact lattice_sum hD0 hN3 hk hβ g
  have hint : Integrable Φ (μ.withDensity ((stdDom (latticeGL E k)).indicator 1)) := by
    rw [withDensity_indicator hD, withDensity_one]
    exact hi
  obtain ⟨-, hE⟩ := hQ2 (GA E k) μ ν (Measure.dirac 1) (latticeGL E k : Set (GA E k))
    ((stdDom (latticeGL E k)).indicator 1) ((band E k).indicator β) hmap hae hwt (hβ.1.indicator hband) hone Φ hm
    (fun h hh g => hl h hh g) hint
  rw [restrict_withDensity hband, ← withDensity_indicator hband]
  have e2 : μ.restrict (stdDom (latticeGL E k)) = μ.withDensity ((stdDom (latticeGL E k)).indicator 1) := by
    rw [withDensity_indicator hD, withDensity_one]
  rw [e2, hE]
  simp only [integral_dirac, one_mul]

end QORT

theorem cusp_orthogonality_of : jumpWindows.CuspidalIrreducibleSubrep → jumpWindows.SmoNorm → Q2 → D0 → N3 → W0 → ORT := by
  intro hG hS hQ2 hD0 hN3 _ E _ _ _ k μ _ hk β hβ π π' hπ hπ' hne φ hφ φ' hφ' h h'
  have : μ.IsMulRightInvariant := GlobalTheory.CovolGL.isMulRightInvariant E k μ
  obtain ⟨H, hH, hf⟩ := hG E k μ π hπ
  obtain ⟨H', hH', hf'⟩ := hG E k μ π' hπ'
  have hperp : classes π.V μ ≤ H'ᗮ := fun F hF => by
    by_contra hn
    exact hne (hS E k π π' hπ hπ' (QORTX.sameSat_of_not_perp hπ hH'.1 hf' ⟨F, hF, hn⟩))
  have hHH : H ≤ H'ᗮ := by
    rw [← hf.closure_eq]
    exact Submodule.topologicalClosure_minimal _ hperp (Submodule.isClosed_orthogonal _)
  have m0 := hf.finitePartMemL2 φ hφ
  have m0' := hf'.finitePartMemL2 φ' hφ'
  have m1 := m0.mul_right h
  have m2 := m0'.mul_right h'
  have a1 : m1.toL2 ∈ H := by
    rw [show m1.toL2 = R (latticeGL E k) μ h m0.toL2 from (right_translate_toL2 m0 h).symm]
    exact hH.1.2 h _ (hf.classes_le (toL2_mem_classes hφ m0))
  have a2 : m2.toL2 ∈ H' := by
    rw [show m2.toL2 = R (latticeGL E k) μ h' m0'.toL2 from (right_translate_toL2 m0' h').symm]
    exact hH'.1.2 h' _ (hf'.classes_le (toL2_mem_classes hφ' m0'))
  have e1 : ⟪m2.toL2, m1.toL2⟫_ℂ = 0 := (Submodule.mem_orthogonal _ _).1 (hHH a1) _ a2
  have hd := isFundamentalDomain_stdDom (latticeGL E k) μ
  rw [MemL2Quotient.inner_toL2_eq_theta_pairing, pet_eq hd m1.1 m2.1] at e1
  have hc := ContAut.continuous_of_isOpen_stab E k φ (π.cusp φ hφ).1.level
  have hc' := ContAut.continuous_of_isOpen_stab E k φ' (π'.cusp φ' hφ').1.level
  rw [QORT.band_eq hQ2 hD0 hN3 hk μ hβ _ ?_ ?_ ?_]
  · exact e1
  · exact ((hc.comp (continuous_mul_const h)).mul
      (Complex.continuous_conj.comp (hc'.comp (continuous_mul_const h')))).measurable
  · intro γ hγ g
    have a := m1.1 γ hγ g
    have b := m2.1 γ hγ g
    simp only at a b ⊢
    rw [a, b]
  · exact ((memL2_iff_fundamental_domain hd).1 m1).2.integrable_mul ((memL2_iff_fundamental_domain hd).1 m2).2.star

end PositivityTheory.AdelicQuotientData

end
