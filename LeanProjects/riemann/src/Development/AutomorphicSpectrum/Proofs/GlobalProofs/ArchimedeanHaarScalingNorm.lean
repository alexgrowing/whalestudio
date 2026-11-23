import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.CoefS
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.IntegralIndicatorCharOfTrivial
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.CharEqOneOfNear
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.SelfDualMap
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.AdelicCharacterTrivialAlmostEverywhereStatement
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.LocalAnnihilatorSelfDualVolumeStatement
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.AdelicAnnihilatorBoxProductStatement
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.MemAnnihilatorSmallBallEventuallyStatement
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.FiniteAdeleBoxMeasureProductStatement
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ArchimedeanFourierApproximateIdentityStatement
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.NormalisedFourierBumpLimitStatement
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.AdelicIntegrableProductIndicatorStatement
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ExistsRealApproximateIdentityStatement
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.NumberFieldApproximateIdentityStatement
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.GaloisUnramifiedOutsideDescendsFiniteStatement

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.Hypotheses₂.OneV GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.Test
open scoped TensorProduct ENNReal NNReal

namespace GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.Test

theorem sdConst : ∀ (F : Type) [Field F] [NumberField F], NumberField.IsTotallyReal F → ∀ (laminf : Measure (Ainf F)) (lam : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fv F v)), GlobalTheory.CompanionTheory.SW.IsStdInf laminf → (∀ v, GlobalTheory.CompanionTheory.SW.IsStdV v (lam v)) → ∀ ψ, IsCharAF F ψ → ∃ (cinf : ℝ≥0) (c : HeightOneSpectrum (𝓞 F) → ℝ≥0), GlobalTheory.CompanionTheory.SW.IsUnitProd cinf c ∧ SelfDual (cinf • laminf) (fun s t => psiInf F ψ (s * t)) ∧ ∀ v : HeightOneSpectrum (𝓞 F), SelfDual (c v • lam v) (fun s t => psiV F ψ v (s * t)) := by
  intro F _ _ hF laminf lam hinf hlam ψ hψ
  obtain ⟨cinf, c, hU, h1, h2⟩ := GlobalTheory.CompanionTheory.SW.SdCoord.selfDual_coord F hF laminf lam hinf hlam ψ hψ
    Unit 1 (Matrix.isSymm_one) (by simp)
  refine ⟨cinf, c, hU, ?_, fun v => ?_⟩
  · obtain ⟨a1, a2, a3, a4, -, -, -, -⟩ := GlobalTheory.CompanionTheory.SW.isLocR_Ainf F hF
    haveI := a1; haveI := a2; haveI := a3; haveI := a4
    haveI : BorelSpace (Ainf F) := ⟨rfl⟩
    haveI := hinf.1
    exact (GlobalTheory.CompanionTheory.SW.SdAny.iff_of_unit (psiInf F ψ) laminf cinf _ (Matrix.map_one _ (map_zero _) (map_one _)) h1 _).2 rfl
  · obtain ⟨a1, a2, a3, a4, -, -, -, -⟩ := GlobalTheory.CompanionTheory.SW.LocFv.isLocR_Fv F v
    haveI := a1; haveI := a2; haveI := a3; haveI := a4
    haveI : BorelSpace (Fv F v) := ⟨rfl⟩
    haveI := (hlam v).1
    exact (GlobalTheory.CompanionTheory.SW.SdAny.iff_of_unit (psiV F ψ v) (lam v) (c v) _ (Matrix.map_one _ (map_zero _) (map_one _)) (h2 v) _).2 rfl

end GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.Test

namespace GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.Test

theorem condS_of : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsCharAF F ψ → ∀ (lam : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fv F v)) (c : HeightOneSpectrum (𝓞 F) → ℝ≥0), (∀ v, GlobalTheory.CompanionTheory.SW.IsStdV v (lam v)) → (∀ v, SelfDual (c v • lam v) (fun s t => psiV F ψ v (s * t))) → {v | c v ≠ 1}.Finite → {v : HeightOneSpectrum (𝓞 F) | annV ψ v (v.adicCompletionIntegers F : Set (Fv F v)) ≠ (v.adicCompletionIntegers F : Set (Fv F v))}.Finite := by
  intro F _ _ ψ hψ lam c hlam hsd hc1
  classical
  obtain ⟨T, hT⟩ := GlobalTheory.T.adelic_character_trivial_almost_everywhere F ψ hψ
  refine (T.finite_toSet.union hc1).subset fun v hv => ?_
  by_contra hcon
  simp only [Set.mem_union, Finset.mem_coe, Set.mem_setOf_eq, not_or, not_not] at hcon
  obtain ⟨hvT, hcv⟩ := hcon
  apply hv
  haveI : BorelSpace (Fv F v) := ⟨rfl⟩
  have hloc := GlobalTheory.CompanionTheory.SW.LocFv.isLocR_Fv F v
  haveI : IsTopologicalRing (Fv F v) := hloc.1
  haveI : SecondCountableTopology (Fv F v) := hloc.2.2.1
  haveI := (hlam v).1
  have hO : ((GlobalTheory.CompanionTheory.SW.PiV.ball v 0 : AddSubgroup (Fv F v)) : Set (Fv F v)) =
      (v.adicCompletionIntegers F : Set (Fv F v)) := by
    ext x
    change Valued.v x ≤ WithZero.exp 0 ↔ Valued.v x ≤ 1
    simp
  obtain ⟨-, -, -, hm⟩ := GlobalTheory.T.local_annihilator_self_dual_volume F ψ hψ v (lam v) (c v) (hlam v) (hsd v) (GlobalTheory.CompanionTheory.SW.PiV.ball v 0)
    (GlobalTheory.CompanionTheory.SW.PiV.ball_isCompact 0) (GlobalTheory.CompanionTheory.SW.PiV.ball_isOpen 0)
  rw [hO, hcv, (hlam v).2] at hm
  simp only [NNReal.coe_one, one_pow, ENNReal.toReal_one, mul_one, one_mul] at hm
  have hA1 : lam v (annV ψ v (v.adicCompletionIntegers F : Set (Fv F v))) = 1 := by
    have hne : lam v (annV ψ v (v.adicCompletionIntegers F : Set (Fv F v))) ≠ ⊤ := by
      intro h
      rw [h] at hm
      simp at hm
    rw [← ENNReal.ofReal_toReal hne, hm, ENNReal.ofReal_one]
  have hsub : (v.adicCompletionIntegers F : Set (Fv F v)) ⊆
      annV ψ v (v.adicCompletionIntegers F : Set (Fv F v)) := by
    intro t ht s hs
    have hx : s * t ∈ v.adicCompletionIntegers F := mul_mem hs ht
    rw [← psiF_singleV]
    have hs1 : (singleV F v (s * t)) v = s * t :=
      RestrictedProduct.single_eq_same (fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletionIntegers F) v _
    have hs2 : ∀ w, w ≠ v → (singleV F v (s * t)) w = 0 := fun w h =>
      RestrictedProduct.single_eq_of_ne (fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletionIntegers F) _ h
    refine hT _ (fun w => ?_) (fun w hw => ?_)
    · by_cases h : w = v
      · subst h
        rw [hs1]
        exact hx
      · rw [hs2 w h]
        exact zero_mem _
    · exact hs2 w fun h => hvT (h ▸ hw)
  refine (Set.Subset.antisymm ?_ hsub)
  intro t ht
  by_contra htO
  set O : Set (Fv F v) := (v.adicCompletionIntegers F : Set (Fv F v)) with hOdef
  set A : Set (Fv F v) := annV ψ v O with hAdef
  have hmO : MeasurableSet O := by
    rw [← hO]
    exact (GlobalTheory.CompanionTheory.SW.PiV.ball_isOpen 0).measurableSet
  have hshift : lam v ((fun x => -t + x) ⁻¹' O) = 1 := by
    rw [measure_preimage_add]
    exact (hlam v).2
  have hdisj : Disjoint O ((fun x => -t + x) ⁻¹' O) := by
    refine Set.disjoint_left.2 fun x hx hx' => htO ?_
    have h1 : x - (-t + x) ∈ v.adicCompletionIntegers F := sub_mem hx hx'
    have h2 : x - (-t + x) = t := by ring
    rwa [h2] at h1
  have hsub2 : (fun x => -t + x) ⁻¹' O ⊆ A := by
    intro x hx
    have h1 : t + (-t + x) ∈ annS ψ v O := (annS ψ v O).add_mem ht (hsub hx)
    have h2 : t + (-t + x) = x := by ring
    rwa [h2] at h1
  have hle : lam v (O ∪ (fun x => -t + x) ⁻¹' O) ≤ lam v A :=
    measure_mono (Set.union_subset hsub hsub2)
  rw [measure_union hdisj (hmO.preimage (measurable_const_add _)), (hlam v).2, hshift, hA1] at hle
  norm_num at hle

end GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.Test

namespace GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.Test

theorem psiInf_zero {F : Type} [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ) : psiInf F ψ 0 = 1 := by
  have h : pairA F (0 : Ainf F) 0 = 0 := rfl
  rw [psiInf, h, AddChar.map_zero_eq_one]

theorem fouInf_zero {F : Type} [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ) (lam : Measure (Ainf F))
    (ρ : Ainf F → ℝ) : fouInf ψ lam ρ 0 = ((∫ y, ρ y ∂lam : ℝ) : ℂ) := by
  simp only [fouInf, mul_zero, psiInf_zero, mul_one]
  exact integral_ofReal

theorem norm_fouA_le {F : Type} [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ) (hψ : IsCharAF F ψ)
    (db : Measure (AF F)) (ρ : Ainf F → ℝ) (hρ : ∀ y, 0 ≤ ρ y) (S : Finset (HeightOneSpectrum (𝓞 F)))
    (U : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fv F v)) (b : AF F) :
    ‖Coef.fouA ψ db (Coef.testT ρ S U) b‖ ≤ ‖∫ y, Coef.testT ρ S U y ∂db‖ := by
  set h : AF F → ℝ := fun y => ρ (fstA F y) * (Coef.boxA S U).indicator (fun _ => (1 : ℝ)) (sndA F y) with hh
  have hT : ∀ y, Coef.testT ρ S U y = ((h y : ℝ) : ℂ) := by
    intro y
    simp only [Coef.testT, hh, Set.indicator]
    split_ifs <;> simp
  have hnn : ∀ y, 0 ≤ h y := by
    intro y
    refine mul_nonneg (hρ _) (Set.indicator_nonneg (fun _ _ => zero_le_one) _)
  have h1 : ∫ y, Coef.testT ρ S U y ∂db = ((∫ y, h y ∂db : ℝ) : ℂ) := by
    simp only [hT]
    exact integral_ofReal
  rw [h1, Complex.norm_real, Real.norm_of_nonneg (integral_nonneg hnn)]
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  simp only [norm_mul, hψ.2.1, mul_one, hT, Complex.norm_real]
  exact Real.norm_of_nonneg (hnn y)

theorem inf_inversion {F : Type} [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ)
    (laminf : Measure (Ainf F)) (cinf : ℝ≥0) (hsd : SelfDual (cinf • laminf) (fun s t => psiInf F ψ (s * t)))
    (ρ : Ainf F → ℝ) (hc : Continuous ρ) (hs : HasCompactSupport ρ)
    (hI : Integrable (fouInf ψ laminf ρ) laminf) (t : Ainf F) :
    ((cinf : ℝ) : ℂ) ^ 2 * ∫ x, fouInf ψ laminf ρ x * psiInf F ψ (x * t) ∂laminf = (ρ (-t) : ℂ) := by
  have e1 : ∀ y, ∫ x, (ρ x : ℂ) * psiInf F ψ (x * y) ∂(cinf • laminf) =
      ((cinf : ℝ) : ℂ) * fouInf ψ laminf ρ y := by
    intro y
    rw [integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul]
    rfl
  have hc' : Continuous fun x => (ρ x : ℂ) := Complex.continuous_ofReal.comp hc
  have hs' : HasCompactSupport fun x => (ρ x : ℂ) := hs.comp_left (g := Complex.ofReal) (by simp)
  have h := hsd.2 (fun x => (ρ x : ℂ)) hc' hs' (by
    simp only [e1]
    exact (hI.const_mul _).smul_measure_nnreal) t
  simp only [e1] at h
  rw [integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul] at h
  rw [← h, pow_two, mul_assoc, ← integral_const_mul]
  congr 1
  refine congrArg _ (funext fun y => ?_)
  ring

theorem exists_test_approx : ∀ (F : Type) [Field F] [NumberField F], NumberField.IsTotallyReal F → ∀ ψ : AddChar (AF F) ℂ, IsCharAF F ψ → ∀ db : Measure (AF F), IsCovolOne db → ∀ (laminf : Measure (Ainf F)) (lam : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fv F v)), GlobalTheory.CompanionTheory.SW.IsStdInf laminf → (∀ v, GlobalTheory.CompanionTheory.SW.IsStdV v (lam v)) → ∃ S₁ : Finset (HeightOneSpectrum (𝓞 F)), ∀ S, S₁ ⊆ S → ∃ (ρ : ℕ → Ainf F → ℝ) (U : ℕ → ∀ v : HeightOneSpectrum (𝓞 F), Set (Fv F v)), (∀ k, Continuous (ρ k) ∧ HasCompactSupport (ρ k) ∧ (∀ y, 0 ≤ ρ k y) ∧ 0 < ∫ y, ρ k y ∂laminf) ∧ Filter.Tendsto (fun k => tsupport (ρ k)) Filter.atTop (nhds (0 : Ainf F)).smallSets ∧ (∀ k v, IsCompact (U k v) ∧ IsOpen (U k v) ∧ (0 : Fv F v) ∈ U k v) ∧ (∀ v, Filter.Tendsto (fun k => U k v) Filter.atTop (nhds (0 : Fv F v)).smallSets) ∧ (∀ k, Integrable (Coef.fouA ψ db (Coef.testT (ρ k) S (U k))) db ∧ ∀ z, ∫ b, Coef.fouA ψ db (Coef.testT (ρ k) S (U k)) b * ψ (b * z) ∂db = Coef.testT (ρ k) S (U k) (-z)) ∧ (∀ k, ∫ y, Coef.testT (ρ k) S (U k) y ∂db = ((∫ y, ρ k y ∂laminf : ℝ) : ℂ) * ∏ v ∈ S, (((lam v) (U k v)).toReal : ℂ)) ∧ (∀ k b, ‖Coef.fouA ψ db (Coef.testT (ρ k) S (U k)) b‖ ≤ ‖∫ y, Coef.testT (ρ k) S (U k) y ∂db‖) ∧ ∀ b, Filter.Tendsto (fun k => Coef.fouA ψ db (Coef.testT (ρ k) S (U k)) b / ∫ y, Coef.testT (ρ k) S (U k) y ∂db) Filter.atTop (nhds ((Coef.intF S).indicator (fun _ => (1 : ℂ)) (sndA F b))) := by
  intro F _ _ hF ψ hψ db hdb laminf lam hinf hlam
  classical
  obtain ⟨lf, hlfH, hlf1, e, he, hep⟩ := GlobalTheory.T.adelic_haar_finite_infinite_product F db hdb laminf hinf
  obtain ⟨cinf, c, hU, hsdI, hsdV⟩ := sdConst F hF laminf lam hinf hlam ψ hψ
  have hfin2 : {v | c v ≠ 1}.Finite := hU.1
  have hfin1 := condS_of F ψ hψ lam c hlam hsdV hfin2
  refine ⟨hfin1.toFinset ∪ hfin2.toFinset, fun S hS => ?_⟩
  have hSc : ∀ v, v ∉ S → annV ψ v (v.adicCompletionIntegers F : Set (Fv F v)) =
      (v.adicCompletionIntegers F : Set (Fv F v)) := fun v hv => by
    by_contra h
    exact hv (hS (Finset.mem_union_left _ (hfin1.mem_toFinset.2 h)))
  have hSc1 : ∀ v, v ∉ S → c v = 1 := fun v hv => by
    by_contra h
    exact hv (hS (Finset.mem_union_right _ (hfin2.mem_toFinset.2 h)))
  obtain ⟨ρ, hρ, hρt, hρI⟩ := GlobalTheory.T.number_field_approximate_identity GlobalTheory.T.exists_real_approximate_identity F hF ψ hψ laminf hinf.1
  haveI : ∀ v : HeightOneSpectrum (𝓞 F), BorelSpace (Fv F v) := fun v => ⟨rfl⟩
  haveI : ∀ v : HeightOneSpectrum (𝓞 F), (lam v).IsAddHaarMeasure := fun v => (hlam v).1
  have hloc := fun v => GlobalTheory.CompanionTheory.SW.LocFv.isLocR_Fv F v
  haveI : ∀ v, IsTopologicalRing (Fv F v) := fun v => (hloc v).1
  let Ub : ℕ → ∀ v : HeightOneSpectrum (𝓞 F), AddSubgroup (Fv F v) :=
    fun k v => GlobalTheory.CompanionTheory.SW.PiV.ball v (-(k : ℤ))
  have hUc : ∀ k v, IsCompact (Ub k v : Set (Fv F v)) := fun k v => GlobalTheory.CompanionTheory.SW.PiV.ball_isCompact _
  have hUo : ∀ k v, IsOpen (Ub k v : Set (Fv F v)) := fun k v => GlobalTheory.CompanionTheory.SW.PiV.ball_isOpen _
  have hdual := fun k v => GlobalTheory.T.local_annihilator_self_dual_volume F ψ hψ v (lam v) (c v) (hlam v) (hsdV v) (Ub k v) (hUc k v) (hUo k v)
  let Ua : ℕ → ∀ v : HeightOneSpectrum (𝓞 F), AddSubgroup (Fv F v) :=
    fun k v => annS ψ v (Ub k v)
  have hUac : ∀ k v, IsCompact (Ua k v : Set (Fv F v)) := fun k v => (hdual k v).2.1
  have hUao : ∀ k v, IsOpen (Ua k v : Set (Fv F v)) := fun k v => (hdual k v).2.2.1
  have hmass : ∀ (W : ∀ v : HeightOneSpectrum (𝓞 F), AddSubgroup (Fv F v)),
      (∀ v, IsCompact (W v : Set (Fv F v))) → (∀ v, IsOpen (W v : Set (Fv F v))) →
      MeasurableSet (boxS S W : Set (Af F)) ∧ lf (boxS S W : Set (Af F)) ≠ ⊤ ∧
        (lf (boxS S W : Set (Af F))).toReal = ∏ v ∈ S, (lam v (W v : Set (Fv F v))).toReal := by
    intro W hc ho
    obtain ⟨h1, h2⟩ := GlobalTheory.T.finite_adele_box_measure_product F lam hlam lf hlfH hlf1 S (fun v => (W v : Set (Fv F v)))
      (fun v => (ho v).measurableSet)
    have hne : ∀ v, lam v (W v : Set (Fv F v)) ≠ ⊤ := fun v => (hc v).measure_lt_top.ne
    refine ⟨h1, ?_, ?_⟩
    · change lf (Coef.boxA S fun v => (W v : Set (Fv F v))) ≠ ⊤
      rw [h2]
      exact ENNReal.prod_ne_top fun v _ => hne v
    · change (lf (Coef.boxA S fun v => (W v : Set (Fv F v)))).toReal = _
      rw [h2, ENNReal.toReal_prod]
  let B : ℕ → AddSubgroup (Af F) := fun k => boxS S (Ub k)
  let B' : ℕ → AddSubgroup (Af F) := fun k => boxS S (Ua k)
  have hB : ∀ k, annF ψ (B k : Set (Af F)) = (B' k : Set (Af F)) := fun k =>
    GlobalTheory.T.adelic_annihilator_box_product F ψ hψ S hSc (fun v => (Ub k v : Set (Fv F v))) (fun v => (Ub k v).zero_mem)
  have hB' : ∀ k, annF ψ (B' k : Set (Af F)) = (B k : Set (Af F)) := fun k => by
    refine (GlobalTheory.T.adelic_annihilator_box_product F ψ hψ S hSc (fun v => (Ua k v : Set (Fv F v))) (fun v => (Ua k v).zero_mem)).trans ?_
    change Coef.boxA S (fun v => annV ψ v (annV ψ v (Ub k v))) = _
    simp only [fun v => (hdual k v).1]
    rfl
  have hBm := fun k => hmass (Ub k) (hUc k) (hUo k)
  have hBm' := fun k => hmass (Ua k) (hUac k) (hUao k)
  have hfou : ∀ k b, Coef.fouA ψ db (Coef.testT (ρ k) S (fun v => (Ub k v : Set (Fv F v)))) b =
      fouInf ψ laminf (ρ k) (fstA F b) * (((lf (B k : Set (Af F))).toReal : ℝ) : ℂ) *
        (B' k : Set (Af F)).indicator (fun _ => (1 : ℂ)) (sndA F b) := by
    intro k b
    have h := GlobalTheory.T.adelic_integral_product_subgroup F ψ hψ db laminf lf hinf.1 hlfH e he hep (fun x => (ρ k x : ℂ)) (B k)
      (hBm k).1 (hBm k).2.1 b
    rw [hB k] at h
    exact h
  have hint : ∀ k, ∫ y, Coef.testT (ρ k) S (fun v => (Ub k v : Set (Fv F v))) y ∂db =
      ((∫ y, ρ k y ∂laminf : ℝ) : ℂ) * (((lf (B k : Set (Af F))).toReal : ℝ) : ℂ) := by
    intro k
    have h := hfou k 0
    have h0 : (0 : Af F) ∈ (B' k : Set (Af F)) := (B' k).zero_mem
    simp only [map_zero, fouInf_zero, Set.indicator_of_mem h0, mul_one, Coef.fouA, mul_zero,
      AddChar.map_zero_eq_one] at h
    exact h
  have hκ : ∀ k, ((lf (B k : Set (Af F))).toReal : ℝ) ≠ 0 := by
    intro k
    rw [(hBm k).2.2]
    refine Finset.prod_ne_zero_iff.2 fun v _ => ?_
    refine (ENNReal.toReal_pos ?_ (hUc k v).measure_lt_top.ne).ne'
    exact ((hUo k v).measure_pos (lam v) ⟨0, (Ub k v).zero_mem⟩).ne'
  have hconst : ∀ k, (lf (B k : Set (Af F))).toReal * (lf (B' k : Set (Af F))).toReal = (cinf : ℝ) ^ 2 := by
    intro k
    have hP : (∏ v ∈ S, (c v : ℝ)) ^ 2 * ((lf (B k : Set (Af F))).toReal * (lf (B' k : Set (Af F))).toReal) = 1 := by
      rw [(hBm k).2.2, (hBm' k).2.2, ← Finset.prod_pow, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
      refine Finset.prod_eq_one fun v _ => ?_
      have := (hdual k v).2.2.2
      rw [← mul_assoc]
      exact this
    have hcp : (cinf : ℝ) * ∏ v ∈ S, (c v : ℝ) = 1 := by
      have h2 : ∏ᶠ v, c v = ∏ v ∈ S, c v := finprod_eq_prod_of_mulSupport_subset _ (fun v hv => by
        by_contra h
        exact hv (hSc1 v h))
      have h3 := hU.2
      rw [h2] at h3
      exact_mod_cast h3
    calc (lf (B k : Set (Af F))).toReal * (lf (B' k : Set (Af F))).toReal
        = ((cinf : ℝ) * ∏ v ∈ S, (c v : ℝ)) ^ 2 * ((lf (B k : Set (Af F))).toReal * (lf (B' k : Set (Af F))).toReal) := by
          rw [hcp]; ring
      _ = (cinf : ℝ) ^ 2 * ((∏ v ∈ S, (c v : ℝ)) ^ 2 * ((lf (B k : Set (Af F))).toReal * (lf (B' k : Set (Af F))).toReal)) := by ring
      _ = (cinf : ℝ) ^ 2 := by rw [hP, mul_one]
  have hcinf : (cinf : ℝ) ≠ 0 := by
    intro h0
    have h3 := hU.2
    have : cinf = 0 := by exact_mod_cast h0
    rw [this, zero_mul] at h3
    exact zero_ne_one h3
  refine ⟨ρ, fun k v => (Ub k v : Set (Fv F v)), hρ, hρt, fun k v => ⟨hUc k v, hUo k v, (Ub k v).zero_mem⟩,
    ?_, fun k => ⟨?_, fun z => ?_⟩, fun k => ?_, fun k b => ?_, fun b => ?_⟩
  · intro v
    refine Filter.tendsto_smallSets_iff.2 fun t ht => ?_
    obtain ⟨m, hm⟩ := GlobalTheory.CompanionTheory.SW.PiV.exists_ball_subset t ht
    filter_upwards [Filter.eventually_ge_atTop (-m).toNat] with k hk
    refine (GlobalTheory.CompanionTheory.SW.PiV.ball_le ?_).trans hm
    omega
  · have : Coef.fouA ψ db (Coef.testT (ρ k) S (fun v => (Ub k v : Set (Fv F v)))) =
        fun b => (((lf (B k : Set (Af F))).toReal : ℝ) : ℂ) * (fouInf ψ laminf (ρ k) (fstA F b) *
          (B' k : Set (Af F)).indicator (fun _ => (1 : ℂ)) (sndA F b)) := by
      funext b
      rw [hfou]
      ring
    rw [this]
    exact (GlobalTheory.T.adelic_integrable_product_indicator F db laminf lf hinf.1 hlfH e he hep _ _ (hρI k) (hBm' k).1 (hBm' k).2.1).const_mul _
  · have h1 : ∀ b, Coef.fouA ψ db (Coef.testT (ρ k) S (fun v => (Ub k v : Set (Fv F v)))) b * ψ (b * z) =
        (((lf (B k : Set (Af F))).toReal : ℝ) : ℂ) * ((fouInf ψ laminf (ρ k) (fstA F b) *
          (B' k : Set (Af F)).indicator (fun _ => (1 : ℂ)) (sndA F b)) * ψ (b * z)) := by
      intro b
      rw [hfou]
      ring
    simp only [h1]
    rw [integral_const_mul, GlobalTheory.T.adelic_integral_product_subgroup F ψ hψ db laminf lf hinf.1 hlfH e he hep _ (B' k) (hBm' k).1 (hBm' k).2.1 z,
      hB' k]
    have hinv := inf_inversion ψ laminf cinf hsdI (ρ k) (hρ k).1 (hρ k).2.1 (hρI k) (fstA F z)
    have hz : (sndA F (-z) ∈ (B k : Set (Af F))) ↔ sndA F z ∈ (B k : Set (Af F)) := by
      rw [map_neg]
      exact (B k).neg_mem_iff
    have hc2 : ((lf (B k : Set (Af F))).toReal : ℂ) * ((lf (B' k : Set (Af F))).toReal : ℂ) = ((cinf : ℝ) : ℂ) ^ 2 := by
      exact_mod_cast hconst k
    have hT : Coef.testT (ρ k) S (fun v => (Ub k v : Set (Fv F v))) (-z) =
        (ρ k (-(fstA F z)) : ℂ) * (B k : Set (Af F)).indicator (fun _ => (1 : ℂ)) (sndA F z) := by
      simp only [Coef.testT, map_neg]
      congr 1
      by_cases h : sndA F z ∈ (B k : Set (Af F))
      · rw [Set.indicator_of_mem h]
        exact Set.indicator_of_mem ((B k).neg_mem h) _
      · rw [Set.indicator_of_notMem h]
        exact Set.indicator_of_notMem (fun h' => h (by simpa using (B k).neg_mem h')) _
    rw [hT, ← hinv, ← hc2]
    ring
  · rw [hint k, (hBm k).2.2]
    push_cast
    rfl
  · exact norm_fouA_le ψ hψ db (ρ k) (hρ k).2.2.1 S _ b
  · have hr : ∀ k, Coef.fouA ψ db (Coef.testT (ρ k) S (fun v => (Ub k v : Set (Fv F v)))) b /
        ∫ y, Coef.testT (ρ k) S (fun v => (Ub k v : Set (Fv F v))) y ∂db =
        fouInf ψ laminf (ρ k) (fstA F b) / ((∫ y, ρ k y ∂laminf : ℝ) : ℂ) *
          (B' k : Set (Af F)).indicator (fun _ => (1 : ℂ)) (sndA F b) := by
      intro k
      have hk : (((lf (B k : Set (Af F))).toReal : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hκ k
      have hk2 : ((∫ y, ρ k y ∂laminf : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (hρ k).2.2.2.ne'
      rw [hfou, hint]
      field_simp
    simp only [hr]
    have hlim := GlobalTheory.T.archimedean_fourier_approximate_identity F ψ hψ laminf hinf.1 ρ hρ hρt (fstA F b)
    by_cases hb : sndA F b ∈ Coef.intF S
    · rw [Set.indicator_of_mem hb]
      refine hlim.congr' ?_
      have hev : ∀ᶠ k : ℕ in Filter.atTop, ∀ v ∈ S, (sndA F b) v ∈ annV ψ v (Ub k v : Set (Fv F v)) :=
        (Filter.eventually_all_finset S).2 fun v _ => GlobalTheory.T.mem_annihilator_small_ball_eventually F ψ hψ v _
      filter_upwards [hev] with k hk
      have hm : sndA F b ∈ (B' k : Set (Af F)) := ⟨hk, hb⟩
      rw [Set.indicator_of_mem hm, mul_one]
    · rw [Set.indicator_of_notMem hb]
      have h0 : ∀ k, sndA F b ∉ (B' k : Set (Af F)) := fun k hm => hb hm.2
      simp only [fun k => Set.indicator_of_notMem (h0 k) (fun _ => (1 : ℂ)), mul_zero]
      exact tendsto_const_nhds

end GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.Test
