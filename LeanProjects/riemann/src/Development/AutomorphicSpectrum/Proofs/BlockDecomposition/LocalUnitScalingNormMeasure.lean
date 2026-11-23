import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsContent
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorIntegerRingAlmostAllPlaces
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.LocalRankOneDensityUniformizerPower
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSquareMulOfNonsquareUnits
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free GlobalTheory.CompanionTheory.WeilSiegel.HypStep GlobalTheory.CompanionTheory.WeilSiegel.HypMass

noncomputable section

namespace GlobalTheory.CompanionTheory.WeilSiegel.HypMass.ContentScale

section Ring

open scoped Pointwise

variable {A : Type} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [LocallyCompactSpace A]
  [MeasurableSpace A] [BorelSpace A]

theorem map_mul_unit (μ : Measure A) [μ.IsAddHaarMeasure] [μ.Regular] (u : Aˣ) :
    μ.map (fun x => (u : A) * x) = (distribHaarChar A u)⁻¹ • μ := by
  have hm : Measurable fun x : A => (u : A) * x := (continuous_const.mul continuous_id).measurable
  ext B hB
  rw [Measure.map_apply hm hB, Measure.smul_apply]
  have e : (fun x : A => (u : A) * x) ⁻¹' B = u⁻¹ • B := by
    ext y
    rw [Set.mem_smul_set_iff_inv_smul_mem]
    simp [Units.smul_def]
  rw [e, ← distribHaarChar_mul, map_inv]
  rfl

theorem exists_pos_finite (μ : Measure A) [μ.IsAddHaarMeasure] :
    ∃ K : Set A, μ K ≠ 0 ∧ μ K ≠ ∞ := by
  obtain ⟨K, hK, hn⟩ := exists_compact_mem_nhds (0 : A)
  refine ⟨K, ?_, hK.measure_lt_top.ne⟩
  exact (Measure.measure_pos_of_mem_nhds μ hn).ne'

theorem smul_inj (μ : Measure A) [μ.IsAddHaarMeasure] {a b : ℝ≥0} (h : a • μ = b • μ) : a = b := by
  obtain ⟨K, h0, h1⟩ := exists_pos_finite μ
  have e := congrArg (fun m : Measure A => m K) h
  simp only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at e
  exact ENNReal.coe_injective ((ENNReal.mul_left_inj h0 h1).1 e)

theorem char_map (s : A ≃+* A) (hs : Continuous s) (hs' : Continuous s.symm) (u : Aˣ) :
    distribHaarChar A (Units.map (s : A →* A) u) = distribHaarChar A u := by
  let H : A ≃ₜ A := ⟨s.toEquiv, hs, hs'⟩
  let μ : Measure A := Measure.addHaar
  have : (μ.map H).IsAddHaarMeasure := s.toAddEquiv.isAddHaarMeasure_map μ hs hs'
  have : (μ.map H).Regular := Measure.Regular.map H
  obtain ⟨K, h0, h1⟩ := exists_pos_finite μ
  have hap : ∀ S : Set A, (μ.map H) S = μ (H ⁻¹' S) := fun S =>
    H.toMeasurableEquiv.map_apply S
  have hpre : H ⁻¹' (H '' K) = K := H.injective.preimage_image K
  refine distribHaarChar_eq_of_measure_smul_eq_mul (μ := μ.map H) (s := H '' K)
    (by rwa [hap, hpre]) (by rwa [hap, hpre]) ?_
  rw [hap, hap, hpre, distribHaarChar_mul]
  congr 1
  ext x
  simp only [Set.mem_preimage, Set.mem_smul_set, Set.mem_image]
  constructor
  · rintro ⟨y, ⟨k, hk, rfl⟩, hy⟩
    refine ⟨k, hk, H.injective ?_⟩
    rw [← hy]
    simp [H, Units.smul_def]
  · rintro ⟨k, hk, rfl⟩
    refine ⟨H k, ⟨k, hk, rfl⟩, ?_⟩
    simp [H, Units.smul_def]

end Ring

theorem sigma_sigma {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (hσ : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  apply τ.injective
  rw [hσ.2.2.2, hσ.2.2.2, star_star]

end GlobalTheory.CompanionTheory.WeilSiegel.HypMass.ContentScale

namespace GlobalTheory.CompanionTheory.WeilSiegel.HypMass.ContentScale

theorem coordK_map_mul : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) (lam : Measure (Fv F v)), IsStdV v lam → ∀ (c : Fv F v ⊗[F] E) (t : Fv F v) (w : ℕ), IsUnit c → algebraMap (Fv F v) (Fv F v ⊗[F] E) t = sigR (Fv F v) σ c * c → ‖t‖ = ((qv v : ℝ) ^ w)⁻¹ → (coordK (Fv F v) b lam).map (fun x => c * x) = (qv v ^ w) • coordK (Fv F v) b lam := by
  intro F E _ _ _ _ _ σ hσ d b v lam hlam c t w hc ht hnorm
  haveI : BorelSpace (Fv F v) := ⟨rfl⟩
  obtain ⟨i1, i2, i3, i4, -⟩ := GlobalTheory.T.completion_is_local_ring F v
  haveI : lam.IsAddHaarMeasure := hlam.1
  obtain ⟨j1, j2, j3, j4, hsc, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hσ (Fv F v)
  haveI : BorelSpace (Fv F v ⊗[F] E) := ⟨rfl⟩
  obtain ⟨hK, -, -⟩ := GlobalTheory.T.coordinate_haar_measure F E σ hσ (Fv F v) d b lam ‹_›
  haveI := hK
  have hd : d = 2 := by
    rw [← hσ.2.2.1, Module.finrank_eq_card_basis b, Fintype.card_fin]
  subst hd
  set μ := coordK (Fv F v) b lam with hμ
  haveI : μ.Regular := inferInstance
  have hss : ∀ x, sigR (Fv F v) σ (sigR (Fv F v) σ x) = x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul r e => simp [sigR, sigma_sigma σ hσ]
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  let s : (Fv F v ⊗[F] E) ≃+* (Fv F v ⊗[F] E) :=
    { toFun := sigR (Fv F v) σ, invFun := sigR (Fv F v) σ, left_inv := hss, right_inv := hss,
      map_mul' := map_mul _, map_add' := map_add _ }
  let u : (Fv F v ⊗[F] E)ˣ := hc.unit
  have hu : (u : Fv F v ⊗[F] E) = c := hc.unit_spec
  have hchar := char_map s hsc hsc u
  have hq : (Ideal.absNorm v.asIdeal : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.2 fun h => v.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
  have hqv : (qv v : ℝ) = (Ideal.absNorm v.asIdeal : ℝ) := by simp [qv]
  have ht0 : t ≠ 0 := by
    intro h
    rw [h, norm_zero, hqv] at hnorm
    exact inv_ne_zero (pow_ne_zero w hq) hnorm.symm
  have hk : ‖t‖ = ((Ideal.absNorm v.asIdeal : ℝ))⁻¹ ^ w := by
    rw [hnorm, hqv, inv_pow]
  have h1 := GlobalTheory.CompanionTheory.SW.Dil.scale_fv v lam t ht0 w hk
  have h2 := GlobalTheory.CompanionTheory.SW.Dil.coordK_map (Fv F v) σ hσ b lam t ht0 _ h1
  have h3 := map_mul_unit μ (Units.map (s : _ →* _) u * u)
  have hval : ((Units.map (s : _ →* _) u * u : (Fv F v ⊗[F] E)ˣ) : Fv F v ⊗[F] E) =
      algebraMap (Fv F v) (Fv F v ⊗[F] E) t := by
    rw [ht, ← hu]
    rfl
  rw [hval, h2, map_mul, hchar] at h3
  have h4 := smul_inj μ h3
  have h5 : (distribHaarChar (Fv F v ⊗[F] E) u)⁻¹ = qv v ^ w := by
    refine (pow_left_inj₀ zero_le' zero_le' two_ne_zero).1 ?_
    rw [inv_pow, pow_two]
    exact h4.symm
  rw [← h5, ← map_mul_unit μ u, hu]

end GlobalTheory.CompanionTheory.WeilSiegel.HypMass.ContentScale
