import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HypOneZeroZero
import Development.WeilBound.CoreStatements.ThetaDilations.ThetaLint
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelicTupleCompactSetsStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ThetaMeasureNonzeroVectorsBoundStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelicUnitaryGroupProjectionsStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelicTupleProjectionsStatement
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.FreeOpen
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.TopoAF

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free

noncomputable section

namespace GlobalTheory.CompanionTheory.WeilSiegel.Free.ThetaFrame

theorem free_act {S : Type} [CommRing S] {M n : ℕ} (g : GL (Fin M) S) {Y : Fin n → Fin M → S}
    (hY : LinearIndependent S Y) :
    LinearIndependent S fun a => (g : Matrix (Fin M) (Fin M) S) *ᵥ Y a := by
  have hk : LinearMap.ker (Matrix.mulVecLin (g : Matrix (Fin M) (Fin M) S)) = ⊥ := by
    rw [LinearMap.ker_eq_bot]
    intro x y h
    have h2 := congrArg (Matrix.mulVec ((g⁻¹ : GL (Fin M) S) : Matrix (Fin M) (Fin M) S)) h
    simpa [Matrix.mulVec_mulVec] using h2
  exact hY.map' _ hk

theorem free_of_unit {S : Type} [CommRing S] {M : ℕ} {Y : Fin 1 → Fin M → S} {i : Fin M}
    (hu : IsUnit (Y 0 i)) : LinearIndependent S Y := by
  rw [Fintype.linearIndependent_iff]
  intro g hg a
  have h1 := congrFun hg i
  simp only [Fin.sum_univ_one, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h1
  rw [Subsingleton.elim a 0]
  exact hu.mul_left_eq_zero.1 h1

section Rat

variable {F E : Type} [Field F] [Field E] [Algebra F E]

theorem free_ratTup (R : Type) [CommRing R] [Algebra F R] {M : ℕ} {X : Fin 1 → Fin M → E}
    (hX : LinearIndependent E X) : LinearIndependent (R ⊗[F] E) (ratTup (F := F) R X) := by
  obtain ⟨i, hi⟩ := Function.ne_iff.1 (hX.ne_zero 0)
  exact free_of_unit (i := i) ((isUnit_iff_ne_zero.2 hi).map (inclR (F := F) R))

variable [NumberField F]

theorem projInf_ratTup {M n : ℕ} (X : Fin n → Fin M → E) :
    projInf (ratTup (F := F) (AF F) X) = ratTup (Ainf F) X := by
  funext a i
  simp [projInf, ratTup, inclR]

theorem projV_ratTup (v : HeightOneSpectrum (𝓞 F)) {M n : ℕ} (X : Fin n → Fin M → E) :
    projV v (projFin (ratTup (F := F) (AF F) X)) = ratTup (Fv F v) X := by
  funext a i
  simp [projV, projFin, ratTup, inclR]

theorem act_rat_free {σ : E →ₐ[F] E} {M n : ℕ} {J : Matrix (Fin M) (Fin M) E} (γ : HFinIn (AF F) σ J)
    {X : Fin n → Fin M → E} (hX : LinearIndependent E X) :
    ∃ X' : Fin n → Fin M → E, LinearIndependent E X' ∧
      actW (AF F) σ J γ.1 (ratTup (AF F) X) = ratTup (AF F) X' := by
  obtain ⟨γ, g, -, e⟩ := γ
  refine ⟨fun a => g.val *ᵥ X a, free_act g hX, funext fun a => funext fun i => ?_⟩
  have e' : (HA.mat (AF F) σ J γ).val = g.val.map (inclR (AF F)) := (congrArg Units.val e).symm
  simp only [actW, actTup, e', ratTup, Matrix.mulVec, dotProduct, Matrix.map_apply, map_sum, map_mul]

end Rat

theorem theta_inv_of_stable (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (hcm : IsCMExt F E σ) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (hJ : IsHermND σ J)
    (μ : Measure (HA (AF F) σ J)) (𝓕 : Set (HA (AF F) σ J)) (hμ : IsHaarH F E σ M J μ)
    (h𝓕 : IsFDH F E σ M J μ 𝓕) (n : ℕ) (S : Set (Fin n → Fin M → E))
    (hS : ∀ (γ : HFinIn (AF F) σ J) (X : Fin n → Fin M → E), X ∈ S →
      ∃ X' ∈ S, actW (AF F) σ J γ.1 (ratTup (AF F) X) = ratTup (AF F) X')
    (h : HA (AF F) σ J) :
    (thetaMeas σ J μ 𝓕 S).map (actW (AF F) σ J h) = thetaMeas σ J μ 𝓕 S := by
  obtain ⟨⟨_, _, _⟩, -⟩ := GlobalTheory.T.adeles_locally_compact_second_countable F
  obtain ⟨_, _, _, _, -, -, -, hB, -, hg⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hcm (AF F)
  have := hB n M
  obtain ⟨_, _, _, _, _, hact⟩ := GlobalTheory.T.adelic_unitary_group_locally_compact F E σ hcm M J hJ (AF F)
  obtain ⟨ac, a1, a2, ag⟩ := hact n
  have hl := PositivityTheory.PlacePermOperatorBicommutantSpan.theta_lint F E σ hcm M J hJ μ 𝓕 hμ h𝓕 n S
  have hinj : Function.Injective (inclR (F := F) (E := E) (AF F)) :=
    Algebra.TensorProduct.includeRight_injective (AdeleRing.algebraMap_injective _ _)
  have hri : Function.Injective (ratTup (F := F) (AF F) : (Fin n → Fin M → E) → _) := fun X Y h =>
    funext fun a => funext fun i => hinj (congrFun (congrFun h a) i)
  have hm : Measurable (actW (AF F) σ J h : (Fin n → Fin M → _) → _) :=
    (ac.comp (continuous_const.prodMk continuous_id)).measurable
  have hfin := ((GlobalTheory.T.unitary_group_finite_volume F E σ hcm M J hJ).2 μ hμ).2 𝓕 h𝓕
  have : μ.IsHaarMeasure := hμ
  let Γ : Subgroup (HA (AF F) σ J) := HFinIn (AF F) σ J
  have : Countable Γ := (GlobalTheory.T.arithmetic_unitary_group_discrete F E σ hcm M J hJ).1
  have h𝓕' : IsFundamentalDomain Γ 𝓕 μ := h𝓕
  obtain ⟨-, _, -⟩ := GlobalTheory.T.finite_covolume_unimodular (HA (AF F) σ J) Γ μ 𝓕 h𝓕' hfin
  refine Measure.ext_of_lintegral _ fun Φ hΦ => ?_
  rw [lintegral_map hΦ hm, hl (fun X => Φ (actW (AF F) σ J h X)) (hΦ.comp hm), hl _ hΦ]
  congr 1
  set f : HA (AF F) σ J → ℝ≥0∞ := fun g => ∑' X : S,
    Φ (actW (AF F) σ J g⁻¹ (ratTup (AF F) (X : Fin n → Fin M → E))) with hf
  have hle : ∀ (γ : Γ) g, f (γ • g) ≤ f g := fun γ g => by
    choose t hts ht using fun X : S => hS γ⁻¹ X.1 X.2
    have ht' : ∀ X, actW (AF F) σ J (γ : HA (AF F) σ J)⁻¹ (ratTup (AF F) X.1) = ratTup (AF F) (t X) := ht
    have hti : Function.Injective fun X => (⟨t X, hts X⟩ : S) := fun X Y e => by
      have h1 := congrArg (actW (AF F) σ J γ) ((ht' X).trans ((congrArg (fun Z => ratTup (AF F) Z.1) e).trans (ht' Y).symm))
      simp only [← a2, mul_inv_cancel, a1] at h1
      exact Subtype.ext (hri h1)
    refine le_trans (le_of_eq (tsum_congr fun X => ?_)) (ENNReal.tsum_comp_le_tsum_of_injective hti _)
    rw [Subgroup.smul_def, smul_eq_mul, mul_inv_rev, a2, ht']
  have hinv : ∀ (γ : Γ) g, f (γ • g) = f g := fun γ g =>
    (hle γ g).antisymm (by simpa using hle γ⁻¹ (γ • g))
  have hD := h𝓕'.preimage_of_equiv (measurePreserving_mul_right μ h).quasiMeasurePreserving (e := id)
    Function.bijective_id fun γ g => (mul_assoc _ _ _)
  rw [h𝓕'.setLIntegral_eq hD f hinv, ← (measurePreserving_mul_right μ h).setLIntegral_comp_preimage_emb
    (measurableEmbedding_mulRight _)]
  simp only [hf, mul_inv_rev, ← a2, mul_inv_cancel_left]

theorem measurableSet_free (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (hcm : IsCMExt F E σ) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) :
    MeasurableSet {X : Fin 1 → Fin M → AF F ⊗[F] E | gramR (AF F) σ J X = (0 : Matrix (Fin 1) (Fin 1) E).map (inclR (AF F)) ∧
      LinearIndependent (Ainf F ⊗[F] E) (projInf X) ∧ ∀ v, LinearIndependent (Fv F v ⊗[F] E) (projV v (projFin X))} := by
  obtain ⟨⟨_, _, _⟩, -⟩ := GlobalTheory.T.adeles_locally_compact_second_countable F
  obtain ⟨_, _, _, _, -, -, -, hB, -, hg⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hcm (AF F)
  have := hB 1 M
  have : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hcm.2.2.1]; norm_num)
  obtain ⟨c1, c2, c3, -⟩ := GlobalTheory.T.adelic_tuple_projections F E σ hcm _ (Module.finBasis F E) 1 M
  have o1 : IsOpen {X : Fin 1 → Fin M → Ainf F ⊗[F] E | LinearIndependent (Ainf F ⊗[F] E) X} :=
    PI.VolStabSW.TensAllW.isOpen_linIndep (Module.finBasis F E) (Ainf F) (PI.VolStabSW.isOpen_units_Ainf F)
      (PI.VolStabSW.lip_ainf F)
  have o2 : ∀ v, IsOpen {X : Fin 1 → Fin M → Fv F v ⊗[F] E | LinearIndependent (Fv F v ⊗[F] E) X} := fun v =>
    PI.VolStabSW.TensAllW.isOpen_linIndep (Module.finBasis F E) (Fv F v) (PI.VolStabSW.isOpen_units_Fv F v)
      (PI.VolStabSW.TensAllW.lip_field _)
  have m1 : MeasurableSet {X : Fin 1 → Fin M → AF F ⊗[F] E | gramR (AF F) σ J X = (0 : Matrix (Fin 1) (Fin 1) E).map (inclR (AF F))} :=
    (isClosed_eq (hg 1 M J) continuous_const).measurableSet
  have m2 : MeasurableSet {X : Fin 1 → Fin M → AF F ⊗[F] E | LinearIndependent (Ainf F ⊗[F] E) (projInf X)} :=
    (o1.preimage c1).measurableSet
  have m3 : MeasurableSet {X : Fin 1 → Fin M → AF F ⊗[F] E | ∀ v, LinearIndependent (Fv F v ⊗[F] E) (projV v (projFin X))} := by
    rw [Set.setOf_forall]
    exact MeasurableSet.iInter fun v => (((o2 v).preimage (c3 v)).preimage c2).measurableSet
  exact m1.inter (m2.inter m3)

theorem theta_frames_zero : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → 3 ≤ M → ∀ (μ : Measure (HA (AF F) σ J)) (𝓕 : Set (HA (AF F) σ J)), IsHaarH F E σ M J μ → IsFDH F E σ M J μ 𝓕 → IsLocallyFiniteMeasure (thetaMeas σ J μ 𝓕 (framesE σ J (0 : Matrix (Fin 1) (Fin 1) E))) ∧ (∀ h : HA (AF F) σ J, (thetaMeas σ J μ 𝓕 (framesE σ J (0 : Matrix (Fin 1) (Fin 1) E))).map (actW (AF F) σ J h) = thetaMeas σ J μ 𝓕 (framesE σ J (0 : Matrix (Fin 1) (Fin 1) E))) ∧ thetaMeas σ J μ 𝓕 (framesE σ J (0 : Matrix (Fin 1) (Fin 1) E)) {X : Fin 1 → Fin M → AF F ⊗[F] E | gramR (AF F) σ J X = (0 : Matrix (Fin 1) (Fin 1) E).map (inclR (AF F)) ∧ LinearIndependent (Ainf F ⊗[F] E) (projInf X) ∧ ∀ v, LinearIndependent (Fv F v ⊗[F] E) (projV v (projFin X))}ᶜ = 0 := by
  intro F E _ _ _ _ _ σ hcm M J hJ hM μ 𝓕 hμ h𝓕
  obtain ⟨⟨_, _, _⟩, -⟩ := GlobalTheory.T.adeles_locally_compact_second_countable F
  obtain ⟨_, _, _, _, -, -, -, hB, -, hg⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hcm (AF F)
  have := hB 1 M
  obtain ⟨_, _, _, _, _, hact⟩ := GlobalTheory.T.adelic_unitary_group_locally_compact F E σ hcm M J hJ (AF F)
  obtain ⟨ac, a1, a2, ag⟩ := hact 1
  have hrat := (GlobalTheory.T.gram_matrix_local_global F E σ hcm M J hJ 1 0 0).2
  obtain ⟨pinf, p, hp, -, -⟩ := GlobalTheory.T.adelic_unitary_group_projections F E σ hcm M J hJ
  have hl := PositivityTheory.PlacePermOperatorBicommutantSpan.theta_lint F E σ hcm M J hJ μ 𝓕 hμ h𝓕 1
  have hinj : Function.Injective (inclR (F := F) (E := E) (AF F)) :=
    Algebra.TensorProduct.includeRight_injective (AdeleRing.algebraMap_injective _ _)
  refine ⟨⟨fun X => ?_⟩, fun h => ?_, ?_⟩
  · obtain ⟨K, hK, hX⟩ := exists_compact_mem_nhds X
    obtain ⟨N, r, hN, hr, hsub⟩ := (GlobalTheory.T.adelic_tuple_compact_sets F E σ hcm _ (Module.finBasis F E) 1 M).2 K hK
    obtain ⟨C, hC⟩ := GlobalTheory.T.theta_measure_nonzero_vectors_bound F E σ hcm M J hJ hM _ (Module.finBasis F E) μ 𝓕 hμ h𝓕 N hN
    refine ⟨K, hX, lt_of_le_of_lt (le_trans ?_ ((measure_mono hsub).trans (hC r hr))) ENNReal.ofReal_lt_top⟩
    have hm : Measurable (K.indicator (1 : (Fin 1 → Fin M → AF F ⊗[F] E) → ℝ≥0∞)) := measurable_one.indicator hK.measurableSet
    rw [← lintegral_indicator_one hK.measurableSet, ← lintegral_indicator_one hK.measurableSet,
      hl _ _ hm, hl _ _ hm]
    have hs : framesE σ J (0 : Matrix (Fin 1) (Fin 1) E) ⊆ {X | X ≠ 0} :=
      fun X hX h0 => hX.1.ne_zero 0 (congrFun h0 0)
    exact mul_le_mul_right (lintegral_mono fun h => ENNReal.tsum_mono_subtype (fun X => K.indicator
      (1 : (Fin 1 → Fin M → AF F ⊗[F] E) → ℝ≥0∞) (actW (AF F) σ J h⁻¹ (ratTup (AF F) X))) hs) _
  · refine theta_inv_of_stable F E σ hcm M J hJ μ 𝓕 hμ h𝓕 1 _ (fun γ X hX => ?_) h
    obtain ⟨X', hX', e⟩ := act_rat_free γ hX.1
    refine ⟨X', ⟨hX', ?_⟩, e⟩
    refine Matrix.map_injective hinj ?_
    show (gramE σ J X').map (inclR (AF F)) = (0 : Matrix (Fin 1) (Fin 1) E).map (inclR (AF F))
    rw [← hrat, ← e]
    refine (ag _ _).trans ?_
    rw [hrat, hX.2]
  · have hc := (measurableSet_free F E σ hcm M J).compl
    rw [← lintegral_indicator_one hc, hl _ _ (measurable_one.indicator hc)]
    have e : ∀ (h : HA (AF F) σ J) (X : framesE σ J (0 : Matrix (Fin 1) (Fin 1) E)), Set.indicator
        {X : Fin 1 → Fin M → AF F ⊗[F] E | gramR (AF F) σ J X = (0 : Matrix (Fin 1) (Fin 1) E).map (inclR (AF F)) ∧
          LinearIndependent (Ainf F ⊗[F] E) (projInf X) ∧ ∀ v, LinearIndependent (Fv F v ⊗[F] E) (projV v (projFin X))}ᶜ
        (1 : (Fin 1 → Fin M → AF F ⊗[F] E) → ℝ≥0∞)
        (actW (AF F) σ J h⁻¹ (ratTup (AF F) X.1)) = 0 := fun h X => by
      apply Set.indicator_of_notMem
      rw [Set.notMem_compl_iff]
      refine ⟨?_, ?_, fun v => ?_⟩
      · rw [ag, hrat, X.2.2]
      · rw [(hp 1 h⁻¹ _).1, projInf_ratTup]
        exact free_act (HA.mat (Ainf F) σ J (pinf h⁻¹)) (free_ratTup _ X.2.1)
      · rw [(hp 1 h⁻¹ _).2 v, projV_ratTup]
        exact free_act (HA.mat (Fv F v) σ J (p v h⁻¹)) (free_ratTup _ X.2.1)
    simp only [e, tsum_zero, lintegral_zero, mul_zero]

end GlobalTheory.CompanionTheory.WeilSiegel.Free.ThetaFrame
