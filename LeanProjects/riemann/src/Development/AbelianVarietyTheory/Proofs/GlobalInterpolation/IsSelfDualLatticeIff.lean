import Mathlib
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LcscAdelicUnitaryGroup
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FibOfZero
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.SelfDualUnramifiedPlaces
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.DualExponentDensity
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.QuadraticUnramifiedIffInertOrSplitStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IsFieldAdicCompletionTensorOfInertStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NotIsFieldAdicCompletionTensorOfSplitStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.AdditiveCharConductorExistsStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IntegralClosureCompletedCMAlgebraCompactOpenStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.HermitianFormFiniteZerosOnLineCmExtStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsCompactOpenUnitsSubgroupContinuousSqrtStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.AddHaarMapSmulOfNormEqOneStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MeasureEqZeroOfFiniteInterLinesStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.AveragedFibreMeasureComplFibreEqZeroStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.HaarDisintegrationAveragedFibreMeasuresStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IntegrableContinuousOnAveragedFibreIntegralStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IsFibreFamilyUnivOfNullConeStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ContDensityOnEqFibreMassStatement

open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

noncomputable section
namespace GlobalTheory.LocalDensityCompare

section Top
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F))

@[reducible] def nontrivNormed : NontriviallyNormedField (Fv F v) :=
  { (inferInstance : NormedField (Fv F v)) with
    non_trivial := by
      obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot v.ne_bot
      have h1 := (NumberField.FinitePlace.norm_lt_one_iff_mem F v x).2 hx
      have h0 : NumberField.FinitePlace.embedding v (algebraMap (𝓞 F) F x) ≠ 0 := by
        rw [map_ne_zero]
        exact RingOfIntegers.coe_ne_zero_iff.2 hx0
      refine ⟨(NumberField.FinitePlace.embedding v (algebraMap (𝓞 F) F x))⁻¹, ?_⟩
      rw [norm_inv]
      exact (one_lt_inv₀ (norm_pos_iff.2 h0)).2 h1 }

theorem modTop : IsModuleTopology (Fv F v) (Fv F v ⊗[F] E) := ⟨rfl⟩
theorem topRing : IsTopologicalRing (Fv F v ⊗[F] E) :=
  haveI := modTop (E := E) v
  IsModuleTopology.isTopologicalRing (Fv F v) _
theorem lcs : LocallyCompactSpace (Fv F v ⊗[F] E) ∧ SecondCountableTopology (Fv F v ⊗[F] E) ∧
    T2Space (Fv F v ⊗[F] E) := by
  haveI := GlobalTheory.AdelicUnitaryTop.properSpace_adicCompletion F v
  obtain ⟨e⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := F) (E := E) (Fv F v)
  exact ⟨e.isClosedEmbedding.locallyCompactSpace, e.secondCountableTopology, e.isEmbedding.t2Space⟩

variable (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)

theorem continuous_q : Continuous fun X : Fin 1 → Fin M → Fv F v ⊗[F] E => qR (Fv F v) σ J (X 0) := by
  haveI := modTop (E := E) v
  haveI := topRing (E := E) v
  have h1 : Continuous (Algebra.trace (Fv F v) (Fv F v ⊗[F] E)) :=
    IsModuleTopology.continuous_of_linearMap _
  have h2 := GlobalTheory.AdelicUnitaryTop.continuous_sigR (Fv F v) σ
  unfold qR hR Formalism.UG.hform
  refine continuous_const.mul (h1.comp ?_)
  fun_prop

theorem q_smul (c : Fv F v) (X : Fin 1 → Fin M → Fv F v ⊗[F] E) :
    qR (Fv F v) σ J ((c • X) 0) = c ^ 2 * qR (Fv F v) σ J (X 0) := by
  have h : ∀ z : Fv F v ⊗[F] E, sigR (Fv F v) σ (c • z) = c • sigR (Fv F v) σ z := fun z =>
    (Algebra.TensorProduct.map (AlgHom.id (Fv F v) (Fv F v)) σ).toLinearMap.map_smul c z
  have h2 : hR (Fv F v) σ J ((c • X) 0) ((c • X) 0) = c ^ 2 • hR (Fv F v) σ J (X 0) (X 0) := by
    simp only [hR, Formalism.UG.hform, Pi.smul_apply, h, Finset.smul_sum, smul_mul_assoc, mul_smul_comm,
      smul_smul, sq]
  unfold qR
  rw [h2, map_smul, smul_eq_mul]
  ring

theorem lattice_compact_open (hσ : IsCMExt F E σ)
    (L : Submodule (GlobalTheory.IndefiniteRowSideFullHecke.PlaceSplittingTypes.maxOrder F E v) (Fin M → Fv F v ⊗[F] E)) (hfg : L.FG)
    (hsp : Submodule.span (Fv F v ⊗[F] E) (L : Set (Fin M → Fv F v ⊗[F] E)) = ⊤) :
    IsCompact (GlobalTheory.IndefiniteRowSideFullHecke.PlaceSplittingTypes.latTup v L) ∧ IsOpen (GlobalTheory.IndefiniteRowSideFullHecke.PlaceSplittingTypes.latTup v L) := by
  haveI := modTop (E := E) v
  haveI := topRing (E := E) v
  obtain ⟨hc, ho⟩ := GlobalTheory.T.integralClosure_completedCMAlgebra_compact_open F E σ hσ v
  obtain ⟨n, x, hx⟩ := Submodule.fg_iff_exists_fin_generating_family.1 hfg
  let f : (Fin n → Fv F v ⊗[F] E) →ₗ[Fv F v ⊗[F] E] (Fin M → Fv F v ⊗[F] E) :=
    Fintype.linearCombination _ x
  have hf : Function.Surjective f := by
    rw [← LinearMap.range_eq_top, Fintype.range_linearCombination, eq_top_iff, ← hsp,
      Submodule.span_le, ← hx]
    exact Submodule.span_subset_span _ _ _
  have hfo : IsOpenMap f := IsModuleTopology.isOpenMap_of_surjective
    (φ := f.restrictScalars (Fv F v)) hf
  have hfc : Continuous f := IsModuleTopology.continuous_of_linearMap (f.restrictScalars (Fv F v))
  have himg : (L : Set (Fin M → Fv F v ⊗[F] E)) = f '' Set.pi Set.univ fun _ =>
      (GlobalTheory.IndefiniteRowSideFullHecke.PlaceSplittingTypes.maxOrder F E v : Set (Fv F v ⊗[F] E)) := by
    ext y
    rw [← hx, SetLike.mem_coe, Submodule.mem_span_range_iff_exists_fun]
    constructor
    · rintro ⟨c, rfl⟩
      exact ⟨fun i => c i, fun i _ => (c i).2, rfl⟩
    · rintro ⟨c, hc, rfl⟩
      exact ⟨fun i => ⟨c i, hc i trivial⟩, rfl⟩
  have e : GlobalTheory.IndefiniteRowSideFullHecke.PlaceSplittingTypes.latTup v L = Set.pi Set.univ fun _ : Fin 1 =>
      (L : Set (Fin M → Fv F v ⊗[F] E)) := by
    ext X
    simp [GlobalTheory.IndefiniteRowSideFullHecke.PlaceSplittingTypes.latTup, Fin.forall_fin_one]
  rw [e, himg]
  exact ⟨isCompact_univ_pi fun _ => (isCompact_univ_pi fun _ => hc).image hfc,
    isOpen_set_pi Set.finite_univ fun _ _ => hfo _ (isOpen_set_pi Set.finite_univ fun _ _ => ho)⟩

theorem null_and_exists (hσ : IsCMExt F E σ) (hM : 1 ≤ M) (hJ : IsHermND σ J)
    (μ : Measure (Fin 1 → Fin M → Fv F v ⊗[F] E)) (hμ : μ.IsAddHaarMeasure)
    (ν : Measure (Fv F v)) (hν : ν.IsAddHaarMeasure) :
    μ {X | qR (Fv F v) σ J (X 0) = 0} = 0 ∧
    ∃ fib, IsFibreFamily μ (fun X => qR (Fv F v) σ J (X 0)) id Set.univ ν {c | c ≠ 0} fib := by
  haveI := modTop (E := E) v
  haveI := topRing (E := E) v
  obtain ⟨h1, h2, h3⟩ := lcs (E := E) v
  haveI := GlobalTheory.AdelicUnitaryTop.properSpace_adicCompletion F v
  letI := nontrivNormed v
  haveI : BorelSpace (Fv F v) := ⟨rfl⟩
  haveI : BorelSpace (Fv F v ⊗[F] E) := ⟨rfl⟩
  have hq := continuous_q v σ J
  have hnull : μ {X | qR (Fv F v) σ J (X 0) = 0} = 0 := by
    obtain ⟨y, hy⟩ := GlobalTheory.T.hermitian_form_finite_zeros_on_line_cmExt F E σ hσ M hM J hJ (Fv F v)
    exact GlobalTheory.T.measure_eq_zero_of_finite_inter_lines' (Fv F v) _ μ _ (isClosed_eq hq continuous_const).measurableSet (fun _ => y)
      fun x => hy (x 0)
  refine ⟨hnull, ?_⟩
  haveI : CharZero (Fv F v) := charZero_of_injective_ringHom (algebraMap F (Fv F v)).injective
  obtain ⟨U, s, hs⟩ := GlobalTheory.T.exists_compact_open_units_subgroup_continuous_sqrt (Fv F v) two_ne_zero
  refine ⟨GlobalTheory.QuadFibre.fibOf μ ν (fun X => qR (Fv F v) σ J (X 0)) U s, fun b => ?_,
    fun φ hφ => ?_, fun φ h1 h2 _ => ?_⟩
  · rw [Set.inter_univ]
    exact GlobalTheory.T.averagedFibreMeasure_compl_fibre_eq_zero (Fv F v) _ μ ν _ hq (q_smul v σ J) U s hs b
  · rw [Measure.restrict_univ]
    exact GlobalTheory.T.haar_disintegration_averagedFibreMeasures (Fv F v) _ μ ν _ hq (q_smul v σ J) U s hs (GlobalTheory.T.map_smul_addHaar_of_norm_eq_one (Fv F v) _ μ) hnull φ hφ
  · exact GlobalTheory.T.integrable_continuousOn_averagedFibreIntegral (Fv F v) _ μ ν _ hq (q_smul v σ J) U s hs φ h1 h2

end Top

section Dict
variable (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F))

theorem isEtaAt_iff (h2 : Module.finrank F E = 2) (η : ℤ) :
    GlobalTheory.IndefiniteRowSideFullHecke.PlaceSplittingTypes.IsEtaAt F E v η ↔
      GlobalTheory.IndefiniteRowSideFullHecke.SelfDualUnramifiedPlaces.UnramifiedPlace F E v ∧ (η : ℝ) = GlobalTheory.IndefiniteRowSideFullHecke.SelfDualUnramifiedPlaces.eta F E v := by
  unfold GlobalTheory.IndefiniteRowSideFullHecke.SelfDualUnramifiedPlaces.eta
  constructor
  · rintro (⟨h, rfl⟩ | ⟨h, rfl⟩)
    · exact ⟨(GlobalTheory.T.quadratic_unramified_iff_isPrime_map_or_ncard_primesOver_two F E h2 v).2 (Or.inl h), by rw [if_pos (GlobalTheory.T.isField_adicCompletion_tensor_of_inert F E h2 v h)]; simp⟩
    · exact ⟨(GlobalTheory.T.quadratic_unramified_iff_isPrime_map_or_ncard_primesOver_two F E h2 v).2 (Or.inr h), by rw [if_neg (GlobalTheory.T.not_isField_adicCompletion_tensor_of_split F E h2 v h)]; simp⟩
  · rintro ⟨h, hη⟩
    rcases (GlobalTheory.T.quadratic_unramified_iff_isPrime_map_or_ncard_primesOver_two F E h2 v).1 h with h | h
    · rw [if_pos (GlobalTheory.T.isField_adicCompletion_tensor_of_inert F E h2 v h)] at hη
      exact Or.inl ⟨h, by exact_mod_cast hη⟩
    · rw [if_neg (GlobalTheory.T.not_isField_adicCompletion_tensor_of_split F E h2 v h)] at hη
      exact Or.inr ⟨h, by exact_mod_cast hη⟩

theorem exists_eta : ∃ η : ℤ, (η : ℝ) = GlobalTheory.IndefiniteRowSideFullHecke.SelfDualUnramifiedPlaces.eta F E v := by
  unfold GlobalTheory.IndefiniteRowSideFullHecke.SelfDualUnramifiedPlaces.eta
  split_ifs
  · exact ⟨-1, by simp⟩
  · exact ⟨1, by simp⟩

theorem resCard_eq : GlobalTheory.IndefiniteRowSideFullHecke.SelfDualUnramifiedPlaces.resCard F v = (GlobalTheory.IndefiniteRowSideFullHecke.PlaceSplittingTypes.resCard F v : ℝ) := by
  unfold GlobalTheory.IndefiniteRowSideFullHecke.SelfDualUnramifiedPlaces.resCard GlobalTheory.IndefiniteRowSideFullHecke.PlaceSplittingTypes.resCard
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]

theorem maxOrder_eq :
    GlobalTheory.IndefiniteRowSideFullHecke.SelfDualUnramifiedPlaces.maxOrder F E v = (GlobalTheory.IndefiniteRowSideFullHecke.PlaceSplittingTypes.maxOrder F E v).toSubring := rfl

variable {F E}

theorem isSelfDualLattice_iff (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (L : Submodule (GlobalTheory.IndefiniteRowSideFullHecke.PlaceSplittingTypes.maxOrder F E v) (Fin M → Fv F v ⊗[F] E)) :
    GlobalTheory.IndefiniteRowSideFullHecke.SelfDualUnramifiedPlaces.IsSelfDualLattice σ J v L ↔ GlobalTheory.IndefiniteRowSideFullHecke.PlaceSplittingTypes.IsSelfDualLattice σ J v L :=
  Iff.rfl

theorem vol_eq (c : ℤ) (M : ℕ) : (GlobalTheory.IndefiniteRowSideFullHecke.SelfDualUnramifiedPlaces.resCard F v ^ c) ^ (-(M : ℝ)) =
    GlobalTheory.IndefiniteRowSideFullHecke.PlaceSplittingTypes.dualIndex F v c ^ (-(M : ℤ)) := by
  rw [resCard_eq, GlobalTheory.IndefiniteRowSideFullHecke.PlaceSplittingTypes.dualIndex, ← Real.rpow_intCast]
  simp

theorem volInt_eq (c : ℤ) : (GlobalTheory.IndefiniteRowSideFullHecke.SelfDualUnramifiedPlaces.resCard F v ^ c) ^ (-(1 / 2 : ℝ)) =
    GlobalTheory.IndefiniteRowSideFullHecke.PlaceSplittingTypes.dualIndex F v c ^ (-(1 / 2 : ℝ)) := by
  rw [resCard_eq, GlobalTheory.IndefiniteRowSideFullHecke.PlaceSplittingTypes.dualIndex]

theorem dens_eq (c : ℤ) (M : ℕ) (η : ℤ) (hη : (η : ℝ) = GlobalTheory.IndefiniteRowSideFullHecke.SelfDualUnramifiedPlaces.eta F E v) :
    (GlobalTheory.IndefiniteRowSideFullHecke.SelfDualUnramifiedPlaces.resCard F v ^ c) ^ ((1 / 2 : ℝ) - (M : ℝ)) *
      (1 - GlobalTheory.IndefiniteRowSideFullHecke.SelfDualUnramifiedPlaces.eta F E v ^ M * (GlobalTheory.IndefiniteRowSideFullHecke.SelfDualUnramifiedPlaces.resCard F v ^ M)⁻¹) =
    GlobalTheory.IndefiniteRowSideFullHecke.PlaceSplittingTypes.densityValue (GlobalTheory.IndefiniteRowSideFullHecke.PlaceSplittingTypes.dualIndex F v c) (GlobalTheory.IndefiniteRowSideFullHecke.PlaceSplittingTypes.resCard F v)
      η M := by
  rw [resCard_eq, ← hη, GlobalTheory.IndefiniteRowSideFullHecke.PlaceSplittingTypes.densityValue, GlobalTheory.IndefiniteRowSideFullHecke.PlaceSplittingTypes.dualIndex]
  simp

end Dict

theorem fib_inter {V K : Type} [MeasurableSpace V] (m : Measure V) (q : V → K) (b : K)
    (h : m (q ⁻¹' {id b} ∩ Set.univ)ᶜ = 0) (P : V → Prop) :
    m {X | q X = b ∧ P X} = m {X | P X} := by
  refine measure_congr ?_
  filter_upwards [h] with X hX
  have : q X = b := hX.1
  exact propext ⟨fun h => h.2, fun h => ⟨this, h⟩⟩

theorem localDensity_iff :
    GlobalTheory.IndefiniteRowSideFullHecke.SelfDualUnramifiedPlaces.LocalDensity ↔ GlobalTheory.IndefiniteRowSideFullHecke.PlaceSplittingTypes.SelfDualLatticeDensity := by
  constructor
  · intro h F E _ _ _ _ _ σ hσ M J hM hJ v η hη ψ hψ
    obtain ⟨hu, hη'⟩ := (isEtaAt_iff F E v hσ.2.2.1 η).1 hη
    refine ⟨GlobalTheory.T.additive_char_conductor_exists F v ψ hψ.1 hψ.2.1 hψ.2.2, fun c hc L hL μ hμ ν hν => ?_⟩
    obtain ⟨a1, a2, a3⟩ := h F E σ hσ M hM J hJ v hu ψ hψ c hc L hL μ hμ ν hν
    rw [vol_eq] at a1
    rw [volInt_eq] at a2
    refine ⟨a1, a2, fun β hβ => ?_⟩
    obtain ⟨hnull, fib0, hfib0⟩ := null_and_exists v σ J hσ hM hJ μ hμ.1 ν hν.1
    haveI := modTop (E := E) v
    haveI := topRing (E := E) v
    obtain ⟨h1, h2, h3⟩ := lcs (E := E) v
    haveI := GlobalTheory.AdelicUnitaryTop.properSpace_adicCompletion F v
    haveI : BorelSpace (Fv F v) := ⟨rfl⟩
    haveI : BorelSpace (Fv F v ⊗[F] E) := ⟨rfl⟩
    have hq := continuous_q v σ J
    have key : ∀ fib, IsFibreFamily μ (fun X => qR (Fv F v) σ J (X 0)) id Set.univ ν
        {c | c ≠ 0} fib → fib β (GlobalTheory.IndefiniteRowSideFullHecke.PlaceSplittingTypes.latTup v L) = ENNReal.ofReal
          (GlobalTheory.IndefiniteRowSideFullHecke.PlaceSplittingTypes.densityValue (GlobalTheory.IndefiniteRowSideFullHecke.PlaceSplittingTypes.dualIndex F v c)
            (GlobalTheory.IndefiniteRowSideFullHecke.PlaceSplittingTypes.resCard F v) η M) ∧
        ∀ t : Fv F v, Valued.v (t - β) < 1 →
          fib t (GlobalTheory.IndefiniteRowSideFullHecke.PlaceSplittingTypes.latTup v L) = fib β (GlobalTheory.IndefiniteRowSideFullHecke.PlaceSplittingTypes.latTup v L) := by
      intro fib hfib
      obtain ⟨b1, b2⟩ := a3 fib hfib β hβ
      rw [dens_eq v c M η hη', fib_inter _ _ _ (hfib.1 β)] at b1
      exact ⟨b1, b2⟩
    refine ⟨fun U B fib hU hB hfib => key fib
      (GlobalTheory.T.isFibreFamily_univ_of_null_cone' (Fv F v) _ μ ν _ hq hnull U B fib hU hB hfib), fun g hg t ht => ?_⟩
    obtain ⟨hLc, hLo⟩ := lattice_compact_open v σ hσ L hL.1 hL.2.1
    have ht0 : t ≠ 0 := by
      rintro rfl
      rw [zero_sub, Valuation.map_neg, hβ] at ht
      exact lt_irrefl _ ht
    haveI := hν.1
    have hpos : 0 ≤ GlobalTheory.IndefiniteRowSideFullHecke.PlaceSplittingTypes.densityValue (GlobalTheory.IndefiniteRowSideFullHecke.PlaceSplittingTypes.dualIndex F v c)
        (GlobalTheory.IndefiniteRowSideFullHecke.PlaceSplittingTypes.resCard F v) η M := by
      rw [← dens_eq v c M η hη']
      have := GlobalTheory.IndefiniteRowSideFullHecke.SelfDualUnramifiedPlaces.one_lt_resCard F v
      exact mul_nonneg (by positivity) (GlobalTheory.IndefiniteRowSideFullHecke.SelfDualUnramifiedPlaces.density_factor_pos F E v M hM).le
    rw [GlobalTheory.T.contDensity_eq_fibre_measure_of_compact_open (Fv F v) _ μ ν _ hq fib0 hfib0 _ hLc hLo g hg t ht0, (key fib0 hfib0).2 t ht,
      (key fib0 hfib0).1, ENNReal.toReal_ofReal hpos]
  · intro h F E _ _ _ _ _ σ hσ M hM J hJ v hu ψ hψ c hc L hL μ hμ ν hν
    obtain ⟨η, hη⟩ := exists_eta F E v
    obtain ⟨a1, a2, a3⟩ := (h F E σ hσ M J hM hJ v η ((isEtaAt_iff F E v hσ.2.2.1 η).2 ⟨hu, hη⟩)
      ψ hψ).2 c hc L hL μ hμ ν hν
    rw [vol_eq, volInt_eq]
    refine ⟨a1, a2, fun fib hfib β hβ => ?_⟩
    obtain ⟨b1, b2⟩ := (a3 β hβ).1 Set.univ _ fib (Set.subset_univ _) subset_rfl hfib
    rw [dens_eq v c M η hη, fib_inter _ _ _ (hfib.1 β)]
    exact ⟨b1, b2⟩

end GlobalTheory.LocalDensityCompare
