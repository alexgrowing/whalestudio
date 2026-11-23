import Mathlib
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.HypJ
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorLocallyCompactRingStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelesLocallyCompactSecondCountable
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GroupActionHaarScalingContinuousStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelicHaarScalingByRealIdeleStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.HaarScalingUnderFlowStatement

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.FChi

theorem continuous_norm_tensor {F E : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
    (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R]
    [IsTopologicalRing (R ⊗[F] E)] :
    Continuous (Algebra.norm R : R ⊗[F] E → R) := by
  classical
  haveI : IsModuleTopology R (R ⊗[F] E) := ⟨rfl⟩
  let B := Algebra.TensorProduct.basis R (Module.finBasis F E)
  have h : (fun y : R ⊗[F] E => Algebra.norm R y) = fun y => (Algebra.leftMulMatrix B y).det := by
    funext y; exact Algebra.norm_eq_matrix_det B y
  change Continuous (fun y : R ⊗[F] E => Algebra.norm R y)
  rw [h]
  refine Continuous.matrix_det ?_
  refine continuous_matrix fun i j => ?_
  let L : (R ⊗[F] E) →ₗ[R] R :=
    (Matrix.entryLinearMap R R i j) ∘ₗ (Algebra.leftMulMatrix B).toLinearMap
  exact IsModuleTopology.continuous_of_linearMap L

theorem norm_tmul_one {F E : Type} [Field F] [Field E] [Algebra F E]
    (h2 : Module.finrank F E = 2) (R : Type) [CommRing R] [Nontrivial R] [Algebra F R] (r : R) :
    Algebra.norm R (r ⊗ₜ[F] (1 : E)) = r ^ 2 := by
  classical
  haveI : FiniteDimensional F E := Module.finite_of_finrank_pos (by omega)
  have e : r ⊗ₜ[F] (1 : E) = algebraMap R (R ⊗[F] E) r := by
    simp [Algebra.TensorProduct.algebraMap_apply]
  rw [e, Algebra.norm_algebraMap, Module.finrank_baseChange, h2]

theorem map_scale_adele {F : Type} [Field F] [NumberField F] (hF : IsTotallyReal F)
    (θ : ℝ →+* Ainf F) (hθ : Continuous θ) (μA : Measure (AF F)) (hA : μA.IsAddHaarMeasure)
    (t : ℝ) (ht : 0 < t) :
    μA.map (fun y => pairA F (θ t) 1 * y) =
      ENNReal.ofReal ((t ^ Module.finrank ℚ F)⁻¹) • μA := by
  obtain ⟨⟨lcA, scA, t2A⟩, -⟩ := GlobalTheory.CompanionTheory.AdeleTop.adele_top F
  haveI : BorelSpace (AF F) := ⟨rfl⟩
  let μ' : Measure (Unit → AF F) := Measure.pi fun _ => μA
  haveI : μ'.IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  have h := GlobalTheory.T.adelic_haar_scaling_by_real_idele F hF θ hθ Unit μ' t ht
  have he : μ'.map (MeasurableEquiv.funUnique Unit (AF F)) = μA :=
    (measurePreserving_funUnique μA Unit).map_eq
  have hf : Measurable (fun y : AF F => pairA F (θ t) 1 * y) :=
    (continuous_const.mul continuous_id).measurable
  have hg : Measurable (fun (x : Unit → AF F) (i : Unit) =>
      (show AdeleRing (𝓞 F) F from (θ t, 1)) * x i) :=
    measurable_pi_lambda _ fun i =>
      (continuous_const.mul (continuous_apply i)).measurable
  have hc : (fun y : AF F => pairA F (θ t) 1 * y) ∘ (MeasurableEquiv.funUnique Unit (AF F)) =
      (MeasurableEquiv.funUnique Unit (AF F)) ∘ (fun (x : Unit → AF F) (i : Unit) =>
        (show AdeleRing (𝓞 F) F from (θ t, 1)) * x i) := rfl
  calc μA.map (fun y => pairA F (θ t) 1 * y)
      = (μ'.map (MeasurableEquiv.funUnique Unit (AF F))).map (fun y => pairA F (θ t) 1 * y) := by
        rw [he]
    _ = (μ'.map (fun (x : Unit → AF F) (i : Unit) =>
          (show AdeleRing (𝓞 F) F from (θ t, 1)) * x i)).map
          (MeasurableEquiv.funUnique Unit (AF F)) := by
        rw [Measure.map_map hf (MeasurableEquiv.measurable _),
          Measure.map_map (MeasurableEquiv.measurable _) hg, hc]
    _ = ENNReal.ofReal ((t ^ Module.finrank ℚ F)⁻¹) • μA := by
        rw [h, Measure.map_smul, he]
        simp

theorem exists_modulus_chi : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ τ : Multiplicative ℝ →* (AF F ⊗[F] E)ˣ, IsFlow τ →
    ∀ (M : ℕ) (μW : Measure (Fin 1 → Fin M → AF F ⊗[F] E)) (μA : Measure (AF F)),
    μW.IsAddHaarMeasure → μA.IsAddHaarMeasure →
    ∃ χ : (AF F ⊗[F] E)ˣ →* ℝ≥0, Continuous χ ∧
      (∀ a : (AF F ⊗[F] E)ˣ, (μW.prod μA).map (fun p =>
        (sigR (AF F) σ (a : AF F ⊗[F] E) • p.1, Algebra.norm (AF F) (a : AF F ⊗[F] E) * p.2)) =
          χ a • μW.prod μA) ∧
      ∀ x : ℝ, (χ (τ (Multiplicative.ofAdd x)) : ℝ) =
        Real.exp (-(2 * Module.finrank ℚ F * (M + 1) * x)) := by
  intro F E _ _ _ _ _ σ hCM τ hτ M μW μA hW hA
  obtain ⟨⟨lcA, scA, t2A⟩, -⟩ := GlobalTheory.CompanionTheory.AdeleTop.adele_top F
  obtain ⟨trK, lcK, scK, t2K, cSig, -, -, bor, -, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hCM (AF F)
  haveI : BorelSpace (AF F) := ⟨rfl⟩
  haveI : BorelSpace (Fin 1 → Fin M → AF F ⊗[F] E) := bor 1 M
  have h2 : Module.finrank F E = 2 := hCM.2.2.1
  haveI : FiniteDimensional F E := Module.finite_of_finrank_pos (by omega)
  have cN : Continuous (Algebra.norm (AF F) : AF F ⊗[F] E → AF F) := continuous_norm_tensor (AF F)
  let a : (AF F ⊗[F] E)ˣ →
      ((Fin 1 → Fin M → AF F ⊗[F] E) × AF F) →+ ((Fin 1 → Fin M → AF F ⊗[F] E) × AF F) := fun t =>
    { toFun := fun p => (sigR (AF F) σ (t : AF F ⊗[F] E) • p.1,
        Algebra.norm (AF F) (t : AF F ⊗[F] E) * p.2)
      map_zero' := by simp
      map_add' := by intro p q; simp [smul_add, mul_add] }
  have ha : ∀ t p, a t p = (sigR (AF F) σ (t : AF F ⊗[F] E) • p.1,
      Algebra.norm (AF F) (t : AF F ⊗[F] E) * p.2) := fun _ _ => rfl
  haveI : LocallyCompactSpace (AF F ⊗[F] E)ˣ :=
    (Units.isClosedEmbedding_embedProduct (α := AF F ⊗[F] E)).locallyCompactSpace
  haveI : SecondCountableTopology (AF F ⊗[F] E)ᵐᵒᵖ :=
    (MulOpposite.opHomeomorph (M := AF F ⊗[F] E)).symm.secondCountableTopology
  haveI : SecondCountableTopology (AF F ⊗[F] E)ˣ :=
    (Units.isEmbedding_embedProduct (M := AF F ⊗[F] E)).secondCountableTopology
  have hcont : Continuous fun p : (AF F ⊗[F] E)ˣ × ((Fin 1 → Fin M → AF F ⊗[F] E) × AF F) =>
      a p.1 p.2 := by
    have hv : Continuous fun p : (AF F ⊗[F] E)ˣ × ((Fin 1 → Fin M → AF F ⊗[F] E) × AF F) =>
        ((p.1 : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) := Units.continuous_val.comp continuous_fst
    refine Continuous.prodMk ?_ ?_
    · exact (cSig.comp hv).smul (continuous_fst.comp continuous_snd)
    · exact (cN.comp hv).mul (continuous_snd.comp continuous_snd)
  haveI : μW.IsAddHaarMeasure := hW
  haveI : μA.IsAddHaarMeasure := hA
  haveI : IsTopologicalAddGroup (Fin 1 → Fin M → AF F ⊗[F] E) := inferInstance
  haveI : LocallyCompactSpace (Fin 1 → Fin M → AF F ⊗[F] E) := inferInstance
  haveI : SecondCountableTopology (Fin 1 → Fin M → AF F ⊗[F] E) := inferInstance
  haveI : SigmaFinite μW := inferInstance
  haveI : SigmaFinite μA := inferInstance
  haveI : (μW.prod μA).IsAddHaarMeasure := inferInstance
  obtain ⟨χ, hχc, hχ⟩ := GlobalTheory.T.group_action_haar_scaling_continuous ((Fin 1 → Fin M → AF F ⊗[F] E) × AF F) (μW.prod μA)
    (AF F ⊗[F] E)ˣ a hcont continuous_inv
    (by intro y; rw [ha]; simp)
    (by intro s t y; simp only [ha, Units.val_mul, map_mul, smul_smul, mul_assoc])
  refine ⟨χ, hχc, hχ, ?_⟩
  intro x
  have hτ' := hτ
  obtain ⟨-, θ, hθ, hval⟩ := hτ
  have hu := hval x
  have hsig : sigR (AF F) σ ((τ (Multiplicative.ofAdd x) : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) =
      ((τ (Multiplicative.ofAdd x) : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) := by
    rw [hu]; simp [sigR]
  haveI : Nontrivial (Ainf F) := by
    obtain ⟨v⟩ : Nonempty (InfinitePlace F) := inferInstance
    unfold Ainf InfiniteAdeleRing
    exact Pi.nontrivial_at v
  haveI : Nontrivial (AF F) := inferInstanceAs (Nontrivial (Ainf F × Af F))
  have hnorm : Algebra.norm (AF F) ((τ (Multiplicative.ofAdd x) : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) =
      pairA F (θ (Real.exp (2 * x))) 1 := by
    rw [hu, norm_tmul_one h2, sq]
    have e2 : Real.exp (2 * x) = Real.exp x * Real.exp x := by
      rw [← Real.exp_add]; congr 1; ring
    rw [e2, map_mul]
    change ((θ (Real.exp x) * θ (Real.exp x), (1 : Af F) * 1) : Ainf F × Af F) = (_, 1)
    rw [one_mul]
  have hWm := GlobalTheory.T.haar_scaling_under_flow F E σ hCM τ hτ' 1 M μW hW x
  have hAm := map_scale_adele hCM.1 θ hθ μA hA (Real.exp (2 * x)) (Real.exp_pos _)
  have mW : Measurable (fun X : Fin 1 → Fin M → AF F ⊗[F] E =>
      ((τ (Multiplicative.ofAdd x) : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) • X) :=
    (continuous_const_smul _).measurable
  have mA : Measurable (fun y : AF F => pairA F (θ (Real.exp (2 * x))) 1 * y) :=
    (continuous_const.mul continuous_id).measurable
  have hmap := Measure.map_prod_map μW μA mW mA
  rw [hWm, hAm, Measure.prod_smul_left, Measure.prod_smul_right, smul_smul] at hmap
  have hfun : (a (τ (Multiplicative.ofAdd x)) : _ → _) = Prod.map
      (fun X : Fin 1 → Fin M → AF F ⊗[F] E =>
        ((τ (Multiplicative.ofAdd x) : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) • X)
      (fun y : AF F => pairA F (θ (Real.exp (2 * x))) 1 * y) := by
    funext p
    rw [ha, hsig, hnorm]
    rfl
  have hfin := hχ (τ (Multiplicative.ofAdd x))
  rw [hfun, ← hmap] at hfin
  obtain ⟨S, hS, hS0⟩ := exists_compact_mem_nhds (0 : (Fin 1 → Fin M → AF F ⊗[F] E) × AF F)
  have pos : (μW.prod μA) S ≠ 0 := (Measure.measure_pos_of_mem_nhds _ hS0).ne'
  have fin : (μW.prod μA) S ≠ ⊤ := hS.measure_lt_top.ne
  have hS1 := congrArg (fun m : Measure _ => m S) hfin
  simp only [Measure.smul_apply, smul_eq_mul, ENNReal.smul_def] at hS1
  have hS2 := (ENNReal.mul_left_inj pos fin).1 hS1
  have hS3 := congrArg ENNReal.toReal hS2
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.exp_pos _).le,
    ENNReal.toReal_ofReal (by positivity), ENNReal.coe_toReal] at hS3
  rw [← hS3, ← Real.exp_nat_mul, ← Real.exp_neg, ← Real.exp_add]
  congr 1
  push_cast
  ring

end GlobalTheory.CompanionTheory.SW.FChi
