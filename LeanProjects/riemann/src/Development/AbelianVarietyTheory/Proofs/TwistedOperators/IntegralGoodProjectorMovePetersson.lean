import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ConjScalarAtOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReadingsExistRow
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.RealLowestKTypeCoeffSquareIntegrable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearSection
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormLiftFormsFiniteGroupAction
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdelicLiftDatumOfConjugateLiftDatumStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsMultIPOfModel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearLift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormOfClassSums
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FundamentalDomainSetIntegralMulRight
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LocallyCompactSecondCountableBorelCountable
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MultValueLeftContLevel
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HaarMapMulRightOfMemCompactSubgroup
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsCompactParahoricLevelAndContainsLifts
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormLevChiFlagLEqOne
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.EwfMove

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

theorem star_eC (hX : ∀ χ ∈ A.X, IsAbsIrrChar χ) (σ : D.what₂.LL →+* ℂ) (g : G) :
    starRingEnd ℂ (RealDat.eC (A := A) σ g) = RealDat.eC (A := A) σ g⁻¹ := by
  unfold RealDat.eC
  rw [coeff_idemOf, coeff_idemOf, map_sum, map_sum, map_sum]
  refine Finset.sum_congr rfl fun χ hχ => ?_
  have h1 := (hX χ hχ).map_inv σ 1
  have h2 := (hX χ hχ).map_inv σ g⁻¹
  rw [inv_one] at h1
  simp only [map_mul, map_div₀, map_natCast]
  rw [h2, ← h1]

theorem integral_levelGroupAction_pairing_invariant {V : HSp D} (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank)
    (g0 : G0 L.Pg L.r) (μ : Measure (GA D V)) [μ.IsHaarMeasure] (𝓕 : Set (GA D V))
    (h𝓕 : IsFundamentalDomain (GQ V) 𝓕 μ) (hk : ∃ κ, IsLevelLift V β L g0 κ) (F S : GA D V → ℂ)
    (hF : ∀ γ ∈ GQ V, ∀ g, F (γ * g) = F g) (hS : ∀ γ ∈ GQ V, ∀ g, S (γ * g) = S g)
    (hi : IntegrableOn (fun g => star (F g) * S g) 𝓕 μ) :
    IntegrableOn (fun g => star (actG0 V β L g0 F g) * actG0 V β L g0 S g) 𝓕 μ ∧
      ∫ g in 𝓕, star (actG0 V β L g0 F g) * actG0 V β L g0 S g ∂μ = ∫ g in 𝓕, star (F g) * S g ∂μ := by
  obtain ⟨h1, h2, h3, h4⟩ := GlobalTheory.TwistAdelicTop.locallyCompact_secondCountable_borel_countable V
  have : IsModuleTopology (AF D.host.F) (AF D.host.F ⊗[D.host.F] D.host.E) := ⟨rfl⟩
  have : Module.Finite D.host.F D.host.E := Module.Finite.of_restrictScalars_finite ℚ _ _
  have : IsTopologicalRing (AF D.host.F ⊗[D.host.F] D.host.E) :=
    IsModuleTopology.isTopologicalRing (AF D.host.F) _
  have : IsTopologicalGroup (GA D V) :=
    inferInstanceAs (IsTopologicalGroup (HR (AF D.host.F) D.sp.cm.sig V.gram))
  obtain ⟨hcpt, hlift⟩ := GlobalTheory.ParahoricCompact.isCompact_flag_and_lift V β L
  have hκ : hk.choose ∈ levG V β (flagL L) := hlift g0 _ hk.choose_spec
  have ha : ‖(levChi V β (flagL L) hk.choose)⁻¹‖ = 1 := by
    rw [norm_inv, GlobalTheory.norm_levChi_flagL_eq_one V β L _ hκ, inv_one]
  have hmap : Measure.map (fun g => g * hk.choose) μ = μ :=
    GlobalTheory.haar_map_mul_right_of_mem_compact_subgroup μ _ hcpt _ hκ
  set a := (levChi V β (flagL L) hk.choose)⁻¹ with ha_def
  have haa : star a * a = 1 := by
    have : star a * a = ((‖a‖ ^ 2 : ℝ) : ℂ) := by
      rw [Complex.star_def, Complex.conj_mul']; push_cast; rfl
    rw [this, ha]; norm_num
  have key : (fun g => star (actG0 V β L g0 F g) * actG0 V β L g0 S g) =
      fun g => star (F (g * hk.choose)) * S (g * hk.choose) := by
    funext g
    simp only [actG0, dif_pos hk]
    rw [star_mul', ← ha_def]
    linear_combination (star (F (g * hk.choose)) * S (g * hk.choose)) * haa
  rw [key]
  exact GlobalTheory.fundamentalDomain_setIntegral_mul_right (GQ V) μ 𝓕 h𝓕 _ hmap (fun g => star (F g) * S g)
    (fun γ hγ g => by simp only [hF γ hγ g, hS γ hγ g]) hi

end GlobalTheory.EwfMove

noncomputable section

namespace GlobalTheory.EwfMove

theorem integral_eWf_move : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → (∀ χ ∈ A.X, IsAbsIrrChar χ) → ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (v : ∀ ρ, lowT (R.MW i σ) ρ) (Φ : GA D (Wc D i) → ℂ), (∀ γ ∈ GQ (Wc D i), ∀ g, Φ (γ * g) = Φ g) → (∀ y : (R.HW i σ).H, IntegrableOn (fun g => star (Φ g) * (R.HW i σ).e y (fun ρ => v ρ) g) (R.fdW i) (R.νW i)) → ∀ y : (R.HW i σ).H, ∫ g in R.fdW i, star (R.eWf i σ Φ g) * (R.HW i σ).e y (fun ρ => v ρ) g ∂(R.νW i) = ∫ g in R.fdW i, star (Φ g) * (R.HW i σ).e (GlobalTheory.LiftLower.projH R i σ y) (fun ρ => v ρ) g ∂(R.νW i) := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hC hX i σ v Φ hΦ hi y
  obtain ⟨hinj, hrange, hip⟩ := hC.models.HW i σ
  obtain ⟨h1, h2⟩ := hC.models.νW i
  haveI := h1.1
  have hgW := hC.models.gW
  have hL : ∀ z : (R.HW i σ).H, ∀ γ ∈ GQ (Wc D i), ∀ g,
      (R.HW i σ).e z (fun ρ => v ρ) (γ * g) = (R.HW i σ).e z (fun ρ => v ρ) g := fun z =>
    (GlobalTheory.mult_value_left_cont_level R.θ (R.MW i σ) _ _ _
      ((hrange.le : _ ≤ R.Wall i σ) (LinearMap.mem_range_self _ z)) _).1
  have hS : ∀ (g : G) (z : (R.HW i σ).H), (R.HW i σ).e z (fun ρ => v ρ) =
      actG0 (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g) ((R.HW i σ).e (R.gW i σ g⁻¹ z) (fun ρ => v ρ)) := by
    intro g z
    have e := congrArg (fun T : MMap (R.MW i σ) => T (fun ρ => v ρ)) (hgW i σ g (R.gW i σ g⁻¹ z))
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply] at e
    exact e
  have hper : ∀ g : G,
      IntegrableOn (fun h => star (actG0 (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g) Φ h) *
        (R.HW i σ).e y (fun ρ => v ρ) h) (R.fdW i) (R.νW i) ∧
      ∫ h in R.fdW i, star (actG0 (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g) Φ h) *
        (R.HW i σ).e y (fun ρ => v ρ) h ∂(R.νW i) =
      ∫ h in R.fdW i, star (Φ h) * (R.HW i σ).e (R.gW i σ g⁻¹ y) (fun ρ => v ρ) h ∂(R.νW i) := by
    intro g
    by_cases hk : ∃ κ, IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g) κ
    · rw [hS g y]
      exact integral_levelGroupAction_pairing_invariant _ _ _ _ _ h2 hk Φ _ hΦ (hL _) (hi _)
    · have h0 : ∀ z : (R.HW i σ).H, (R.HW i σ).e z (fun ρ => v ρ) = 0 := fun z => by
        rw [hS g z]
        simp only [actG0, dif_neg hk]
      constructor
      · simp only [h0, Pi.zero_apply, mul_zero]
        exact integrableOn_zero
      · simp only [h0, Pi.zero_apply, mul_zero]
  have eL : ∀ h, star (R.eWf i σ Φ h) * (R.HW i σ).e y (fun ρ => v ρ) h =
      ∑ g, starRingEnd ℂ (RealDat.eC (A := A) σ g) *
        (star (actG0 (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g) Φ h) * (R.HW i σ).e y (fun ρ => v ρ) h) := by
    intro h
    simp only [RealDat.eWf, gaL, LinearMap.sum_apply, LinearMap.smul_apply, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul, star_sum, star_mul', Finset.sum_mul]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [mul_assoc]
    rfl
  have eR : ∀ h, star (Φ h) * (R.HW i σ).e (GlobalTheory.LiftLower.projH R i σ y) (fun ρ => v ρ) h =
      ∑ g, RealDat.eC (A := A) σ g * (star (Φ h) * (R.HW i σ).e (R.gW i σ g y) (fun ρ => v ρ) h) := by
    intro h
    simp only [GlobalTheory.LiftLower.projH, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul,
      MultilinearMap.sum_apply, MultilinearMap.smul_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun g _ => ?_
    ring
  simp only [eL, eR]
  rw [integral_finset_sum _ fun g _ => ((hper g).1.const_mul _),
    integral_finset_sum _ fun g _ => ((hi (R.gW i σ g y)).const_mul _)]
  simp only [integral_const_mul, (hper _).2, star_eC hX]
  exact Fintype.sum_equiv (Equiv.inv G) _ _ (fun g => rfl)

end GlobalTheory.EwfMove
