import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspDiscreteDecompositionGL
import Development.AbelianVarietyTheory.Definitions.Foundations.MemL2AutomorphicCharacter

noncomputable section

open NumberField MeasureTheory Matrix Formalism.L2.Host
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult GlobalTheory.DiscreteSum GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.IdeleCovolume
open scoped InnerProductSpace

namespace GlobalTheory.CuspRep.CuspidalL2GL.SpecModel

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E]

theorem exists_scalar {G K : Type} [Group G] [TopologicalSpace G] [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    [CompleteSpace K] {ρ : G →* (K →L[ℂ] K)} (hu : GlobalTheory.OpTrace.IsUnitaryRep ρ) (hc : ∀ g h : G, g * h = h * g)
    {H : Submodule ℂ K} (hi : IsIrredSubrep ρ H) (g : G) : ∃ c : ℂ, ∀ F ∈ H, ρ g F = c • F := by
  have hπ := isIrrUnitary_rep hu hi
  have := hπ.complete
  have h1 : ContinuousLinearMap.id ℂ H ∈ homIn hi.1.rep hi.1.rep ⊤ := mem_homIn_top.2 fun _ _ => rfl
  have hT : hi.1.rep g ∈ homIn hi.1.rep hi.1.rep ⊤ := mem_homIn_top.2 fun k x =>
    DFunLike.congr_fun ((map_mul hi.1.rep g k).symm.trans ((congrArg _ (hc g k)).trans (map_mul hi.1.rep k g))) x
  refine ⟨be (hi.1.rep g) (.id ℂ H), fun F hF => congrArg Subtype.val
    (show hi.1.rep g ⟨F, hF⟩ = be (hi.1.rep g) (.id ℂ H) • ⟨F, hF⟩ from ext_inner_left ℂ fun y => ?_)⟩
  exact (inner_eq_be hπ hπ.unitary hT h1 _ y).trans (inner_smul_right _ _ _).symm

theorem finiteVectors_one (μ : Measure (GA E 1)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant]
    (H : Submodule ℂ (L2 (latticeGL E 1) μ)) (hH : H ≤ L2cusp μ) (hi : IsIrredSubrep (R (latticeGL E 1) μ) H) :
    ∃ ν : HChar E, IsFinitePartOf μ ((CuspSub.triv E le_rfl).twist ν) H := by
  have hu := isUnitaryRep_R (latticeGL E 1) μ
  choose c hc using exists_scalar hu mul_comm_one hi
  obtain ⟨F, hF, h0⟩ := (Submodule.ne_bot_iff _).1 hi.2.1
  have h1 : ∀ g, R (latticeGL E 1) μ g F = F → c g = 1 := fun g e =>
    smul_left_injective ℂ h0 (by beta_reduce; rw [← hc g F hF, e, one_smul])
  let ω : GA E 1 →* ℂ :=
    { toFun := c
      map_one' := h1 1 (by rw [map_one]; rfl)
      map_mul' := fun g h => smul_left_injective ℂ h0 (by
        beta_reduce
        rw [← hc _ F hF, map_mul, mul_apply_eq_comp, hc h F hF, map_smul, hc g F hF, smul_smul, mul_comm]) }
  have hn : ∀ g, ‖c g‖ = 1 := fun g => by
    have := norm_R g F
    rw [hc g F hF, norm_smul] at this
    exact (mul_eq_right₀ (norm_ne_zero_iff.2 h0)).1 this
  have hcont : Continuous c := by
    have : c = fun g => ⟪F, R (latticeGL E 1) μ g F⟫_ℂ / ⟪F, F⟫_ℂ := funext fun g => by
      rw [hc g F hF, inner_smul_right, mul_div_assoc, div_self (inner_self_ne_zero.2 h0), mul_one]
    rw [this]
    exact (continuous_const.inner (continuous_R F)).div_const _
  let χ : GA E 1 →* Circle :=
    { toFun := fun g => ⟨c g, mem_sphere_zero_iff_norm.2 (hn g)⟩
      map_one' := Subtype.ext ω.map_one
      map_mul' := fun g h => Subtype.ext (ω.map_mul g h) }
  have hχ : Continuous χ := hcont.subtype_mk _
  have key : ∀ F' ∈ H, ∃ z : ℂ, lift (latticeGL E 1) F' =ᵐ[μ] fun x => z * c x := fun F' hF' =>
    GlobalTheory.AutMult.Model.exists_ae_eq_char hχ fun g => hc g F' hF'
  have hΓ : ∀ γ ∈ latticeGL E 1, c γ = 1 := fun γ hγ => h1 γ (l2DiscreteQuotient_ext_iff_lift_ae_eq.2 ((lift_R γ F).trans (.of_forall fun x => by
    beta_reduce; rw [mul_comm_one]; exact leftInv_lift F γ hγ x)))
  let ν : HChar E := ⟨(ω.comp (toGL E)).toHomUnits,
    Units.isEmbedding_val₀.continuous_iff.2 (hcont.comp (continuous_toGL E)), fun γ => Units.ext
      (hΓ _ ((mem_latticeGL E _).2 ⟨γ, 0, by rw [det_toGL, zpow_zero, mul_one]; rfl⟩))⟩
  have hν : ∀ g, ((chiDet 1 ν g : ℂˣ) : ℂ) = c g := fun g => congrArg c (toGL_det E g)
  have hV : ∀ φ ∈ ((CuspSub.triv E le_rfl).twist ν).V, ∃ z : ℂ, φ.1 = fun x => z * c x := by
    rintro _ ⟨φ, hφ, rfl⟩
    obtain ⟨z, rfl⟩ := Submodule.mem_span_singleton.1 hφ
    exact ⟨z, funext fun x => (mulChi_apply ν _ x).trans (by rw [hν]; exact congrArg (· * _) (mul_one z))⟩
  have hV' : ∀ z : ℂ, ∃ φ ∈ ((CuspSub.triv E le_rfl).twist ν).V, φ.1 = fun x => z * c x := fun z =>
    ⟨_, ⟨z • oneFn E 1, Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _), rfl⟩,
      funext fun x => (mulChi_apply ν _ x).trans (by rw [hν]; exact congrArg (· * _) (mul_one z))⟩
  have e : classes ((CuspSub.triv E le_rfl).twist ν).V μ = H := by
    refine le_antisymm ?_ fun F' hF' => ?_
    · rintro F' ⟨φ, hφ, e⟩
      obtain ⟨z, hz⟩ := hV φ hφ
      obtain ⟨z₀, hz₀⟩ := key F hF
      have hz0 : z₀ ≠ 0 := by
        rintro rfl
        exact h0 (l2DiscreteQuotient_ext_iff_lift_ae_eq.2 (hz₀.trans (Filter.EventuallyEq.trans (.of_forall fun x => zero_mul _)
          (show lift (latticeGL E 1) (0 : L2 (latticeGL E 1) μ) =ᵐ[μ] 0 from
            ae_quotMeasure_iff.1 (Lp.coeFn_zero ℂ 2 _)).symm)))
      have : F' = (z / z₀) • F := l2DiscreteQuotient_ext_iff_lift_ae_eq.2 (e.trans (Filter.EventuallyEq.trans (.of_forall fun x => by
        rw [hz]; simp only [Pi.smul_apply, smul_eq_mul]; field_simp) (GlobalTheory.AutMult.Model.lift_smul _ hz₀).symm))
      exact this ▸ H.smul_mem _ hF
    · obtain ⟨z, hz⟩ := key F' hF'
      obtain ⟨φ, hφ, e⟩ := hV' z
      exact ⟨φ, hφ, e ▸ hz⟩
  refine ⟨ν, fun φ hφ t g => ?_, fun φ hφ => ?_, by rw [e, hi.1.1.submodule_topologicalClosure_eq],
    fun F' hF' _ => e ▸ hF'⟩
  · obtain ⟨z, hz⟩ := hV φ hφ
    rw [hz]
    change z * ω _ = z * ω _
    rw [map_mul, show ω (splitCentre E 1 t) = 1 from h1 _ (R_splitCentre t (hH hF)), one_mul]
  · obtain ⟨z, hz⟩ := hV φ hφ
    rw [hz]
    refine memL2_of_rank_one (continuous_const.mul hcont) fun γ hγ g => ?_
    change z * ω _ = z * ω _
    rw [map_mul, show ω γ = 1 from hΓ γ hγ, one_mul]

theorem finiteDimensional_zero (μ : Measure (GA E 0)) [μ.IsHaarMeasure] :
    FiniteDimensional ℂ (L2 (latticeGL E 0) μ) := by
  have : Subsingleton (Quot (latticeGL E 0)) := ⟨fun p q => Quotient.inductionOn₂ p q fun x y => by
    rw [Subsingleton.elim x y]⟩
  refine FiniteDimensional.of_injective (V₂ := ℂ) (K := ℂ)
    { toFun := fun F : L2 (latticeGL E 0) μ => lift (latticeGL E 0) F 1
      map_add' := fun F F' => ?_
      map_smul' := fun c F => ?_ } fun F F' e => l2DiscreteQuotient_ext_iff_lift_ae_eq.2 (.of_forall fun x => by rw [Subsingleton.elim x 1]; exact e)
  · obtain ⟨x, hx⟩ := (ae_quotMeasure_iff.1 (Lp.coeFn_add F F')).exists
    rw [Subsingleton.elim x 1] at hx
    exact hx
  · obtain ⟨x, hx⟩ := (ae_quotMeasure_iff.1 (Lp.coeFn_smul c F)).exists
    rw [Subsingleton.elim x 1] at hx
    exact hx

theorem discrete_zero (μ : Measure (GA E 0)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] : IsDiscreteSum (Rcusp μ) := by
  have := finiteDimensional_zero μ
  exact EnoughCompact.isDiscreteSum (isUnitaryRep_Rcusp μ) fun v hv =>
    ⟨ContinuousLinearMap.id ℂ _, isCompactOperator_of_locallyCompactSpace_rng _, fun _ _ _ => rfl, hv⟩

theorem finiteVectors_zero (μ : Measure (GA E 0)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant]
    (H : Submodule ℂ (L2 (latticeGL E 0) μ)) (hi : IsIrredSubrep (R (latticeGL E 0) μ) H) :
    IsFinitePartOf μ (CuspSub.triv E zero_le_one) H := by
  have hcl : ∀ F, F ∈ classes (CuspSub.triv E (a := 0) zero_le_one).V μ := fun F =>
    ⟨lift (latticeGL E 0) F 1 • oneFn E 0, Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _),
      .of_forall fun x => by rw [Subsingleton.elim x 1]; exact (mul_one _).symm⟩
  obtain ⟨F, hF, h0⟩ := (Submodule.ne_bot_iff _).1 hi.2.1
  have hz : lift (latticeGL E 0) F 1 ≠ 0 := fun e => h0 (l2DiscreteQuotient_ext_iff_lift_ae_eq.2 (Filter.EventuallyEq.trans
    (.of_forall fun x => by rw [Subsingleton.elim x 1]; exact e)
    (show lift (latticeGL E 0) (0 : L2 (latticeGL E 0) μ) =ᵐ[μ] 0 from ae_quotMeasure_iff.1 (Lp.coeFn_zero ℂ 2 _)).symm))
  have hH : ∀ F', F' ∈ H := fun F' => by
    have : F' = (lift (latticeGL E 0) F' 1 / lift (latticeGL E 0) F 1) • F := l2DiscreteQuotient_ext_iff_lift_ae_eq.2 (Filter.EventuallyEq.trans
      (.of_forall fun x => by
        rw [Subsingleton.elim x 1]; simp only [Pi.smul_apply, smul_eq_mul]; field_simp)
      (GlobalTheory.AutMult.Model.lift_smul _ .rfl).symm)
    exact this ▸ H.smul_mem _ hF
  refine ⟨isNormalised_triv _, fun φ hφ => ?_, le_antisymm (fun F' _ => hH F')
    fun F' _ => Submodule.le_topologicalClosure _ (hcl F'), fun F' _ _ => hcl F'⟩
  have hd := isFundamentalDomain_stdDom (latticeGL E 0) μ
  refine (memL2_iff_fundamental_domain hd).2 ⟨fun _ _ _ => congrArg _ (Subsingleton.elim _ _), MemLp.restrict _ ?_⟩
  exact (continuous_of_discreteTopology).memLp_of_hasCompactSupport (.of_compactSpace _)

theorem bounded_zero (φ : Sm E 0) : ∃ C : ℝ, ∀ g, ‖φ.1 g‖ ≤ C := ⟨_, fun g => by rw [Subsingleton.elim g 1]⟩

theorem exists_unbounded : ∃ φ : Sm E 1, IsCuspForm φ ∧ ¬ ∃ C : ℝ, ∀ g, ‖φ.1 g‖ ≤ C := by
  by_contra! h
  obtain ⟨σ, hσ⟩ := exists_not_isUnitary (E := E)
  induction σ using Quotient.inductionOn with | _ π => ?_
  refine hσ ((CG.isUnitary_mk π).2 ?_)
  obtain ⟨ω, hω⟩ := Central.exists_hasCentral E 1 π
  obtain ⟨φ, hφ, h0⟩ := (Submodule.ne_bot_iff _).1 π.ne_bot
  obtain ⟨C, hC⟩ := h φ (π.cusp φ hφ)
  obtain ⟨g, hg⟩ : ∃ g, φ.1 g ≠ 0 := Function.ne_iff.1 fun e => h0 (Subtype.ext e)
  have hle : ∀ x, ‖((ω.1 x : ℂˣ) : ℂ)‖ ≤ 1 := fun x => by
    by_contra hc
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (C / ‖φ.1 g‖) (not_le.1 hc)
    have := hC (GeneralLinearGroup.scalar (Fin 1) (x ^ n) * g)
    rw [hω.apply hφ, norm_mul, map_pow, Units.val_pow_eq_pow_val, norm_pow] at this
    exact hn.not_ge ((le_div_iff₀ (norm_pos_iff.2 hg)).2 this)
  refine ⟨ω, fun x => le_antisymm (hle x) ?_, hω⟩
  have := hle x⁻¹
  rw [map_inv, Units.val_inv_eq_inv_val, norm_inv] at this
  exact (inv_le_one₀ (norm_pos_iff.2 (Units.ne_zero _))).1 this

theorem not_isFinitePartOf_bot {a : ℕ} (μ : Measure (GA E a)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant]
    (π : CuspSub E a) : ¬ IsFinitePartOf μ π ⊥ := fun h => by
  obtain ⟨φ, hφ, h0⟩ := (Submodule.ne_bot_iff _).1 π.ne_bot
  exact toL2_ne_zero (h.finitePartMemL2 φ hφ) (ContAut.continuous_of_isOpen_stab E a φ (π.cusp φ hφ).1.level)
    (fun e => h0 (Subtype.ext e)) (h.classes_le (toL2_mem_classes hφ (h.finitePartMemL2 φ hφ)))

theorem clauses_of_le_one {a : ℕ} (ha : a ≤ 1) :
    (∀ (μ : Measure (GA E a)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (H : Submodule ℂ (L2 (latticeGL E a) μ)),
      H ≤ L2cusp μ → IsIrredSubrep (R (latticeGL E a) μ) H → ∃ π : CuspSub E a, IsFinitePartOf μ π H) ∧
    ∀ φ : Sm E a, IsCuspForm φ → (∀ t g, ‖φ.1 (splitCentre E a t * g)‖ = ‖φ.1 g‖) → ∃ C : ℝ, ∀ g, ‖φ.1 g‖ ≤ C := by
  obtain rfl | rfl : a = 0 ∨ a = 1 := by omega
  · exact ⟨fun μ _ _ H _ hi => ⟨_, finiteVectors_zero μ H hi⟩, fun φ _ _ => bounded_zero φ⟩
  · exact ⟨fun μ _ _ H hH hi => (finiteVectors_one μ H hH hi).elim fun _ h => ⟨_, h⟩, fun _ => bounded_one⟩

end GlobalTheory.CuspRep.CuspidalL2GL.SpecModel

end
