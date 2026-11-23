import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.Foundations.RowRawRange

open ValuativeRel MeasureTheory Formalism.MainNotions.S.Loc

namespace GlobalTheory.SgLoc.Top

section Field
variable (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

theorem localField_secondCountable : SecondCountableTopology F := by
  have hZ : Countable (WithZero (Multiplicative ℤ)) := by
    have : Countable (Multiplicative ℤ) := inferInstanceAs (Countable ℤ)
    exact inferInstanceAs (Countable (Option (Multiplicative ℤ)))
  have hcount : Countable (ValueGroupWithZero F) :=
    (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt F).injective.countable
  have : Countable (ValueGroupWithZero F)ˣ := Units.val_injective.countable
  have hsig : SigmaCompactSpace F := by
    refine SigmaCompactSpace.of_countable (Set.range fun γ : ValueGroupWithZero F => {x : F | valuation F x ≤ γ})
      (Set.countable_range _) ?_ ?_
    · rintro _ ⟨γ, rfl⟩
      exact IsNonarchimedeanLocalField.isCompact_closedBall F γ
    · refine Set.eq_univ_of_forall fun x => ?_
      exact Set.mem_sUnion.mpr ⟨_, ⟨valuation F x, rfl⟩, show valuation F x ≤ valuation F x from le_rfl⟩
  let := IsTopologicalAddGroup.rightUniformSpace F
  have := isUniformAddGroup_of_addCommGroup (G := F)
  have : (nhds (0 : F)).IsCountablyGenerated :=
    (IsValuativeTopology.hasBasis_nhds_zero F).isCountablyGenerated
  have := IsUniformAddGroup.uniformity_countably_generated (α := F)
  infer_instance

theorem t2Space_of_isNonarchimedeanLocalField_flag_measures : T2Space F := by
  refine IsTopologicalAddGroup.t2Space_of_zero_sep fun x hx => ?_
  refine ⟨{y | valuation F y < valuation F x},
    (IsValuativeTopology.hasBasis_nhds_zero' F).mem_of_mem (by simpa using hx), ?_⟩
  exact lt_irrefl (valuation F x)

theorem localField_isOpen_integer : IsOpen (𝒪[F] : Set F) := (valuation F).isOpen_integer

theorem localField_isCompact_integer : IsCompact (𝒪[F] : Set F) := IsNonarchimedeanLocalField.isCompact_closedBall F 1

variable {F}

theorem isOpen_mul_integer {c : F} (hc : c ≠ 0) : IsOpen ((fun x => c * x) '' (𝒪[F] : Set F)) := (Homeomorph.mulLeft₀ c hc).isOpenMap _ (localField_isOpen_integer F)

theorem isCompact_mul_integer (c : F) : IsCompact ((fun x => c * x) '' (𝒪[F] : Set F)) := (localField_isCompact_integer F).image (continuous_const.mul continuous_id)

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem mem_integer_of_isIntegral {a : F} (h : IsIntegral 𝒪[F] a) : a ∈ 𝒪[F] := (Valuation.integer.integers (valuation F)).mem_of_integral h

end Field

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]

theorem locE_nontrivial (L : LocE F E) : Nontrivial E := by
  have := L.free
  exact Module.nontrivial_of_finrank_pos (R := F) (by rw [L.rank]; norm_num)

theorem locE_exists_pure [CharZero F] (L : LocE F E) :
    ∃ (d : E) (D : F), D ≠ 0 ∧ D ∈ 𝒪[F] ∧ L.cj d = -d ∧ d * d = algebraMap F E D := by
  have := L.free
  have := L.reduced
  have hnt := locE_nontrivial L
  obtain ⟨x, hx⟩ : ∃ x : E, ∀ a : F, algebraMap F E a ≠ x := by
    by_contra! h
    have e := LinearEquiv.ofBijective (Algebra.linearMap F E) ⟨(algebraMap F E).injective, fun y => h y⟩
    have := e.finrank_eq
    rw [Module.finrank_self, L.rank] at this
    norm_num at this
  set d0 := x - L.cj x with hd0def
  have hcj0 : L.cj d0 = -d0 := by
    rw [hd0def, map_sub, L.cj_cj]; ring
  have hd0 : d0 ≠ 0 := by
    intro h0
    obtain ⟨a, ha⟩ := (L.cj_fix x).mp (by rw [hd0def, sub_eq_zero] at h0; exact h0.symm)
    exact hx a ha
  obtain ⟨D0, hD0⟩ := (L.cj_fix (d0 * d0)).mp (by rw [map_mul, hcj0, neg_mul_neg])
  have hD0ne : D0 ≠ 0 := by
    rintro rfl
    rw [map_zero] at hD0
    exact hd0 (IsReduced.eq_zero d0 ⟨2, by rw [pow_two, ← hD0]⟩)
  by_cases hD : D0 ∈ 𝒪[F]
  · exact ⟨d0, D0, hD0ne, hD, hcj0, hD0.symm⟩
  · refine ⟨algebraMap F E D0⁻¹ * d0, D0⁻¹, inv_ne_zero hD0ne, ?_, ?_, ?_⟩
    · rw [Valuation.mem_integer_iff] at hD ⊢
      rw [map_inv₀]
      exact inv_le_one_of_one_le₀ (le_of_lt (not_le.mp hD))
    · rw [map_mul, AlgEquiv.commutes, hcj0, mul_neg]
    · rw [show (algebraMap F E D0⁻¹ * d0) * (algebraMap F E D0⁻¹ * d0) =
          algebraMap F E (D0⁻¹ * D0⁻¹ * D0) by rw [map_mul, map_mul, hD0]; ring]
      congr 1
      field_simp

theorem locE_exists_coords [CharZero F] (L : LocE F E) :
    ∃ (ψ : (F × F) ≃ₗ[F] E) (D : F), D ≠ 0 ∧
      (∀ p : F × F, p.1 ∈ 𝒪[F] → p.2 ∈ 𝒪[F] → ψ p ∈ L.O) ∧
      (∀ p : F × F, ψ p ∈ L.O → 2 * p.1 ∈ 𝒪[F] ∧ 2 * D * p.2 ∈ 𝒪[F]) := by
  obtain ⟨d, D, hD0, hDO, hcj, hdd⟩ := locE_exists_pure L
  have := L.free
  have hnt := locE_nontrivial L
  have hfin : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [L.rank]; norm_num)
  let φ : (F × F) →ₗ[F] E := (LinearMap.fst F F F).smulRight (1 : E) + (LinearMap.snd F F F).smulRight d
  have hφ : ∀ p : F × F, φ p = algebraMap F E p.1 + algebraMap F E p.2 * d := by
    intro p
    simp [φ, Algebra.smul_def]
  have hinjA := (algebraMap F E).injective
  have hinj : Function.Injective φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro p hp
    rw [hφ] at hp
    have hc : algebraMap F E p.1 - algebraMap F E p.2 * d = 0 := by
      have h' := congrArg L.cj hp
      rw [map_add, map_mul, AlgEquiv.commutes, AlgEquiv.commutes, hcj, map_zero] at h'
      rw [← h']; ring
    have hb : algebraMap F E (2 * p.2 * D) = 0 := by
      rw [map_mul, map_mul, ← hdd, map_ofNat]
      linear_combination d * hp - d * hc
    have hb' : p.2 = 0 := by
      have h2 := (map_eq_zero_iff _ hinjA).mp hb
      simpa [hD0] using h2
    have ha : p.1 = 0 := by
      rw [hb', map_zero, zero_mul, add_zero] at hp
      exact (map_eq_zero_iff _ hinjA).mp hp
    exact Prod.ext ha hb'
  have hdim : Module.finrank F (F × F) = Module.finrank F E := by
    rw [Module.finrank_prod, Module.finrank_self, L.rank]
  have hA : ∀ a ∈ 𝒪[F], IsIntegral 𝒪[F] (algebraMap F E a) := by
    intro a ha
    rw [isIntegral_algebraMap_iff hinjA]
    exact (show IsIntegral 𝒪[F] (algebraMap 𝒪[F] F ⟨a, ha⟩) from isIntegral_algebraMap)
  have hdI : IsIntegral 𝒪[F] d := by
    refine ⟨Polynomial.X ^ 2 - Polynomial.C ⟨D, hDO⟩, Polynomial.monic_X_pow_sub_C _ two_ne_zero, ?_⟩
    rw [Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_C,
      IsScalarTower.algebraMap_apply 𝒪[F] F E, pow_two, hdd]
    exact sub_self _
  refine ⟨LinearMap.linearEquivOfInjective φ hinj hdim, D, hD0, ?_, ?_⟩
  · intro p h1 h2
    rw [LinearMap.linearEquivOfInjective_apply, hφ, L.O_def]
    exact (hA _ h1).add ((hA _ h2).mul hdI)
  · intro p hp
    rw [LinearMap.linearEquivOfInjective_apply, hφ, L.O_def] at hp
    have hq := hp.map (L.cj.toAlgHom.restrictScalars 𝒪[F])
    have hcx : (L.cj.toAlgHom.restrictScalars 𝒪[F]) (algebraMap F E p.1 + algebraMap F E p.2 * d) =
        algebraMap F E p.1 - algebraMap F E p.2 * d := by
      change L.cj _ = _
      rw [map_add, map_mul, AlgEquiv.commutes, AlgEquiv.commutes, hcj]; ring
    rw [hcx] at hq
    constructor
    · have h' := hp.add hq
      rw [show algebraMap F E p.1 + algebraMap F E p.2 * d + (algebraMap F E p.1 - algebraMap F E p.2 * d) =
        algebraMap F E (2 * p.1) by rw [map_mul, map_ofNat]; ring, isIntegral_algebraMap_iff hinjA] at h'
      exact mem_integer_of_isIntegral h'
    · have h' := (hp.sub hq).mul hdI
      rw [show (algebraMap F E p.1 + algebraMap F E p.2 * d - (algebraMap F E p.1 - algebraMap F E p.2 * d)) * d =
        algebraMap F E (2 * D * p.2) by rw [map_mul, map_mul, map_ofNat, ← hdd]; ring, isIntegral_algebraMap_iff hinjA] at h'
      exact mem_integer_of_isIntegral h'

theorem locE_homeo [IsNonarchimedeanLocalField F] (L : LocE F E) (ψ : (F × F) ≃ₗ[F] E) :
    ∃ h : (F × F) ≃ₜ E, ∀ p, h p = ψ p := by
  have := L.top
  have := IsModuleTopology.toContinuousAdd F E
  exact ⟨{ toEquiv := ψ.toEquiv
           continuous_toFun := IsModuleTopology.continuous_of_linearMap ψ.toLinearMap
           continuous_invFun := IsModuleTopology.continuous_of_linearMap ψ.symm.toLinearMap }, fun _ => rfl⟩

theorem locE_topRing [IsNonarchimedeanLocalField F] (L : LocE F E) : IsTopologicalRing E := by
  have := L.top
  have := L.free
  have : Module.Finite F E := Module.finite_of_finrank_pos (by rw [L.rank]; norm_num)
  exact IsModuleTopology.isTopologicalRing F E

theorem locE_integers [IsNonarchimedeanLocalField F] [CharZero F] (L : LocE F E) :
    IsCompact (L.O : Set E) ∧ IsOpen (L.O : Set E) := by
  obtain ⟨ψ, D, hD0, h1, h2⟩ := locE_exists_coords L
  obtain ⟨h, hh⟩ := locE_homeo L ψ
  have := locE_topRing L
  have hAo : IsOpen (h '' ((𝒪[F] : Set F) ×ˢ (𝒪[F] : Set F))) :=
    h.isOpenMap _ ((localField_isOpen_integer F).prod (localField_isOpen_integer F))
  have hAO : h '' ((𝒪[F] : Set F) ×ˢ (𝒪[F] : Set F)) ⊆ (L.O : Set E) := by
    rintro _ ⟨p, ⟨hp1, hp2⟩, rfl⟩
    rw [hh]
    exact h1 p hp1 hp2
  have h0 : (0 : E) ∈ h '' ((𝒪[F] : Set F) ×ˢ (𝒪[F] : Set F)) :=
    ⟨0, ⟨zero_mem _, zero_mem _⟩, by rw [hh, map_zero]⟩
  have hOo : IsOpen (L.O : Set E) :=
    AddSubgroup.isOpen_of_mem_nhds L.O.toAddSubgroup (g := 0) (Filter.mem_of_superset (hAo.mem_nhds h0) hAO)
  have hOc : IsClosed (L.O : Set E) := AddSubgroup.isClosed_of_isOpen L.O.toAddSubgroup hOo
  have h2ne : (2 : F) ≠ 0 := two_ne_zero
  have hBc : IsCompact (h '' (((fun x => (2 : F)⁻¹ * x) '' (𝒪[F] : Set F)) ×ˢ
      ((fun x => (2 * D)⁻¹ * x) '' (𝒪[F] : Set F)))) :=
    ((isCompact_mul_integer _).prod (isCompact_mul_integer _)).image h.continuous
  have hOB : (L.O : Set E) ⊆ h '' (((fun x => (2 : F)⁻¹ * x) '' (𝒪[F] : Set F)) ×ˢ
      ((fun x => (2 * D)⁻¹ * x) '' (𝒪[F] : Set F))) := by
    intro x hx
    have hx' := h2 (ψ.symm x) (by rw [LinearEquiv.apply_symm_apply]; exact hx)
    refine ⟨ψ.symm x, ⟨⟨2 * (ψ.symm x).1, hx'.1, ?_⟩, ⟨2 * D * (ψ.symm x).2, hx'.2, ?_⟩⟩, ?_⟩
    · field_simp
    · field_simp
    · rw [hh, LinearEquiv.apply_symm_apply]
  exact ⟨hBc.of_isClosed_subset hOc hOB, hOo⟩

variable [MeasurableSpace E]

theorem mem_R_split (M : Model F E) (g : SplitG M.L) (hg : M.split = some g) (x : E) :
    x ∈ M.R ↔ ∃ a b : 𝒪[F], g.q ∣ a - b ∧ g.e x = ((a : F), (b : F)) := by
  simp only [Model.R, hg]
  rw [Subring.mem_comap, Subring.mem_map]
  constructor
  · rintro ⟨y, hy, hyx⟩
    refine ⟨y.1, y.2, ?_, ?_⟩
    · rw [← Ideal.mem_span_singleton, ← Ideal.Quotient.eq]
      exact hy
    · exact hyx.symm
  · rintro ⟨a, b, hab, hx⟩
    refine ⟨(a, b), ?_, ?_⟩
    · show Ideal.Quotient.mk _ a = Ideal.Quotient.mk _ b
      rw [Ideal.Quotient.eq, Ideal.mem_span_singleton]
      exact hab
    · exact hx.symm

theorem R_le_O (M : Model F E) : M.R ≤ M.L.O := by
  intro x hx
  cases hs : M.split with
  | none =>
    simp only [Model.R, hs] at hx
    exact hx
  | some g =>
    obtain ⟨a, b, -, hx'⟩ := (mem_R_split M g hs x).mp hx
    rw [M.L.O_def]
    have hab : IsIntegral 𝒪[F] ((a : F), (b : F)) := by
      refine ⟨(Polynomial.X - Polynomial.C a) * (Polynomial.X - Polynomial.C b),
        (Polynomial.monic_X_sub_C a).mul (Polynomial.monic_X_sub_C b), ?_⟩
      simp only [Polynomial.eval₂_mul, Polynomial.eval₂_sub, Polynomial.eval₂_X, Polynomial.eval₂_C,
        IsScalarTower.algebraMap_apply 𝒪[F] F (F × F), Prod.algebraMap_apply, Algebra.algebraMap_self,
        RingHom.id_apply]
      ext
      · simp
        left
        exact sub_self _
      · simp
        right
        exact sub_self _
    have hxe : x = g.e.symm ((a : F), (b : F)) := by rw [← hx', AlgEquiv.symm_apply_apply]
    rw [hxe]
    exact hab.map (g.e.symm.toAlgHom.restrictScalars 𝒪[F])

theorem isOpen_R [IsNonarchimedeanLocalField F] [CharZero F] (M : Model F E) :
    IsOpen (M.R : Set E) := by
  have := locE_topRing M.L
  cases hs : M.split with
  | none =>
    have hR : (M.R : Set E) = M.L.O := by simp only [Model.R, hs]
    rw [hR]
    exact (locE_integers M.L).2
  | some g =>
    have := M.L.top
    have := IsModuleTopology.toContinuousAdd F E
    have hec : Continuous (g.e : E → F × F) :=
      IsModuleTopology.continuous_of_linearMap g.e.toLinearEquiv.toLinearMap
    have hq : (g.q : F) ≠ 0 := fun h => g.q_irr.ne_zero (Subtype.ext h)
    have hU : IsOpen (((fun x => (g.q : F) * x) '' (𝒪[F] : Set F)) ×ˢ ((fun x => (g.q : F) * x) '' (𝒪[F] : Set F))) :=
      (isOpen_mul_integer hq).prod (isOpen_mul_integer hq)
    have hsub : (g.e : E → F × F) ⁻¹' (((fun x => (g.q : F) * x) '' (𝒪[F] : Set F)) ×ˢ
        ((fun x => (g.q : F) * x) '' (𝒪[F] : Set F))) ⊆ (M.R : Set E) := by
      rintro x ⟨⟨a, ha, h1⟩, ⟨b, hb, h2⟩⟩
      rw [SetLike.mem_coe, mem_R_split M g hs]
      refine ⟨⟨g.q * a, mul_mem g.q.2 ha⟩, ⟨g.q * b, mul_mem g.q.2 hb⟩, ⟨⟨a, ha⟩ - ⟨b, hb⟩, ?_⟩, ?_⟩
      · exact Subtype.ext (by simp [mul_sub])
      · exact Prod.ext h1.symm h2.symm
    have h0 : (0 : E) ∈ (g.e : E → F × F) ⁻¹' (((fun x => (g.q : F) * x) '' (𝒪[F] : Set F)) ×ˢ
        ((fun x => (g.q : F) * x) '' (𝒪[F] : Set F))) := by
      rw [Set.mem_preimage, map_zero]
      exact ⟨⟨0, zero_mem _, mul_zero _⟩, ⟨0, zero_mem _, mul_zero _⟩⟩
    exact AddSubgroup.isOpen_of_mem_nhds M.R.toAddSubgroup (g := 0)
      (Filter.mem_of_superset ((hU.preimage hec).mem_nhds h0) hsub)

theorem model_topology : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type}
    [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK →
    IsTopologicalRing E ∧ T2Space E ∧ LocallyCompactSpace E ∧ SecondCountableTopology E ∧
    ContinuousSMul F E ∧ IsCompact (M.R : Set E) ∧ IsOpen (M.R : Set E) ∧
    IsCompact (M.L.O : Set E) ∧ IsOpen (M.L.O : Set E) ∧ M.R ≤ M.L.O := by
  intro F _ _ _ E _ _ _ _ M hM
  have := hM.loc
  have := hM.char0
  obtain ⟨ψ, -, -, -, -⟩ := locE_exists_coords M.L
  obtain ⟨h, -⟩ := locE_homeo M.L ψ
  have hTR := locE_topRing M.L
  have := t2Space_of_isNonarchimedeanLocalField_flag_measures F
  have := localField_secondCountable F
  have := M.L.top
  have hRo := isOpen_R M
  have hO := locE_integers M.L
  have hRc : IsClosed (M.R : Set E) := AddSubgroup.isClosed_of_isOpen M.R.toAddSubgroup hRo
  exact ⟨hTR, h.symm.isEmbedding.t2Space, h.symm.isClosedEmbedding.locallyCompactSpace,
    h.symm.isEmbedding.secondCountableTopology, inferInstance,
    hO.1.of_isClosed_subset hRc (R_le_O M), hRo, hO.1, hO.2, R_le_O M⟩

end GlobalTheory.SgLoc.Top
