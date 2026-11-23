import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.PhiCharacterResidues.ContinuousResLe

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp

open scoped Pointwise in
private theorem val_lt {F Ω : Type} [Field F] [Field Ω] [Algebra F Ω] (A : ValuationSubring Ω) (t : G F Ω) (y : Ω) :
    (t⁻¹ • A).valuation y < 1 ↔ A.valuation (t y) < 1 := by
  rw [valuation_lt_one_iff', valuation_lt_one_iff', ValuationSubring.mem_inv_pointwise_smul_iff,
    ValuationSubring.mem_inv_pointwise_smul_iff]
  simp only [AlgEquiv.smul_def, map_inv₀, map_eq_zero]

open scoped Pointwise in
private theorem conj_place {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] {A : ValuationSubring Ω}
    {v : HeightOneSpectrum (𝓞 F)} (h : IsPlaceOver A v) (t : G F Ω) :
    IsPlaceOver (t⁻¹ • A) v ∧ ∀ σ ∈ Ine (F := F) A, t⁻¹ * σ * t ∈ Ine (F := F) (t⁻¹ • A) := by
  refine ⟨fun x => ?_, fun σ hσ => ?_⟩
  · rw [val_lt, AlgEquiv.commutes]
    exact h x
  · obtain ⟨hd, hi⟩ := hσ
    refine ⟨?_, fun x hx => ?_⟩
    · rw [ValuationSubring.decompositionSubgroup, MulAction.mem_stabilizer_iff] at hd ⊢
      rw [mul_smul, mul_smul, smul_inv_smul, hd]
    · rw [ValuationSubring.valuation_le_one_iff, ValuationSubring.mem_inv_pointwise_smul_iff,
        AlgEquiv.smul_def] at hx
      rw [val_lt, map_sub]
      have := hi (t x) ((ValuationSubring.valuation_le_one_iff A _).2 hx)
      simpa [AlgEquiv.mul_apply, mul_inv_apply] using this

theorem UpperTheory.V.Ws.phiKer :
    ∀ {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] {s : W.HidaSetting l L Ω} (V : s.Lev), Function.Surjective V.pr ∧ Topology.IsQuotientMap V.pr ∧ ∀ U : Subgroup (G L Ω), IsClosed (U : Set (G L Ω)) → (∀ (A : ValuationSubring Ω) (v : W.Plc (W.Lp L)), IsPlaceOver A v → v ∉ V.S' → Ine (F := L) A ≤ U) → V.pr.ker ≤ U := by
  intro l _ L Ω _ _ _ _ _ _ s V
  have hres : ∀ (g : G L Ω) (x : Ω), W.resP L Ω g x = g x := fun _ _ => rfl
  have hinj : Function.Injective (W.resP L Ω) := fun a b h =>
    AlgEquiv.ext fun x => by rw [← hres a x, ← hres b x, h]
  have hsurj : Function.Surjective V.pr := by
    rintro ⟨y, hy⟩
    obtain ⟨g', rfl⟩ := QuotientGroup.mk'_surjective (NS Ω V.S') y
    obtain ⟨g, rfl⟩ := (V.hη g').1 hy
    exact ⟨g, rfl⟩
  have hcont : Continuous V.pr := V.pr_cont W.continuous_resP
  haveI : IsClosed ((NS Ω V.S' : Subgroup (G (W.Lp L) Ω)) : Set (G (W.Lp L) Ω)) := isClosed_NS Ω V.S'
  haveI : T2Space (GS Ω V.S') := by
    unfold GS
    infer_instance
  refine ⟨hsurj, (hcont.isClosedMap).isQuotientMap hcont hsurj, fun U hU hI g hg => ?_⟩
  open scoped Pointwise in
  have hsm : ∀ (g : G L Ω) (B : ValuationSubring Ω), W.resP L Ω g • B = g • B := by
    intro g B
    ext x
    rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem,
      ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, ← map_inv, AlgEquiv.smul_def,
      AlgEquiv.smul_def, hres]
  have hM : IsClosed ((U.map (W.resP L Ω) : Subgroup (G (W.Lp L) Ω)) : Set (G (W.Lp L) Ω)) := by
    rw [Subgroup.coe_map]
    exact ((hU.isCompact).image W.continuous_resP).isClosed
  have hle : NS Ω V.S' ≤ U.map (W.resP L Ω) := by
    unfold NS
    refine Subgroup.topologicalClosure_minimal _ ?_ hM
    rw [Subgroup.normalClosure, Subgroup.closure_le]
    intro c hc
    rw [Group.mem_conjugatesOfSet_iff] at hc
    obtain ⟨a, ha, hac⟩ := hc
    obtain ⟨d, rfl⟩ := isConj_iff.1 hac
    simp only [Set.mem_iUnion, Set.mem_compl_iff, Set.mem_setOf_eq, exists_prop] at ha
    obtain ⟨v, hv, A, hA, haA⟩ := ha
    have key := conj_place hA d⁻¹
    simp only [inv_inv] at key
    obtain ⟨hA', hconj⟩ := key
    have hb := hconj a haA
    obtain ⟨g0, hg0⟩ := s.unr _ v hA' hb
    refine ⟨g0, hI _ v hA' hv ?_, hg0⟩
    rw [← hg0] at hb
    obtain ⟨hd, hi⟩ := hb
    refine ⟨?_, fun x hx => ?_⟩
    · open scoped Pointwise in
      rw [ValuationSubring.decompositionSubgroup, MulAction.mem_stabilizer_iff] at hd ⊢
      open scoped Pointwise in
      rwa [← hsm]
    · have := hi x hx
      rwa [hres] at this
  have hgN : W.resP L Ω g ∈ NS Ω V.S' := by
    rw [MonoidHom.mem_ker, Subtype.ext_iff] at hg
    exact (QuotientGroup.eq_one_iff _).1 hg
  obtain ⟨u, hu, hug⟩ := hle hgN
  rw [← hinj hug]
  exact hu
