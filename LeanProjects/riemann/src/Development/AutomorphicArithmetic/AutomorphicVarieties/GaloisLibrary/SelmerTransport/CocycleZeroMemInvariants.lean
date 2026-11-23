import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.RestrictionMemInvariantH1

open ReciprocityTheory.Gal UpperTheory.V.Base

private theorem exists_inj_of_ker_eq {R A B C : Type} [CommRing R] [AddCommGroup A] [Module R A]
    [AddCommGroup B] [Module R B] [AddCommGroup C] [Module R C] (p : A →ₗ[R] B) (q : A →ₗ[R] C)
    (hp : Function.Surjective p) (hk : ∀ a, p a = 0 ↔ q a = 0) :
    ∃ φ : B →ₗ[R] C, Function.Injective φ := by
  have hle : LinearMap.ker p ≤ LinearMap.ker q := fun a ha => (hk a).1 ha
  have hle' : LinearMap.ker q ≤ LinearMap.ker p := fun a ha => (hk a).2 ha
  refine ⟨(LinearMap.ker p).liftQ q hle ∘ₗ (p.quotKerEquivOfSurjective hp).symm.toLinearMap, ?_⟩
  rw [LinearMap.coe_comp]
  exact (LinearMap.ker_eq_bot.mp (Submodule.ker_liftQ_eq_bot _ q hle hle')).comp
    (p.quotKerEquivOfSurjective hp).symm.injective

section

variable {R G M : Type} [CommRing R] [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup M]
  [Module R M] [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousConstSMul R M] [DiscreteTopology M]

private theorem cocycle_eq_zero (ρ : Representation R G M) {U' U : Subgroup G} (h : U' ≤ U) {γ : G} (hγ : γ ∈ U)
    (hU : U ≤ (Subgroup.zpowers γ ⊔ U').topologicalClosure) (z : Z1U ρ U)
    (h1 : ∀ u : U, u.1 ∈ U' → z.1 u = 0) (h2 : z.1 ⟨γ, hγ⟩ = 0) (u : U) : z.1 u = 0 := by
  obtain ⟨hcont, hcoc⟩ := (mem_Z1_iff_cocycle _ _).1 z.2
  have hone : z.1 1 = 0 := by
    have e := hcoc 1 1
    simp only [mul_one, map_one, Module.End.one_apply] at e
    simpa using e
  let K : Subgroup U :=
    { carrier := {x | z.1 x = 0}
      mul_mem' := fun {a b} ha hb => by
        show z.1 (a * b) = 0
        rw [hcoc, ha, hb, map_zero, add_zero]
      one_mem' := hone
      inv_mem' := fun {a} ha => by
        show z.1 a⁻¹ = 0
        have e := hcoc a⁻¹ a
        rw [inv_mul_cancel, hone, ha, map_zero, add_zero] at e
        exact e.symm }
  have hS : Subgroup.zpowers γ ⊔ U' ≤ K.map U.subtype := by
    refine sup_le ?_ ?_
    · rw [Subgroup.zpowers_le]
      exact ⟨⟨γ, hγ⟩, h2, rfl⟩
    · intro x hx
      exact ⟨⟨x, h hx⟩, h1 ⟨x, h hx⟩ hx, rfl⟩
  have hu := hU u.2
  rw [← SetLike.mem_coe, Subgroup.topologicalClosure_coe] at hu
  have hV : IsOpen (z.1 ⁻¹' {z.1 u}) := hcont.isOpen_preimage _ (isOpen_discrete _)
  obtain ⟨O, hO, hOV⟩ := isOpen_induced_iff.1 hV
  have huO : u.1 ∈ O := by
    have : u ∈ Subtype.val ⁻¹' O := by rw [hOV]; rfl
    exact this
  obtain ⟨s, hsO, hsS⟩ := mem_closure_iff.1 hu O hO huO
  obtain ⟨⟨s', hs'U⟩, hzs, rfl⟩ := hS hsS
  have hmem : (⟨s', hs'U⟩ : U) ∈ Subtype.val ⁻¹' O := hsO
  rw [hOV] at hmem
  have e : z.1 ⟨s', hs'U⟩ = z.1 u := hmem
  rw [← e]
  exact hzs

private noncomputable def cob (ρ : Representation R G M) (hρ : ContAction ρ) (U : Subgroup G) (m : M) : Z1U ρ U :=
  ⟨d0 (ρ.comp U.subtype : Representation R U M) m, coboundaries_le_cocycles (ρ.comp U.subtype : Representation R U M)
    (Continuous.comp (f := fun p : U × M => ((p.1.1, p.2) : G × M)) hρ (by fun_prop)) ⟨m, rfl⟩⟩

private def Z0 (ρ : Representation R G M) (U' U : Subgroup G) : Submodule R (Z1U ρ U) where
  carrier := {z | ∀ u : U, u.1 ∈ U' → z.1 u = 0}
  zero_mem' := fun _ _ => rfl
  add_mem' := fun {a b} ha hb u hu => by
    show a.1 u + b.1 u = 0
    rw [ha u hu, hb u hu, add_zero]
  smul_mem' := fun c a ha u hu => by
    show c • a.1 u = 0
    rw [ha u hu, smul_zero]

private theorem cocycle_zero_mem_invariants (ρ : Representation R G M) {U' U : Subgroup G} (h : U' ≤ U) [hN : (U'.subgroupOf U).Normal]
    (g : U) (z : Z0 ρ U' U) : z.1.1 g ∈ H0U ρ U' := by
  obtain ⟨hcont, hcoc⟩ := (mem_Z1_iff_cocycle _ _).1 z.1.2
  rw [mem_riemannRochSpace_iff_regularAt_everywhere]
  intro v
  let v' : U := ⟨v.1, h v.2⟩
  have hw : g⁻¹ * v' * g ∈ U'.subgroupOf U := by
    have := hN.conj_mem v' (by rw [Subgroup.mem_subgroupOf]; exact v.2) g⁻¹
    simpa using this
  rw [Subgroup.mem_subgroupOf] at hw
  have hzw : z.1.1 (g⁻¹ * v' * g) = 0 := z.2 _ hw
  have hzv : z.1.1 v' = 0 := z.2 v' v.2
  have e1 := hcoc v' g
  have e2 := hcoc g (g⁻¹ * v' * g)
  rw [show g * (g⁻¹ * v' * g) = v' * g by group, hzw, map_zero, add_zero] at e2
  rw [hzv, zero_add, e2] at e1
  exact e1.symm

end

theorem UpperTheory.V.Base.kerResGen1 :
    ∀ (R G M : Type) [CommRing R] [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup M] [Module R M]
      [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousConstSMul R M] [DiscreteTopology M] (ρ : Representation R G M), ContAction ρ → ∀ (U' U : Subgroup G) (h : U' ≤ U) [(U'.subgroupOf U).Normal] (γ : G), γ ∈ U →
      U ≤ (Subgroup.zpowers γ ⊔ U').topologicalClosure → ∀ T : H0U ρ U' →ₗ[R] H0U ρ U', (∀ m, (T m : M) = ρ γ m - m) →
      ∃ φ : LinearMap.ker (resU ρ h) →ₗ[R] (H0U ρ U' ⧸ LinearMap.range T), Function.Injective φ := by
  intro R G M _ _ _ _ _ _ _ _ _ _ ρ hρ U' U h hN γ hγ hU T hT
  have hcobv : ∀ (m : M) (u : U), (cob ρ hρ U m).1 u = ρ u m - m := fun m u => rfl
  let ev : Z0 ρ U' U →ₗ[R] H0U ρ U' :=
    { toFun := fun a => ⟨a.1.1 ⟨γ, hγ⟩, cocycle_zero_mem_invariants ρ h ⟨γ, hγ⟩ a⟩
      map_add' := fun a b => rfl
      map_smul' := fun c a => rfl }
  let q : Z0 ρ U' U →ₗ[R] (H0U ρ U' ⧸ LinearMap.range T) := (LinearMap.range T).mkQ ∘ₗ ev
  let p0 : Z0 ρ U' U →ₗ[R] H1U ρ U :=
    (Submodule.comap (Z1U ρ U).subtype (B1 (MonoidHom.comp ρ U.subtype))).mkQ ∘ₗ (Z0 ρ U' U).subtype
  have hp0 : ∀ a, p0 a ∈ LinearMap.ker (resU ρ h) := by
    intro a
    rw [LinearMap.mem_ker]
    refine (resU_mk_eq_zero ρ h a.1).2 ⟨0, fun u => ?_⟩
    rw [map_zero, sub_zero]
    exact a.2 _ u.2
  let p : Z0 ρ U' U →ₗ[R] LinearMap.ker (resU ρ h) := LinearMap.codRestrict _ p0 hp0
  have hp : Function.Surjective p := by
    rintro ⟨x, hx⟩
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    obtain ⟨m, hm⟩ := (resU_mk_eq_zero ρ h z).1 (LinearMap.mem_ker.1 hx)
    refine ⟨⟨z - cob ρ hρ U m, fun u hu => ?_⟩, ?_⟩
    · show z.1 u - (cob ρ hρ U m).1 u = 0
      rw [hcobv]
      exact sub_eq_zero.2 (hm ⟨u.1, hu⟩)
    · apply Subtype.ext
      show Submodule.Quotient.mk (z - cob ρ hρ U m) = Submodule.Quotient.mk z
      rw [mk_eq_mk]
      refine ⟨-m, fun u => ?_⟩
      show z.1 u - (cob ρ hρ U m).1 u - z.1 u = ρ u (-m) - -m
      rw [hcobv, map_neg]
      abel
  have hk : ∀ a, p a = 0 ↔ q a = 0 := by
    intro a
    have hpa : p a = 0 ↔ ∃ m : M, ∀ u : U, a.1.1 u - (0 : Z1U ρ U).1 u = ρ u m - m := by
      rw [Subtype.ext_iff]
      show Submodule.Quotient.mk a.1 = (0 : H1U ρ U) ↔ _
      rw [← Submodule.Quotient.mk_zero, mk_eq_mk]
    have hqa : q a = 0 ↔ ∃ n : H0U ρ U', (T n : M) = a.1.1 ⟨γ, hγ⟩ := by
      show Submodule.Quotient.mk (ev a) = 0 ↔ _
      rw [Submodule.Quotient.mk_eq_zero, LinearMap.mem_range]
      constructor
      · rintro ⟨n, hn⟩
        exact ⟨n, congrArg Subtype.val hn⟩
      · rintro ⟨n, hn⟩
        exact ⟨n, Subtype.ext hn⟩
    rw [hpa, hqa]
    constructor
    · rintro ⟨m, hm⟩
      have hmH : m ∈ H0U ρ U' := by
        rw [mem_riemannRochSpace_iff_regularAt_everywhere]
        intro v
        have e := hm ⟨v.1, h v.2⟩
        rw [a.2 ⟨v.1, h v.2⟩ v.2] at e
        exact (sub_eq_zero.1 (by simpa using e.symm))
      refine ⟨⟨m, hmH⟩, ?_⟩
      rw [hT]
      simpa using (hm ⟨γ, hγ⟩).symm
    · rintro ⟨n, hn⟩
      rw [hT] at hn
      have hnH := (mem_riemannRochSpace_iff_regularAt_everywhere _ _).1 n.2
      have hv1 : ∀ u : U, u.1 ∈ U' → (a.1 - cob ρ hρ U n.1).1 u = 0 := by
        intro u hu
        show a.1.1 u - (cob ρ hρ U n.1).1 u = 0
        rw [hcobv, a.2 u hu]
        have e := hnH ⟨u.1, hu⟩
        simp only [MonoidHom.coe_comp, Function.comp_apply, Subgroup.coe_subtype] at e
        simp [e]
      have hv2 : (a.1 - cob ρ hρ U n.1).1 ⟨γ, hγ⟩ = 0 := by
        show a.1.1 ⟨γ, hγ⟩ - (cob ρ hρ U n.1).1 ⟨γ, hγ⟩ = 0
        rw [hcobv, ← hn]
        simp
      refine ⟨n.1, fun u => ?_⟩
      have hz := cocycle_eq_zero ρ h hγ hU (a.1 - cob ρ hρ U n.1) hv1 hv2 u
      have e : a.1.1 u - (cob ρ hρ U n.1).1 u = 0 := hz
      rw [hcobv] at e
      simpa using sub_eq_zero.1 e
  exact exists_inj_of_ker_eq p q hp hk
