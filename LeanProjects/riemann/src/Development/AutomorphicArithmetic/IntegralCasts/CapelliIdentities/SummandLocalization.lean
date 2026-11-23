import Mathlib

theorem UpperTheory.Reformulated.B.SummandLocalization.aux1.{u_1, u_2} :
    ∀ {R : Type u_2} [inst : CommRing R] {W : Type u_1} [inst_1 : AddCommGroup W] [inst_2 : _root_.Module R W]
      (S : Submonoid R) (L : Submodule R W) {x y : W},
      x ∈ {x : W | ∃ s ∈ S, s • x ∈ L} → y ∈ {x : W | ∃ s ∈ S, s • x ∈ L} → x + y ∈ {x : W | ∃ s ∈ S, s • x ∈ L} := by
  rintro R _ W _ _ S L x y ⟨s, hs, hx⟩ ⟨t, ht, hy⟩
  refine ⟨s * t, S.mul_mem hs ht, ?_⟩
  rw [smul_add, mul_smul s t y, mul_comm s t, mul_smul t s x]
  exact L.add_mem (L.smul_mem t hx) (L.smul_mem s hy)

theorem UpperTheory.Reformulated.B.SummandLocalization.aux2.{u_1, u_2} :
    ∀ {R : Type u_1} [inst : CommRing R] {W : Type u_2} [inst_1 : AddCommGroup W] [inst_2 : _root_.Module R W]
      (S : Submonoid R) (L : Submodule R W), ∃ s ∈ S, s • (0 : W) ∈ L := by
  intro R _ W _ _ S L
  exact ⟨1, S.one_mem, by rw [smul_zero]; exact L.zero_mem⟩

theorem UpperTheory.Reformulated.B.SummandLocalization.aux3.{u_1, u_2} :
    ∀ {R : Type u_2} [inst : CommRing R] {W : Type u_1} [inst_1 : AddCommGroup W] [inst_2 : _root_.Module R W]
      (S : Submonoid R) (L : Submodule R W) (r : R) {x : W},
      x ∈ {x : W | ∃ s ∈ S, s • x ∈ L} → r • x ∈ {x : W | ∃ s ∈ S, s • x ∈ L} := by
  rintro R _ W _ _ S L r x ⟨s, hs, hx⟩
  refine ⟨s, hs, ?_⟩
  rw [smul_comm]
  exact L.smul_mem r hx

noncomputable def UpperTheory.Reformulated.B.SummandLocalization.locS.{u_1, u_4} :
    {R : Type u_1} →
      [inst : CommRing R] →
        {W : Type u_4} →
          [inst_1 : AddCommGroup W] → [inst_2 : _root_.Module R W] → Submonoid R → Submodule R W → Submodule R W :=
    fun {R : Type u_1} [inst : CommRing R] {W : Type u_4} [inst_1 : AddCommGroup W] [inst_2 : _root_.Module R W]
        (S : Submonoid R) (L : Submodule R W) ↦
      { carrier := {x : W | ∃ s ∈ S, s • x ∈ L}, add_mem' := @UpperTheory.Reformulated.B.SummandLocalization.aux1 R inst W inst_1 inst_2 S L,
        zero_mem' := UpperTheory.Reformulated.B.SummandLocalization.aux2 S L, smul_mem' := UpperTheory.Reformulated.B.SummandLocalization.aux3 S L : Submodule R W }

noncomputable def UpperTheory.Reformulated.B.SummandLocalization.locF :
    {K F W : Type} →
      [inst : Field K] →
        [inst_1 : Field F] →
          [Algebra F K] →
            [inst_3 : AddCommGroup W] →
              [inst_4 : _root_.Module (NumberField.RingOfIntegers K) W] →
                Ideal (NumberField.RingOfIntegers F) →
                  Submodule (NumberField.RingOfIntegers K) W → Submodule (NumberField.RingOfIntegers K) W :=
    fun {K F W : Type} [Field K] [Field F] [Algebra F K] [AddCommGroup W] [_root_.Module (NumberField.RingOfIntegers K) W]
        (𝔭 : Ideal (NumberField.RingOfIntegers F)) (L : Submodule (NumberField.RingOfIntegers K) W) ↦
      UpperTheory.Reformulated.B.SummandLocalization.locS
        (Submonoid.closure
          {s : NumberField.RingOfIntegers K |
            ∃ t ∉ 𝔭,
              (Algebra.algebraMap (NumberField.RingOfIntegers F) (NumberField.RingOfIntegers K) :
                    NumberField.RingOfIntegers F → NumberField.RingOfIntegers K)
                  t =
                s})
        L

noncomputable def UpperTheory.Reformulated.B.SummandLocalization.SummandLoc :
    Prop :=
    ∀ (K F V : Type) [inst : Field K] [NumberField K] [inst_2 : Field F] [NumberField F] [inst_4 : Algebra F K]
      [inst_5 : AddCommGroup V] [inst_6 : _root_.Module K V] [FiniteDimensional K V]
      [inst_8 : _root_.Module (NumberField.RingOfIntegers K) V] [inst_9 : IsScalarTower (NumberField.RingOfIntegers K) K V]
      (X : Submodule K V) (𝔭 : Ideal (NumberField.RingOfIntegers F)),
      𝔭.IsMaximal →
        ∀ (Λ : Submodule (NumberField.RingOfIntegers K) V),
          (∃ (Λ₀ : Submodule (NumberField.RingOfIntegers K) V), Submodule.IsLattice K Λ₀ ∧ UpperTheory.Reformulated.B.SummandLocalization.locF 𝔭 Λ₀ = Λ) →
            ∃ (π : V →ₗ[K] V), (∀ (v : V), (π : V → V) v ∈ X) ∧ (∀ x ∈ X, (π : V → V) x = x) ∧ ∀ y ∈ Λ, (π : V → V) y ∈ Λ

private theorem UpperTheory.Reformulated.B.SummandLocalization.lattice_isLocalizedModule {R K W : Type*} [CommRing R] [IsDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] [AddCommGroup W] [Module K W] [Module R W] [IsScalarTower R K W]
    (M : Submodule R W) (hM : Submodule.span K (M : Set W) = ⊤) :
    IsLocalizedModule (nonZeroDivisors R) M.subtype where
  map_units s := by
    have hs : algebraMap R K s ≠ 0 := (IsLocalization.map_units K s).ne_zero
    rw [Module.End.isUnit_iff]
    have h : ((algebraMap R (Module.End R W)) s : W → W) = fun w => (algebraMap R K s) • w := by
      funext w
      simp
    rw [h]
    exact MulAction.bijective (Units.mk0 _ hs)
  surj y := by
    have hy : y ∈ Submodule.span K (M : Set W) := hM ▸ Submodule.mem_top
    obtain ⟨t, ht⟩ := multiple_mem_span_of_mem_localization_span (nonZeroDivisors R) K (M : Set W) y hy
    rw [Submodule.span_eq] at ht
    exact ⟨⟨⟨_, ht⟩, t⟩, rfl⟩
  exists_of_eq h := ⟨1, by rw [Subtype.ext h]⟩

private theorem UpperTheory.Reformulated.B.SummandLocalization.exists_proj {R K V : Type*} [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]
    (X : Submodule K V) (L : Submodule R V) (hL : Submodule.IsLattice K L) :
    ∃ π : V →ₗ[K] V, (∀ v, π v ∈ X) ∧ (∀ x ∈ X, π x = x) ∧ ∀ y ∈ L, π y ∈ L := by
  let q : V →ₗ[R] V ⧸ X := X.mkQ.restrictScalars R
  let M : Submodule R (V ⧸ X) := L.map q
  have hM : Submodule.span K (M : Set (V ⧸ X)) = ⊤ := by
    have h : (M : Set (V ⧸ X)) = X.mkQ '' (L : Set V) := rfl
    rw [h, ← Submodule.map_span, hL.span_eq_top, Submodule.map_top, Submodule.range_mkQ]
  haveI : Module.Finite R M := Module.Finite.iff_fg.2 (hL.fg.map q)
  haveI : Module.IsTorsionFree R (V ⧸ X) := Module.IsTorsionFree.trans_faithfulSMul R K (V ⧸ X)
  haveI : Module.FinitePresentation R M := Module.finitePresentation_of_finite R M
  haveI : Module.Projective R M := Module.Flat.projective_of_finitePresentation
  have hsurj : Function.Surjective (q.submoduleMap L) := LinearMap.submoduleMap_surjective q L
  obtain ⟨s, hs⟩ := Module.projective_lifting_property (q.submoduleMap L) LinearMap.id hsurj
  haveI := UpperTheory.Reformulated.B.SummandLocalization.lattice_isLocalizedModule M hM
  have hb : IsBaseChange K M.subtype := IsLocalizedModule.isBaseChange (nonZeroDivisors R) K M.subtype
  let σ : (V ⧸ X) →ₗ[K] V := hb.lift (L.subtype ∘ₗ s)
  have hσ : ∀ m : M, σ m = (s m : V) := fun m => hb.lift_eq (L.subtype ∘ₗ s) m
  have hq : X.mkQ ∘ₗ σ = LinearMap.id := by
    apply LinearMap.ext_on hM
    intro m hm
    have h1 := congrArg Subtype.val (LinearMap.congr_fun hs ⟨m, hm⟩)
    rw [LinearMap.comp_apply, hσ ⟨m, hm⟩]
    exact h1
  refine ⟨LinearMap.id - σ ∘ₗ X.mkQ, fun v => ?_, fun x hx => ?_, fun y hy => ?_⟩
  · rw [← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply]
    have h1 := LinearMap.congr_fun hq (X.mkQ v)
    rw [LinearMap.comp_apply, LinearMap.id_apply] at h1
    rw [LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply, map_sub, h1, sub_self]
  · have h1 : X.mkQ x = 0 := (Submodule.Quotient.mk_eq_zero X).2 hx
    rw [LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply, h1, map_zero, sub_zero]
  · have h1 := hσ ⟨q y, Submodule.mem_map_of_mem hy⟩
    have h2 : σ (X.mkQ y) ∈ L := by
      have h3 : σ (X.mkQ y) = _ := h1
      rw [h3]
      exact Subtype.property _
    exact L.sub_mem hy h2

theorem UpperTheory.Reformulated.B.SummandLocalization.summand_localization :
    UpperTheory.Reformulated.B.SummandLocalization.SummandLoc := by
  rintro K F V _ _ _ _ _ _ _ _ _ _ X 𝔭 _ Λ ⟨Λ₀, hΛ₀, rfl⟩
  obtain ⟨π, h1, h2, h3⟩ := UpperTheory.Reformulated.B.SummandLocalization.exists_proj X Λ₀ hΛ₀
  refine ⟨π, h1, h2, ?_⟩
  rintro y ⟨s, hs, hy⟩
  refine ⟨s, hs, ?_⟩
  rw [← LinearMap.map_smul_of_tower]
  exact h3 _ hy
