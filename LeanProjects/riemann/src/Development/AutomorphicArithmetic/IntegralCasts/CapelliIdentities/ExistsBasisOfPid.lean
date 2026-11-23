import Mathlib

theorem UpperTheory.Reformulated.B.Qi33.aux1.{u_1, u_2} :
    ∀ {R : Type u_2} [inst : CommRing R] {W : Type u_1} [inst_1 : AddCommGroup W] [inst_2 : _root_.Module R W]
      (S : Submonoid R) (L : Submodule R W) {x y : W},
      x ∈ {x : W | ∃ s ∈ S, s • x ∈ L} → y ∈ {x : W | ∃ s ∈ S, s • x ∈ L} → x + y ∈ {x : W | ∃ s ∈ S, s • x ∈ L} := by
  intro R _ W _ _ S L x y hx hy
  obtain ⟨s, hs, hx⟩ := hx
  obtain ⟨t, ht, hy⟩ := hy
  refine ⟨s * t, S.mul_mem hs ht, ?_⟩
  rw [smul_add]
  refine L.add_mem ?_ ?_
  · rw [mul_comm, mul_smul]
    exact L.smul_mem t hx
  · rw [mul_smul]
    exact L.smul_mem s hy

theorem UpperTheory.Reformulated.B.Qi33.aux2.{u_1, u_2} :
    ∀ {R : Type u_1} [inst : CommRing R] {W : Type u_2} [inst_1 : AddCommGroup W] [inst_2 : _root_.Module R W]
      (S : Submonoid R) (L : Submodule R W), ∃ s ∈ S, s • (0 : W) ∈ L := by
  intro R _ W _ _ S L
  exact ⟨1, S.one_mem, by simp⟩

theorem UpperTheory.Reformulated.B.Qi33.aux3.{u_1, u_2} :
    ∀ {R : Type u_2} [inst : CommRing R] {W : Type u_1} [inst_1 : AddCommGroup W] [inst_2 : _root_.Module R W]
      (S : Submonoid R) (L : Submodule R W) (r : R) {x : W},
      x ∈ {x : W | ∃ s ∈ S, s • x ∈ L} → r • x ∈ {x : W | ∃ s ∈ S, s • x ∈ L} := by
  intro R _ W _ _ S L r x hx
  obtain ⟨s, hs, hx⟩ := hx
  refine ⟨s, hs, ?_⟩
  rw [smul_comm]
  exact L.smul_mem r hx

noncomputable def UpperTheory.Reformulated.B.Qi33.locS.{u_1, u_4} :
    {R : Type u_1} →
      [inst : CommRing R] →
        {W : Type u_4} →
          [inst_1 : AddCommGroup W] → [inst_2 : _root_.Module R W] → Submonoid R → Submodule R W → Submodule R W :=
    fun {R : Type u_1} [inst : CommRing R] {W : Type u_4} [inst_1 : AddCommGroup W] [inst_2 : _root_.Module R W]
        (S : Submonoid R) (L : Submodule R W) ↦
      { carrier := {x : W | ∃ s ∈ S, s • x ∈ L}, add_mem' := @UpperTheory.Reformulated.B.Qi33.aux1 R inst W inst_1 inst_2 S L,
        zero_mem' := UpperTheory.Reformulated.B.Qi33.aux2 S L, smul_mem' := UpperTheory.Reformulated.B.Qi33.aux3 S L : Submodule R W }

noncomputable def UpperTheory.Reformulated.B.Qi33.localization₂.{u_1, u_4} :
    {R : Type u_1} →
      [inst : CommRing R] →
        {W : Type u_4} →
          [inst_1 : AddCommGroup W] →
            [inst_2 : _root_.Module R W] → (p : Ideal R) → [p.IsPrime] → Submodule R W → Submodule R W :=
    fun {R : Type u_1} [CommRing R] {W : Type u_4} [AddCommGroup W] [_root_.Module R W] (p : Ideal R) [p.IsPrime]
        (L : Submodule R W) ↦
      UpperTheory.Reformulated.B.Qi33.locS p.primeCompl L

private theorem UpperTheory.Reformulated.B.Qi33.mem_locS_iff {R : Type*} [CommRing R] {W : Type*} [AddCommGroup W]
    [Module R W] (S : Submonoid R) (R' : Type*) [CommRing R'] [Algebra R R'] [IsLocalization S R']
    [Module R' W] [IsScalarTower R R' W] (L : Submodule R W) (x : W) :
    x ∈ UpperTheory.Reformulated.B.Qi33.locS S L ↔ x ∈ Submodule.span R' (L : Set W) := by
  rw [IsLocalization.mem_span_iff S, Submodule.span_eq]
  constructor
  · rintro ⟨s, hs, hx⟩
    refine ⟨s • x, hx, ⟨s, hs⟩, ?_⟩
    rw [← algebraMap_smul R' s x, smul_smul]
    have h := IsLocalization.mk'_spec R' (1 : R) (⟨s, hs⟩ : S)
    simp only [map_one] at h
    rw [h, one_smul]
  · rintro ⟨y, hy, z, rfl⟩
    refine ⟨z, z.2, ?_⟩
    rw [← algebraMap_smul R' (z : R), smul_smul]
    have h := IsLocalization.mk'_spec' R' (1 : R) z
    simp only [map_one] at h
    rw [h, one_smul]
    exact hy

private theorem UpperTheory.Reformulated.B.Qi33.exists_basis_of_pid {D K Z : Type} [CommRing D] [IsDomain D]
    [IsPrincipalIdealRing D] [Field K] [Algebra D K] [IsFractionRing D K] [AddCommGroup Z]
    [Module K Z] [Module D Z] [IsScalarTower D K Z] (M : Submodule D Z) (hM : M.FG)
    (hs : Submodule.span K (M : Set Z) = ⊤) :
    ∃ b : Module.Basis (Fin (Module.finrank K Z)) K Z, Submodule.span D (Set.range b) = M := by
  haveI : Module.Finite D M := Module.Finite.iff_fg.mpr hM
  haveI : Module.IsTorsionFree D Z := Module.IsTorsionFree.trans_faithfulSMul D K Z
  haveI : Module.Free D M := inferInstance
  let c := Module.finBasis D M
  let v : Fin (Module.finrank D M) → Z := fun i => (c i : Z)
  have hli : LinearIndependent D v := c.linearIndependent.map' M.subtype M.ker_subtype
  have hliK : LinearIndependent K v := (LinearIndependent.iff_fractionRing D K).mp hli
  have hsp : Submodule.span D (Set.range v) = M := by
    have h1 : Set.range v = M.subtype '' Set.range c := by
      rw [← Set.range_comp]; rfl
    rw [h1, ← Submodule.map_span, c.span_eq, Submodule.map_top, Submodule.range_subtype]
  have hspK : ⊤ ≤ Submodule.span K (Set.range v) := by
    rw [← Submodule.span_span_of_tower D K (Set.range v), hsp, hs]
  let b0 := Module.Basis.mk hliK hspK
  have hn : Module.finrank K Z = Module.finrank D M := by
    simpa using Module.finrank_eq_card_basis b0
  refine ⟨b0.reindex (finCongr hn.symm), ?_⟩
  rw [Module.Basis.range_reindex, Module.Basis.coe_mk, hsp]

theorem UpperTheory.Reformulated.B.Qi33.exists_loc_basis :
    ∀ {K : Type} [inst : Field K] [NumberField K] [StarRing K] {Z : Type} [inst_3 : AddCommGroup Z]
      [inst_4 : _root_.Module K Z] [inst_5 : _root_.Module (NumberField.RingOfIntegers K) Z]
      [IsScalarTower (NumberField.RingOfIntegers K) K Z] [FiniteDimensional K Z]
      (w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
      (A : Submodule (NumberField.RingOfIntegers K) Z),
      A.FG →
        Submodule.span K (↑A : Set Z) = ⊤ →
          ∃ (b : Module.Basis (Fin (Module.finrank K Z)) K Z),
            UpperTheory.Reformulated.B.Qi33.localization₂ w.asIdeal A =
              UpperTheory.Reformulated.B.Qi33.localization₂ w.asIdeal
                (Submodule.span (NumberField.RingOfIntegers K) (Set.range (⇑b : Fin (Module.finrank K Z) → Z))) := by
  intro K _ _ _ Z _ _ _ _ _ w A hA hsp
  let D := Localization.subalgebra.ofField K w.asIdeal.primeCompl
    (Ideal.primeCompl_le_nonZeroDivisors w.asIdeal)
  haveI hloc : IsLocalization w.asIdeal.primeCompl D :=
    Localization.subalgebra.isLocalization_ofField K _ _
  haveI : IsFractionRing D K := Localization.subalgebra.isFractionRing_ofField K _ _
  haveI : IsDiscreteValuationRing D :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain
      (NumberField.RingOfIntegers K) w.ne_bot D
  haveI : IsScalarTower (NumberField.RingOfIntegers K) D Z :=
    IsScalarTower.of_algebraMap_smul fun r z => algebraMap_smul K r z
  have hfg : (Submodule.span D (A : Set Z)).FG := by
    obtain ⟨t, rfl⟩ := hA
    exact ⟨t, (Submodule.span_span_of_tower _ _ _).symm⟩
  obtain ⟨b, hb⟩ := UpperTheory.Reformulated.B.Qi33.exists_basis_of_pid (D := D) (K := K) _ hfg
    (by rw [Submodule.span_span_of_tower, hsp])
  refine ⟨b, ?_⟩
  ext x
  unfold UpperTheory.Reformulated.B.Qi33.localization₂
  rw [UpperTheory.Reformulated.B.Qi33.mem_locS_iff _ D, UpperTheory.Reformulated.B.Qi33.mem_locS_iff _ D,
    Submodule.span_span_of_tower, hb]
