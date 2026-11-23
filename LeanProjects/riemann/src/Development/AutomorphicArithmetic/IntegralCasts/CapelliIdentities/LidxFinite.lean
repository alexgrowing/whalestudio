import Mathlib

theorem UpperTheory.Reformulated.B.Yzb2.aux1.{u_1, u_2} :
    ∀ {R : Type u_2} [inst : CommRing R] {W : Type u_1} [inst_1 : AddCommGroup W] [inst_2 : _root_.Module R W]
      (S : Submonoid R) (L : Submodule R W) {x y : W},
      x ∈ {x : W | ∃ s ∈ S, s • x ∈ L} → y ∈ {x : W | ∃ s ∈ S, s • x ∈ L} → x + y ∈ {x : W | ∃ s ∈ S, s • x ∈ L} := by
  rintro R _ W _ _ S L x y ⟨s, hs, hx⟩ ⟨t, ht, hy⟩
  refine ⟨s * t, S.mul_mem hs ht, ?_⟩
  have e : (s * t) • (x + y) = t • (s • x) + s • (t • y) := by
    simp only [smul_add, smul_smul, mul_comm]
  rw [e]
  exact L.add_mem (L.smul_mem _ hx) (L.smul_mem _ hy)

theorem UpperTheory.Reformulated.B.Yzb2.aux2.{u_1, u_2} :
    ∀ {R : Type u_1} [inst : CommRing R] {W : Type u_2} [inst_1 : AddCommGroup W] [inst_2 : _root_.Module R W]
      (S : Submonoid R) (L : Submodule R W), ∃ s ∈ S, s • (0 : W) ∈ L := by
  intro R _ W _ _ S L
  exact ⟨1, S.one_mem, by simp⟩

theorem UpperTheory.Reformulated.B.Yzb2.aux3.{u_1, u_2} :
    ∀ {R : Type u_2} [inst : CommRing R] {W : Type u_1} [inst_1 : AddCommGroup W] [inst_2 : _root_.Module R W]
      (S : Submonoid R) (L : Submodule R W) (r : R) {x : W},
      x ∈ {x : W | ∃ s ∈ S, s • x ∈ L} → r • x ∈ {x : W | ∃ s ∈ S, s • x ∈ L} := by
  rintro R _ W _ _ S L r x ⟨s, hs, hx⟩
  refine ⟨s, hs, ?_⟩
  rw [smul_comm]
  exact L.smul_mem _ hx

noncomputable def UpperTheory.Reformulated.B.Yzb2.locS.{u_1, u_4} :
    {R : Type u_1} →
      [inst : CommRing R] →
        {W : Type u_4} →
          [inst_1 : AddCommGroup W] → [inst_2 : _root_.Module R W] → Submonoid R → Submodule R W → Submodule R W :=
    fun {R : Type u_1} [inst : CommRing R] {W : Type u_4} [inst_1 : AddCommGroup W] [inst_2 : _root_.Module R W]
        (S : Submonoid R) (L : Submodule R W) ↦
      { carrier := {x : W | ∃ s ∈ S, s • x ∈ L}, add_mem' := @UpperTheory.Reformulated.B.Yzb2.aux1 R inst W inst_1 inst_2 S L,
        zero_mem' := UpperTheory.Reformulated.B.Yzb2.aux2 S L, smul_mem' := UpperTheory.Reformulated.B.Yzb2.aux3 S L : Submodule R W }

noncomputable def UpperTheory.Reformulated.B.Yzb2.localization₂.{u_1, u_4} :
    {R : Type u_1} →
      [inst : CommRing R] →
        {W : Type u_4} →
          [inst_1 : AddCommGroup W] →
            [inst_2 : _root_.Module R W] → (p : Ideal R) → [p.IsPrime] → Submodule R W → Submodule R W :=
    fun {R : Type u_1} [CommRing R] {W : Type u_4} [AddCommGroup W] [_root_.Module R W] (p : Ideal R) [p.IsPrime]
        (L : Submodule R W) ↦
      UpperTheory.Reformulated.B.Yzb2.locS p.primeCompl L

noncomputable def UpperTheory.Reformulated.B.Yzb2.locLen.{u_1, u_3} :
    {R : Type u_1} →
      {V : Type u_3} →
        [inst : CommRing R] →
          [inst_1 : AddCommGroup V] →
            [inst_2 : _root_.Module R V] → (p : Ideal R) → [p.IsPrime] → Submodule R V → Submodule R V → ℕ :=
    fun {R : Type u_1} {V : Type u_3} [CommRing R] [AddCommGroup V] [_root_.Module R V] (p : Ideal R) [p.IsPrime]
        (A B : Submodule R V) ↦
      (Module.length R
          (↥(UpperTheory.Reformulated.B.Yzb2.localization₂ p A) ⧸
            Submodule.comap (UpperTheory.Reformulated.B.Yzb2.localization₂ p A).subtype (UpperTheory.Reformulated.B.Yzb2.localization₂ p B))).toNat

noncomputable def UpperTheory.Reformulated.B.Yzb2.lidx.{u_1, u_3} :
    {R : Type u_1} →
      {V : Type u_3} →
        [inst : CommRing R] →
          [inst_1 : AddCommGroup V] →
            [inst_2 : _root_.Module R V] → (p : Ideal R) → [p.IsPrime] → Submodule R V → Submodule R V → ℤ :=
    fun {R : Type u_1} {V : Type u_3} [CommRing R] [AddCommGroup V] [_root_.Module R V] (p : Ideal R) [p.IsPrime]
        (A B : Submodule R V) ↦
      (↑(UpperTheory.Reformulated.B.Yzb2.locLen p A (A ⊓ B)) : ℤ) - (↑(UpperTheory.Reformulated.B.Yzb2.locLen p B (A ⊓ B)) : ℤ)

private theorem UpperTheory.Reformulated.B.Yzb2.common_mul {R V : Type*} [CommRing R] [IsDomain R] [AddCommGroup V]
    [_root_.Module R V] (B : Submodule R V) (T : Finset V)
    (h : ∀ x ∈ T, ∃ s : R, s ≠ 0 ∧ s • x ∈ B) :
    ∃ s : R, s ≠ 0 ∧ ∀ x ∈ Submodule.span R (T : Set V), s • x ∈ B := by
  classical
  induction T using Finset.induction_on with
  | empty =>
    refine ⟨1, one_ne_zero, fun x hx => ?_⟩
    have : x = 0 := by simpa using hx
    simp [this]
  | insert a T _ ih =>
    obtain ⟨t, ht, htT⟩ := ih (fun x hx => h x (Finset.mem_insert_of_mem hx))
    obtain ⟨s, hs, hsa⟩ := h a (Finset.mem_insert_self a T)
    refine ⟨s * t, mul_ne_zero hs ht, fun x hx => ?_⟩
    rw [Finset.coe_insert, Submodule.mem_span_insert] at hx
    obtain ⟨c, z, hz, rfl⟩ := hx
    have e : (s * t) • (c • a + z) = (t * c) • (s • a) + s • (t • z) := by
      simp only [smul_add, smul_smul]
      congr 2
      ring
    rw [e]
    exact B.add_mem (B.smul_mem _ hsa) (B.smul_mem _ (htT z hz))

private theorem UpperTheory.Reformulated.B.Yzb2.locLen_eq_zero {R V : Type*} [CommRing R] [AddCommGroup V]
    [_root_.Module R V] (p : Ideal R) [p.IsPrime] (X Y : Submodule R V) (u : R) (hu : u ∉ p)
    (h : ∀ x ∈ X, u • x ∈ Y) : UpperTheory.Reformulated.B.Yzb2.locLen p X Y = 0 := by
  have top : Submodule.comap (UpperTheory.Reformulated.B.Yzb2.localization₂ p X).subtype (UpperTheory.Reformulated.B.Yzb2.localization₂ p Y) = ⊤ := by
    rw [eq_top_iff]
    rintro ⟨y, v, hv, hy⟩ -
    refine ⟨u * v, p.primeCompl.mul_mem hu hv, ?_⟩
    rw [mul_smul]
    exact h _ hy
  have : Subsingleton (↥(UpperTheory.Reformulated.B.Yzb2.localization₂ p X) ⧸
      Submodule.comap (UpperTheory.Reformulated.B.Yzb2.localization₂ p X).subtype (UpperTheory.Reformulated.B.Yzb2.localization₂ p Y)) :=
    Submodule.Quotient.subsingleton_iff.mpr top
  simp only [UpperTheory.Reformulated.B.Yzb2.locLen, Module.length_eq_zero, ENat.toNat_zero]

theorem UpperTheory.Reformulated.B.Yzb2.lidx_finite :
    ∀ {K V : Type} [inst : Field K] [NumberField K] [inst_2 : AddCommGroup V]
      [inst_3 : _root_.Module (NumberField.RingOfIntegers K) V] (A B : Submodule (NumberField.RingOfIntegers K) V),
      A.FG →
        B.FG →
          (∀ x ∈ A, ∃ (s : NumberField.RingOfIntegers K), s ≠ (0 : NumberField.RingOfIntegers K) ∧ s • x ∈ B) →
            (∀ x ∈ B, ∃ (s : NumberField.RingOfIntegers K), s ≠ (0 : NumberField.RingOfIntegers K) ∧ s • x ∈ A) →
              {w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K) |
                  UpperTheory.Reformulated.B.Yzb2.lidx w.asIdeal A B ≠ (0 : ℤ)}.Finite := by
  intro K V _ _ _ _ A B hA hB hAB hBA
  obtain ⟨TA, rfl⟩ := id hA
  obtain ⟨TB, rfl⟩ := id hB
  obtain ⟨s, hs, hsA⟩ := UpperTheory.Reformulated.B.Yzb2.common_mul _ TA
    (fun x hx => hAB x (Submodule.subset_span hx))
  obtain ⟨t, ht, htB⟩ := UpperTheory.Reformulated.B.Yzb2.common_mul _ TB
    (fun x hx => hBA x (Submodule.subset_span hx))
  have hst : Ideal.span {s * t} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact mul_ne_zero hs ht
  refine (Ideal.finite_factors hst).subset fun w hw => ?_
  rw [Set.mem_setOf_eq] at hw ⊢
  rw [Ideal.dvd_span_singleton]
  by_contra hmem
  apply hw
  have hsw : s ∉ w.asIdeal := fun h => hmem (Ideal.mul_mem_right _ _ h)
  have htw : t ∉ w.asIdeal := fun h => hmem (Ideal.mul_mem_left _ _ h)
  have h1 := UpperTheory.Reformulated.B.Yzb2.locLen_eq_zero w.asIdeal _ (Submodule.span _ (TA : Set V) ⊓ Submodule.span _ (TB : Set V)) s hsw
    (fun x hx => ⟨Submodule.smul_mem _ _ hx, hsA x hx⟩)
  have h2 := UpperTheory.Reformulated.B.Yzb2.locLen_eq_zero w.asIdeal _ (Submodule.span _ (TA : Set V) ⊓ Submodule.span _ (TB : Set V)) t htw
    (fun x hx => ⟨htB x hx, Submodule.smul_mem _ _ hx⟩)
  simp only [UpperTheory.Reformulated.B.Yzb2.lidx, h1, h2, Nat.cast_zero, sub_zero]
