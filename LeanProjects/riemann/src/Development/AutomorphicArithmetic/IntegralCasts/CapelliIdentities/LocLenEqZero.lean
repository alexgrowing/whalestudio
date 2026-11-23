import Mathlib

theorem UpperTheory.Reformulated.B.Yzb1.aux1.{u_1, u_2} :
    ∀ {R : Type u_2} [inst : CommRing R] {W : Type u_1} [inst_1 : AddCommGroup W] [inst_2 : _root_.Module R W]
      (S : Submonoid R) (L : Submodule R W) {x y : W},
      x ∈ {x : W | ∃ s ∈ S, s • x ∈ L} → y ∈ {x : W | ∃ s ∈ S, s • x ∈ L} → x + y ∈ {x : W | ∃ s ∈ S, s • x ∈ L} := by
  rintro R _ W _ _ S L x y ⟨s, hs, hx⟩ ⟨t, ht, hy⟩
  refine ⟨s * t, S.mul_mem hs ht, ?_⟩
  have e : (s * t) • (x + y) = t • (s • x) + s • (t • y) := by
    rw [smul_add, mul_smul, smul_comm s t x, mul_smul]
  rw [e]
  exact L.add_mem (L.smul_mem t hx) (L.smul_mem s hy)

theorem UpperTheory.Reformulated.B.Yzb1.aux2.{u_1, u_2} :
    ∀ {R : Type u_1} [inst : CommRing R] {W : Type u_2} [inst_1 : AddCommGroup W] [inst_2 : _root_.Module R W]
      (S : Submonoid R) (L : Submodule R W), ∃ s ∈ S, s • (0 : W) ∈ L := by
  intro R _ W _ _ S L
  exact ⟨1, S.one_mem, by rw [smul_zero]; exact L.zero_mem⟩

theorem UpperTheory.Reformulated.B.Yzb1.aux3.{u_1, u_2} :
    ∀ {R : Type u_2} [inst : CommRing R] {W : Type u_1} [inst_1 : AddCommGroup W] [inst_2 : _root_.Module R W]
      (S : Submonoid R) (L : Submodule R W) (r : R) {x : W},
      x ∈ {x : W | ∃ s ∈ S, s • x ∈ L} → r • x ∈ {x : W | ∃ s ∈ S, s • x ∈ L} := by
  rintro R _ W _ _ S L r x ⟨s, hs, hx⟩
  refine ⟨s, hs, ?_⟩
  rw [smul_comm]
  exact L.smul_mem r hx

noncomputable def UpperTheory.Reformulated.B.Yzb1.locS.{u_1, u_4} :
    {R : Type u_1} →
      [inst : CommRing R] →
        {W : Type u_4} →
          [inst_1 : AddCommGroup W] → [inst_2 : _root_.Module R W] → Submonoid R → Submodule R W → Submodule R W :=
    fun {R : Type u_1} [inst : CommRing R] {W : Type u_4} [inst_1 : AddCommGroup W] [inst_2 : _root_.Module R W]
        (S : Submonoid R) (L : Submodule R W) ↦
      { carrier := {x : W | ∃ s ∈ S, s • x ∈ L}, add_mem' := @UpperTheory.Reformulated.B.Yzb1.aux1 R inst W inst_1 inst_2 S L,
        zero_mem' := UpperTheory.Reformulated.B.Yzb1.aux2 S L, smul_mem' := UpperTheory.Reformulated.B.Yzb1.aux3 S L : Submodule R W }

noncomputable def UpperTheory.Reformulated.B.Yzb1.localization₂.{u_1, u_4} :
    {R : Type u_1} →
      [inst : CommRing R] →
        {W : Type u_4} →
          [inst_1 : AddCommGroup W] →
            [inst_2 : _root_.Module R W] → (p : Ideal R) → [p.IsPrime] → Submodule R W → Submodule R W :=
    fun {R : Type u_1} [CommRing R] {W : Type u_4} [AddCommGroup W] [_root_.Module R W] (p : Ideal R) [p.IsPrime]
        (L : Submodule R W) ↦
      UpperTheory.Reformulated.B.Yzb1.locS p.primeCompl L

noncomputable def UpperTheory.Reformulated.B.Yzb1.locLen.{u_1, u_3} :
    {R : Type u_1} →
      {V : Type u_3} →
        [inst : CommRing R] →
          [inst_1 : AddCommGroup V] →
            [inst_2 : _root_.Module R V] → (p : Ideal R) → [p.IsPrime] → Submodule R V → Submodule R V → ℕ :=
    fun {R : Type u_1} {V : Type u_3} [CommRing R] [AddCommGroup V] [_root_.Module R V] (p : Ideal R) [p.IsPrime]
        (A B : Submodule R V) ↦
      (Module.length R
          (↥(UpperTheory.Reformulated.B.Yzb1.localization₂ p A) ⧸
            Submodule.comap (UpperTheory.Reformulated.B.Yzb1.localization₂ p A).subtype (UpperTheory.Reformulated.B.Yzb1.localization₂ p B))).toNat

noncomputable def UpperTheory.Reformulated.B.Yzb1.lidx.{u_1, u_3} :
    {R : Type u_1} →
      {V : Type u_3} →
        [inst : CommRing R] →
          [inst_1 : AddCommGroup V] →
            [inst_2 : _root_.Module R V] → (p : Ideal R) → [p.IsPrime] → Submodule R V → Submodule R V → ℤ :=
    fun {R : Type u_1} {V : Type u_3} [CommRing R] [AddCommGroup V] [_root_.Module R V] (p : Ideal R) [p.IsPrime]
        (A B : Submodule R V) ↦
      (↑(UpperTheory.Reformulated.B.Yzb1.locLen p A (A ⊓ B)) : ℤ) - (↑(UpperTheory.Reformulated.B.Yzb1.locLen p B (A ⊓ B)) : ℤ)

private lemma UpperTheory.Reformulated.B.Yzb1.locLen_eq_zero {R V : Type*} [CommRing R] [AddCommGroup V]
    [_root_.Module R V] (p : Ideal R) [p.IsPrime] (A C : Submodule R V)
    (h : UpperTheory.Reformulated.B.Yzb1.localization₂ p A ≤ UpperTheory.Reformulated.B.Yzb1.localization₂ p C) :
    UpperTheory.Reformulated.B.Yzb1.locLen p A C = 0 := by
  have hs : Subsingleton (↥(UpperTheory.Reformulated.B.Yzb1.localization₂ p A) ⧸
      Submodule.comap (UpperTheory.Reformulated.B.Yzb1.localization₂ p A).subtype (UpperTheory.Reformulated.B.Yzb1.localization₂ p C)) := by
    rw [Submodule.Quotient.subsingleton_iff, Submodule.comap_subtype_eq_top]
    exact h
  have hl := (Module.length_eq_zero_iff (R := R)).mpr hs
  show (Module.length R _).toNat = 0
  rw [hl]
  rfl

private lemma UpperTheory.Reformulated.B.Yzb1.localization_le_localization_inf {R V : Type*} [CommRing R] [AddCommGroup V]
    [_root_.Module R V] (p : Ideal R) [p.IsPrime] (A B : Submodule R V) (s : R) (hs : s ∉ p)
    (h : ∀ x ∈ A, s • x ∈ B) :
    UpperTheory.Reformulated.B.Yzb1.localization₂ p A ≤ UpperTheory.Reformulated.B.Yzb1.localization₂ p (A ⊓ B) := by
  rintro x ⟨t, ht, hx⟩
  refine ⟨s * t, p.primeCompl.mul_mem hs ht, ?_⟩
  rw [mul_smul]
  exact ⟨A.smul_mem s hx, h _ hx⟩

theorem UpperTheory.Reformulated.B.Yzb1.lidx_finite :
    ∀ {K V : Type} [inst : Field K] [NumberField K] [inst_2 : AddCommGroup V]
      [inst_3 : _root_.Module (NumberField.RingOfIntegers K) V] (A B : Submodule (NumberField.RingOfIntegers K) V)
      (s : NumberField.RingOfIntegers K),
      s ≠ (0 : NumberField.RingOfIntegers K) →
        (∀ x ∈ A, s • x ∈ B) →
          (∀ x ∈ B, s • x ∈ A) →
            {w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K) |
                UpperTheory.Reformulated.B.Yzb1.lidx w.asIdeal A B ≠ (0 : ℤ)}.Finite := by
  intro K V _ _ _ _ A B s hs hAB hBA
  have hI : Ideal.span {s} ≠ (0 : Ideal (NumberField.RingOfIntegers K)) := by
    simpa using hs
  refine (Ideal.finite_factors hI).subset ?_
  intro w hw
  by_contra hc
  have hsw : s ∉ w.asIdeal := fun hm => hc (Ideal.dvd_span_singleton.mpr hm)
  apply hw
  have h1 := UpperTheory.Reformulated.B.Yzb1.locLen_eq_zero w.asIdeal A (A ⊓ B)
    (UpperTheory.Reformulated.B.Yzb1.localization_le_localization_inf w.asIdeal A B s hsw hAB)
  have h2 := UpperTheory.Reformulated.B.Yzb1.locLen_eq_zero w.asIdeal B (A ⊓ B)
    (by rw [inf_comm]; exact UpperTheory.Reformulated.B.Yzb1.localization_le_localization_inf w.asIdeal B A s hsw hBA)
  show ((UpperTheory.Reformulated.B.Yzb1.locLen w.asIdeal A (A ⊓ B) : ℕ) : ℤ) -
    ((UpperTheory.Reformulated.B.Yzb1.locLen w.asIdeal B (A ⊓ B) : ℕ) : ℤ) = 0
  rw [h1, h2]
  simp
