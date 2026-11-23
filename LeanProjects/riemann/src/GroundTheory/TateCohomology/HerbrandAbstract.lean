import Mathlib

namespace GroundTheory.GroupCoh

section Card

theorem natCard_eq_ker_mul_range {X Y : Type*} [AddGroup X] [AddGroup Y] (φ : X →+ Y) :
    Nat.card X = Nat.card φ.ker * Nat.card φ.range := by
  rw [← AddSubgroup.index_ker φ, AddSubgroup.card_mul_index]

theorem finite_of_exact {X Y Z : Type*} [AddGroup X] [AddGroup Y] [AddGroup Z]
    (d : X →+ Y) (e : Y →+ Z) (h : e.ker = d.range) [Finite X] [Finite Z] : Finite Y := by
  have h1 : Finite d.range := Finite.of_surjective _ d.rangeRestrict_surjective
  have h2 : Finite e.ker := by rw [h]; exact h1
  apply Nat.finite_of_card_ne_zero
  rw [natCard_eq_ker_mul_range e]
  exact Nat.mul_ne_zero Nat.card_pos.ne' Nat.card_pos.ne'

theorem natCard_hexagon {X₁ X₂ X₃ X₄ X₅ X₆ : Type*} [AddGroup X₁] [AddGroup X₂] [AddGroup X₃]
    [AddGroup X₄] [AddGroup X₅] [AddGroup X₆]
    (d₁ : X₁ →+ X₂) (d₂ : X₂ →+ X₃) (d₃ : X₃ →+ X₄) (d₄ : X₄ →+ X₅) (d₅ : X₅ →+ X₆)
    (d₆ : X₆ →+ X₁) (e₁ : d₁.ker = d₆.range) (e₂ : d₂.ker = d₁.range) (e₃ : d₃.ker = d₂.range)
    (e₄ : d₄.ker = d₃.range) (e₅ : d₅.ker = d₄.range) (e₆ : d₆.ker = d₅.range) :
    Nat.card X₁ * Nat.card X₃ * Nat.card X₅ = Nat.card X₂ * Nat.card X₄ * Nat.card X₆ := by
  rw [natCard_eq_ker_mul_range d₁, natCard_eq_ker_mul_range d₂, natCard_eq_ker_mul_range d₃,
    natCard_eq_ker_mul_range d₄, natCard_eq_ker_mul_range d₅, natCard_eq_ker_mul_range d₆,
    e₁, e₂, e₃, e₄, e₅, e₆]
  ring

end Card

section Defs

variable {A : Type*} [AddCommGroup A]

abbrev KerModRange (f g : A →+ A) : Type _ :=
  f.ker ⧸ g.range.addSubgroupOf f.ker

def HasHerbrandQuotient (f g : A →+ A) : Prop :=
  Finite (KerModRange f g) ∧ Finite (KerModRange g f)

noncomputable def herbrandQuotient (f g : A →+ A) : ℚ :=
  (Nat.card (KerModRange f g) : ℚ) / Nat.card (KerModRange g f)

theorem range_le_ker {f g : A →+ A} (hfg : ∀ x, f (g x) = 0) : g.range ≤ f.ker := by
  intro y hy
  obtain ⟨x, rfl⟩ := AddMonoidHom.mem_range.1 hy
  exact AddMonoidHom.mem_ker.2 (hfg x)

theorem KerModRange.mk_eq_zero_iff {f g : A →+ A} (x : f.ker) :
    (QuotientAddGroup.mk x : KerModRange f g) = 0 ↔ (x : A) ∈ g.range := by
  rw [QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf]

theorem KerModRange.mk_eq_mk_iff {f g : A →+ A} (x y : f.ker) :
    (QuotientAddGroup.mk x : KerModRange f g) = QuotientAddGroup.mk y ↔
      (x : A) - y ∈ g.range := by
  rw [QuotientAddGroup.eq_iff_sub_mem, AddSubgroup.mem_addSubgroupOf, AddSubgroup.coe_sub]

theorem natCard_ker_eq {f g : A →+ A} (hfg : ∀ x, f (g x) = 0) :
    Nat.card f.ker = Nat.card (KerModRange f g) * Nat.card g.range := by
  have h1 := AddSubgroup.card_mul_index (g.range.addSubgroupOf f.ker)
  have h2 : Nat.card (g.range.addSubgroupOf f.ker) = Nat.card g.range :=
    Nat.card_congr (AddSubgroup.addSubgroupOfEquivOfLe (range_le_ker hfg)).toEquiv
  rw [← h1, h2, mul_comm]
  rfl

theorem hasHerbrandQuotient_of_finite [Finite A] (f g : A →+ A) : HasHerbrandQuotient f g :=
  ⟨inferInstance, inferInstance⟩

theorem natCard_kerModRange_eq_of_finite [Finite A] {f g : A →+ A} (hfg : ∀ x, f (g x) = 0)
    (hgf : ∀ x, g (f x) = 0) : Nat.card (KerModRange f g) = Nat.card (KerModRange g f) := by
  have h1 := natCard_ker_eq hfg
  have h2 := natCard_ker_eq hgf
  have h3 := natCard_eq_ker_mul_range f
  have h4 := natCard_eq_ker_mul_range g
  have hf : 0 < Nat.card f.range := Nat.card_pos
  have hg : 0 < Nat.card g.range := Nat.card_pos
  have key : Nat.card (KerModRange f g) * (Nat.card g.range * Nat.card f.range) =
      Nat.card (KerModRange g f) * (Nat.card g.range * Nat.card f.range) := by
    calc _ = Nat.card f.ker * Nat.card f.range := by rw [h1]; ring
      _ = Nat.card g.ker * Nat.card g.range := by rw [← h3, ← h4]
      _ = _ := by rw [h2]; ring
  exact Nat.eq_of_mul_eq_mul_right (Nat.mul_pos hg hf) key

theorem herbrandQuotient_eq_one_of_finite [Finite A] {f g : A →+ A} (hfg : ∀ x, f (g x) = 0)
    (hgf : ∀ x, g (f x) = 0) : herbrandQuotient f g = 1 := by
  have hq : 0 < Nat.card (KerModRange g f) := Nat.card_pos
  rw [herbrandQuotient, natCard_kerModRange_eq_of_finite hfg hgf, div_self]
  exact_mod_cast hq.ne'

end Defs

section Maps

variable {A B : Type*} [AddCommGroup A] [AddCommGroup B]

def kerMap {fA : A →+ A} {fB : B →+ B} (i : A →+ B) (hf : ∀ a, i (fA a) = fB (i a)) :
    fA.ker →+ fB.ker :=
  (i.comp fA.ker.subtype).codRestrict fB.ker fun a => by
    rw [AddMonoidHom.mem_ker, AddMonoidHom.comp_apply, AddSubgroup.coe_subtype, ← hf,
      AddMonoidHom.mem_ker.1 a.2, map_zero]

@[simp]
theorem kerMap_apply {fA : A →+ A} {fB : B →+ B} (i : A →+ B) (hf : ∀ a, i (fA a) = fB (i a))
    (a : fA.ker) : (kerMap i hf a : B) = i a :=
  rfl

def KerModRange.map {fA gA : A →+ A} {fB gB : B →+ B} (i : A →+ B)
    (hf : ∀ a, i (fA a) = fB (i a)) (hg : ∀ a, i (gA a) = gB (i a)) :
    KerModRange fA gA →+ KerModRange fB gB :=
  QuotientAddGroup.map _ _ (kerMap i hf) fun a ha => by
    rw [AddSubgroup.mem_comap, AddSubgroup.mem_addSubgroupOf, kerMap_apply]
    rw [AddSubgroup.mem_addSubgroupOf] at ha
    obtain ⟨x, hx⟩ := AddMonoidHom.mem_range.1 ha
    exact AddMonoidHom.mem_range.2 ⟨i x, by rw [← hg, hx]⟩

theorem KerModRange.map_mk {fA gA : A →+ A} {fB gB : B →+ B} (i : A →+ B)
    (hf : ∀ a, i (fA a) = fB (i a)) (hg : ∀ a, i (gA a) = gB (i a)) (a : fA.ker) :
    KerModRange.map i hf hg (QuotientAddGroup.mk a : KerModRange fA gA) =
      (QuotientAddGroup.mk (kerMap i hf a) : KerModRange fB gB) :=
  rfl

end Maps

section Hexagon

variable {A B C : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
  {fA gA : A →+ A} {fB gB : B →+ B} {fC gC : C →+ C} {i : A →+ B} {p : B →+ C}

theorem KerModRange.ker_map_eq_range_map (hi : Function.Injective i)
    (hp : Function.Surjective p) (hex : Function.Exact i p)
    (hfi : ∀ a, i (fA a) = fB (i a)) (hgi : ∀ a, i (gA a) = gB (i a))
    (hfp : ∀ b, p (fB b) = fC (p b)) (hgp : ∀ b, p (gB b) = gC (p b))
    (hfgB : ∀ b, fB (gB b) = 0) :
    (KerModRange.map p hfp hgp).ker = (KerModRange.map i hfi hgi).range := by
  ext x
  induction x using QuotientAddGroup.induction_on with
  | H z =>
  obtain ⟨b, hb⟩ := z
  rw [AddMonoidHom.mem_ker, KerModRange.map_mk, KerModRange.mk_eq_zero_iff, kerMap_apply,
    AddMonoidHom.mem_range]
  constructor
  · intro h
    obtain ⟨c, hc⟩ := AddMonoidHom.mem_range.1 h
    obtain ⟨b', rfl⟩ := hp c
    obtain ⟨a, ha⟩ : b - gB b' ∈ Set.range i :=
      (hex _).1 (by rw [map_sub, hgp, hc, sub_self])
    have hfa : fA a = 0 := hi (by
      rw [hfi, ha, map_sub, hfgB, AddMonoidHom.mem_ker.1 hb, sub_zero, map_zero])
    refine ⟨QuotientAddGroup.mk ⟨a, hfa⟩, ?_⟩
    rw [KerModRange.map_mk, KerModRange.mk_eq_mk_iff, kerMap_apply]
    exact AddMonoidHom.mem_range.2 ⟨-b', by rw [ha, map_neg]; abel⟩
  · rintro ⟨y, hy⟩
    induction y using QuotientAddGroup.induction_on with
    | H w =>
    obtain ⟨a, ha⟩ := w
    rw [KerModRange.map_mk, KerModRange.mk_eq_mk_iff, kerMap_apply] at hy
    obtain ⟨b'', hb''⟩ := AddMonoidHom.mem_range.1 hy
    have hpa : p (i a) = 0 := (hex _).2 ⟨a, rfl⟩
    refine AddMonoidHom.mem_range.2 ⟨-p b'', ?_⟩
    have : b = i a - gB b'' := by rw [hb'']; abel
    show gC (-p b'') = p b
    rw [this, map_sub, hpa, hgp, map_neg, zero_sub]

def connDomain (fB : B →+ B) (i : A →+ B) : AddSubgroup B :=
  i.range.comap fB

theorem connDomain_mem_ker (hex : Function.Exact i p) (hfp : ∀ b, p (fB b) = fC (p b))
    (s : connDomain fB i) : p s ∈ fC.ker := by
  have : p (fB s) = 0 := (hex _).2 (AddMonoidHom.mem_range.1 (AddSubgroup.mem_comap.1 s.2))
  rw [AddMonoidHom.mem_ker, ← hfp, this]

def connLeft (hex : Function.Exact i p) (hfp : ∀ b, p (fB b) = fC (p b)) :
    connDomain fB i →+ KerModRange fC gC :=
  (QuotientAddGroup.mk' _).comp <|
    (p.comp (connDomain fB i).subtype).codRestrict fC.ker (connDomain_mem_ker hex hfp)

theorem connLeft_apply (hex : Function.Exact i p) (hfp : ∀ b, p (fB b) = fC (p b))
    (s : connDomain fB i) :
    (connLeft hex hfp s : KerModRange fC gC) =
      QuotientAddGroup.mk (⟨p s, connDomain_mem_ker hex hfp s⟩ : fC.ker) :=
  rfl

noncomputable def connInv (hi : Function.Injective i) : connDomain fB i →+ A :=
  (AddMonoidHom.ofInjective hi).symm.toAddMonoidHom.comp <|
    (fB.comp (connDomain fB i).subtype).codRestrict i.range fun s => s.2

theorem apply_connInv (hi : Function.Injective i) (s : connDomain fB i) :
    i (connInv hi s) = fB s :=
  AddMonoidHom.apply_ofInjective_symm hi _

theorem connInv_mem_ker (hi : Function.Injective i) (hgi : ∀ a, i (gA a) = gB (i a))
    (hgfB : ∀ b, gB (fB b) = 0) (s : connDomain fB i) : connInv hi s ∈ gA.ker := by
  rw [AddMonoidHom.mem_ker]
  apply hi
  rw [hgi, apply_connInv, hgfB, map_zero]

noncomputable def connRight (hi : Function.Injective i) (hgi : ∀ a, i (gA a) = gB (i a))
    (hgfB : ∀ b, gB (fB b) = 0) : connDomain fB i →+ KerModRange gA fA :=
  (QuotientAddGroup.mk' _).comp <| (connInv hi).codRestrict gA.ker (connInv_mem_ker hi hgi hgfB)

theorem connRight_apply (hi : Function.Injective i) (hgi : ∀ a, i (gA a) = gB (i a))
    (hgfB : ∀ b, gB (fB b) = 0) (s : connDomain fB i) :
    (connRight hi hgi hgfB s : KerModRange gA fA) =
      QuotientAddGroup.mk (⟨connInv hi s, connInv_mem_ker hi hgi hgfB s⟩ : gA.ker) :=
  rfl

theorem connLeft_surjective (hp : Function.Surjective p) (hex : Function.Exact i p)
    (hfp : ∀ b, p (fB b) = fC (p b)) :
    Function.Surjective (connLeft hex hfp : connDomain fB i →+ KerModRange fC gC) := by
  intro y
  induction y using QuotientAddGroup.induction_on with
  | H z =>
  obtain ⟨c, hc⟩ := z
  obtain ⟨b, rfl⟩ := hp c
  have hb : b ∈ connDomain fB i :=
    AddSubgroup.mem_comap.2 (AddMonoidHom.mem_range.2
      ((hex _).1 (by rw [hfp]; exact AddMonoidHom.mem_ker.1 hc)))
  exact ⟨⟨b, hb⟩, rfl⟩

theorem ker_connLeft_le (hi : Function.Injective i) (hp : Function.Surjective p)
    (hex : Function.Exact i p) (hfi : ∀ a, i (fA a) = fB (i a))
    (hgi : ∀ a, i (gA a) = gB (i a)) (hfp : ∀ b, p (fB b) = fC (p b))
    (hgp : ∀ b, p (gB b) = gC (p b)) (hfgB : ∀ b, fB (gB b) = 0) (hgfB : ∀ b, gB (fB b) = 0) :
    (connLeft hex hfp : connDomain fB i →+ KerModRange fC gC).ker ≤
      (connRight hi hgi hgfB : connDomain fB i →+ KerModRange gA fA).ker := by
  intro s hs
  rw [AddMonoidHom.mem_ker, connLeft_apply, KerModRange.mk_eq_zero_iff] at hs
  rw [AddMonoidHom.mem_ker, connRight_apply, KerModRange.mk_eq_zero_iff]
  obtain ⟨c, hc⟩ := AddMonoidHom.mem_range.1 hs
  obtain ⟨b', rfl⟩ := hp c
  obtain ⟨a, ha⟩ : (s : B) - gB b' ∈ Set.range i :=
    (hex _).1 (by rw [map_sub, hgp, hc]; exact sub_self _)
  refine AddMonoidHom.mem_range.2 ⟨a, hi ?_⟩
  rw [hfi, ha, apply_connInv, map_sub, hfgB, sub_zero]

noncomputable def connecting (hi : Function.Injective i) (hp : Function.Surjective p)
    (hex : Function.Exact i p) (hfi : ∀ a, i (fA a) = fB (i a))
    (hgi : ∀ a, i (gA a) = gB (i a)) (hfp : ∀ b, p (fB b) = fC (p b))
    (hgp : ∀ b, p (gB b) = gC (p b)) (hfgB : ∀ b, fB (gB b) = 0) (hgfB : ∀ b, gB (fB b) = 0) :
    KerModRange fC gC →+ KerModRange gA fA :=
  (QuotientAddGroup.lift _ (connRight hi hgi hgfB : connDomain fB i →+ KerModRange gA fA)
      (ker_connLeft_le hi hp hex hfi hgi hfp hgp hfgB hgfB)).comp
    (QuotientAddGroup.quotientKerEquivOfSurjective _
      (connLeft_surjective hp hex hfp)).symm.toAddMonoidHom

theorem connecting_connLeft (hi : Function.Injective i) (hp : Function.Surjective p)
    (hex : Function.Exact i p) (hfi : ∀ a, i (fA a) = fB (i a))
    (hgi : ∀ a, i (gA a) = gB (i a)) (hfp : ∀ b, p (fB b) = fC (p b))
    (hgp : ∀ b, p (gB b) = gC (p b)) (hfgB : ∀ b, fB (gB b) = 0) (hgfB : ∀ b, gB (fB b) = 0)
    (s : connDomain fB i) :
    connecting hi hp hex hfi hgi hfp hgp hfgB hgfB (connLeft hex hfp s) =
      (connRight hi hgi hgfB s : KerModRange gA fA) := by
  have : (QuotientAddGroup.quotientKerEquivOfSurjective _
      (connLeft_surjective hp hex hfp)).symm (connLeft hex hfp s : KerModRange fC gC) =
      (QuotientAddGroup.mk s : connDomain fB i ⧸ (connLeft hex hfp :
        connDomain fB i →+ KerModRange fC gC).ker) :=
    (AddEquiv.symm_apply_eq _).2 rfl
  rw [connecting, AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom, this,
    QuotientAddGroup.lift_mk]

theorem ker_connecting (hi : Function.Injective i) (hp : Function.Surjective p)
    (hex : Function.Exact i p) (hfi : ∀ a, i (fA a) = fB (i a))
    (hgi : ∀ a, i (gA a) = gB (i a)) (hfp : ∀ b, p (fB b) = fC (p b))
    (hgp : ∀ b, p (gB b) = gC (p b)) (hfgB : ∀ b, fB (gB b) = 0) (hgfB : ∀ b, gB (fB b) = 0) :
    (connecting hi hp hex hfi hgi hfp hgp hfgB hgfB).ker = (KerModRange.map p hfp hgp).range := by
  ext y
  constructor
  · intro hy
    obtain ⟨s, rfl⟩ := connLeft_surjective hp hex hfp y
    rw [AddMonoidHom.mem_ker, connecting_connLeft, connRight_apply,
      KerModRange.mk_eq_zero_iff] at hy
    obtain ⟨a, ha⟩ := AddMonoidHom.mem_range.1 hy
    have hk : (s : B) - i a ∈ fB.ker := by
      rw [AddMonoidHom.mem_ker, map_sub, ← hfi, ha, apply_connInv, sub_self]
    refine ⟨QuotientAddGroup.mk ⟨_, hk⟩, ?_⟩
    rw [KerModRange.map_mk, connLeft_apply, KerModRange.mk_eq_mk_iff, kerMap_apply]
    have hpa : p (i a) = 0 := (hex _).2 ⟨a, rfl⟩
    rw [map_sub, hpa, sub_zero, sub_self]
    exact zero_mem _
  · rintro ⟨x, rfl⟩
    induction x using QuotientAddGroup.induction_on with
    | H z =>
    obtain ⟨b, hb⟩ := z
    have hb' : b ∈ connDomain fB i := by
      refine AddSubgroup.mem_comap.2 ?_
      rw [AddMonoidHom.mem_ker.1 hb]
      exact zero_mem _
    have h1 : KerModRange.map p hfp hgp (QuotientAddGroup.mk ⟨b, hb⟩ : KerModRange fB gB) =
        connLeft hex hfp ⟨b, hb'⟩ := rfl
    have h2 : connInv hi ⟨b, hb'⟩ = 0 :=
      hi (by rw [apply_connInv, map_zero]; exact AddMonoidHom.mem_ker.1 hb)
    rw [AddMonoidHom.mem_ker, h1, connecting_connLeft, connRight_apply,
      KerModRange.mk_eq_zero_iff]
    simp only [h2]
    exact zero_mem _

theorem range_connecting (hi : Function.Injective i) (hp : Function.Surjective p)
    (hex : Function.Exact i p) (hfi : ∀ a, i (fA a) = fB (i a))
    (hgi : ∀ a, i (gA a) = gB (i a)) (hfp : ∀ b, p (fB b) = fC (p b))
    (hgp : ∀ b, p (gB b) = gC (p b)) (hfgB : ∀ b, fB (gB b) = 0) (hgfB : ∀ b, gB (fB b) = 0) :
    (connecting hi hp hex hfi hgi hfp hgp hfgB hgfB).range = (KerModRange.map i hgi hfi).ker := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    obtain ⟨s, rfl⟩ := connLeft_surjective hp hex hfp y
    rw [AddMonoidHom.mem_ker, connecting_connLeft, connRight_apply, KerModRange.map_mk,
      KerModRange.mk_eq_zero_iff, kerMap_apply, apply_connInv]
    exact AddMonoidHom.mem_range.2 ⟨s, rfl⟩
  · intro hx
    induction x using QuotientAddGroup.induction_on with
    | H z =>
    obtain ⟨a, ha⟩ := z
    rw [AddMonoidHom.mem_ker, KerModRange.map_mk, KerModRange.mk_eq_zero_iff,
      kerMap_apply] at hx
    obtain ⟨b, hb⟩ := AddMonoidHom.mem_range.1 hx
    have hb' : b ∈ connDomain fB i := by
      refine AddSubgroup.mem_comap.2 ?_
      rw [hb]
      exact AddMonoidHom.mem_range.2 ⟨a, rfl⟩
    refine ⟨connLeft hex hfp ⟨b, hb'⟩, ?_⟩
    rw [connecting_connLeft, connRight_apply]
    have : connInv hi ⟨b, hb'⟩ = a := hi (by rw [apply_connInv]; exact hb)
    congr 1
    exact Subtype.ext this

end Hexagon

section ShortExact

variable {A B C : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
  {fA gA : A →+ A} {fB gB : B →+ B} {fC gC : C →+ C} {i : A →+ B} {p : B →+ C}

theorem natCard_kerModRange_hexagon (hi : Function.Injective i) (hp : Function.Surjective p)
    (hex : Function.Exact i p) (hfi : ∀ a, i (fA a) = fB (i a))
    (hgi : ∀ a, i (gA a) = gB (i a)) (hfp : ∀ b, p (fB b) = fC (p b))
    (hgp : ∀ b, p (gB b) = gC (p b)) (hfgB : ∀ b, fB (gB b) = 0) (hgfB : ∀ b, gB (fB b) = 0) :
    Nat.card (KerModRange fA gA) * Nat.card (KerModRange fC gC) * Nat.card (KerModRange gB fB) =
      Nat.card (KerModRange fB gB) * Nat.card (KerModRange gA fA) *
        Nat.card (KerModRange gC fC) :=
  natCard_hexagon (KerModRange.map i hfi hgi) (KerModRange.map p hfp hgp)
    (connecting hi hp hex hfi hgi hfp hgp hfgB hgfB) (KerModRange.map i hgi hfi)
    (KerModRange.map p hgp hfp) (connecting hi hp hex hgi hfi hgp hfp hgfB hfgB)
    (range_connecting hi hp hex hgi hfi hgp hfp hgfB hfgB).symm
    (KerModRange.ker_map_eq_range_map hi hp hex hfi hgi hfp hgp hfgB)
    (ker_connecting hi hp hex hfi hgi hfp hgp hfgB hgfB)
    (range_connecting hi hp hex hfi hgi hfp hgp hfgB hgfB).symm
    (KerModRange.ker_map_eq_range_map hi hp hex hgi hfi hgp hfp hgfB)
    (ker_connecting hi hp hex hgi hfi hgp hfp hgfB hfgB)

theorem HasHerbrandQuotient.of_shortExact_left_right (hi : Function.Injective i)
    (hp : Function.Surjective p) (hex : Function.Exact i p) (hfi : ∀ a, i (fA a) = fB (i a))
    (hgi : ∀ a, i (gA a) = gB (i a)) (hfp : ∀ b, p (fB b) = fC (p b))
    (hgp : ∀ b, p (gB b) = gC (p b)) (hfgB : ∀ b, fB (gB b) = 0) (hgfB : ∀ b, gB (fB b) = 0)
    (hA : HasHerbrandQuotient fA gA) (hC : HasHerbrandQuotient fC gC) :
    HasHerbrandQuotient fB gB := by
  have := hA.1; have := hA.2; have := hC.1; have := hC.2
  exact ⟨finite_of_exact (KerModRange.map i hfi hgi) (KerModRange.map p hfp hgp)
      (KerModRange.ker_map_eq_range_map hi hp hex hfi hgi hfp hgp hfgB),
    finite_of_exact (KerModRange.map i hgi hfi) (KerModRange.map p hgp hfp)
      (KerModRange.ker_map_eq_range_map hi hp hex hgi hfi hgp hfp hgfB)⟩

theorem HasHerbrandQuotient.of_shortExact_left_mid (hi : Function.Injective i)
    (hp : Function.Surjective p) (hex : Function.Exact i p) (hfi : ∀ a, i (fA a) = fB (i a))
    (hgi : ∀ a, i (gA a) = gB (i a)) (hfp : ∀ b, p (fB b) = fC (p b))
    (hgp : ∀ b, p (gB b) = gC (p b)) (hfgB : ∀ b, fB (gB b) = 0) (hgfB : ∀ b, gB (fB b) = 0)
    (hA : HasHerbrandQuotient fA gA) (hB : HasHerbrandQuotient fB gB) :
    HasHerbrandQuotient fC gC := by
  have := hA.1; have := hA.2; have := hB.1; have := hB.2
  exact ⟨finite_of_exact (KerModRange.map p hfp hgp) (connecting hi hp hex hfi hgi hfp hgp hfgB hgfB)
      (ker_connecting hi hp hex hfi hgi hfp hgp hfgB hgfB),
    finite_of_exact (KerModRange.map p hgp hfp) (connecting hi hp hex hgi hfi hgp hfp hgfB hfgB)
      (ker_connecting hi hp hex hgi hfi hgp hfp hgfB hfgB)⟩

theorem HasHerbrandQuotient.of_shortExact_mid_right (hi : Function.Injective i)
    (hp : Function.Surjective p) (hex : Function.Exact i p) (hfi : ∀ a, i (fA a) = fB (i a))
    (hgi : ∀ a, i (gA a) = gB (i a)) (hfp : ∀ b, p (fB b) = fC (p b))
    (hgp : ∀ b, p (gB b) = gC (p b)) (hfgB : ∀ b, fB (gB b) = 0) (hgfB : ∀ b, gB (fB b) = 0)
    (hB : HasHerbrandQuotient fB gB) (hC : HasHerbrandQuotient fC gC) :
    HasHerbrandQuotient fA gA := by
  have := hB.1; have := hB.2; have := hC.1; have := hC.2
  exact ⟨finite_of_exact (connecting hi hp hex hgi hfi hgp hfp hgfB hfgB) (KerModRange.map i hfi hgi)
      (range_connecting hi hp hex hgi hfi hgp hfp hgfB hfgB).symm,
    finite_of_exact (connecting hi hp hex hfi hgi hfp hgp hfgB hgfB) (KerModRange.map i hgi hfi)
      (range_connecting hi hp hex hfi hgi hfp hgp hfgB hgfB).symm⟩

theorem herbrandQuotient_eq_mul_of_shortExact (hi : Function.Injective i)
    (hp : Function.Surjective p) (hex : Function.Exact i p) (hfi : ∀ a, i (fA a) = fB (i a))
    (hgi : ∀ a, i (gA a) = gB (i a)) (hfp : ∀ b, p (fB b) = fC (p b))
    (hgp : ∀ b, p (gB b) = gC (p b)) (hfgB : ∀ b, fB (gB b) = 0) (hgfB : ∀ b, gB (fB b) = 0)
    (hA : HasHerbrandQuotient fA gA) (hC : HasHerbrandQuotient fC gC) :
    herbrandQuotient fB gB = herbrandQuotient fA gA * herbrandQuotient fC gC := by
  have hB := HasHerbrandQuotient.of_shortExact_left_right hi hp hex hfi hgi hfp hgp hfgB hgfB hA hC
  have h := natCard_kerModRange_hexagon hi hp hex hfi hgi hfp hgp hfgB hgfB
  have := hA.2; have := hB.2; have := hC.2
  have h4 : (Nat.card (KerModRange gA fA) : ℚ) ≠ 0 := by exact_mod_cast Nat.card_pos.ne'
  have h5 : (Nat.card (KerModRange gB fB) : ℚ) ≠ 0 := by exact_mod_cast Nat.card_pos.ne'
  have h6 : (Nat.card (KerModRange gC fC) : ℚ) ≠ 0 := by exact_mod_cast Nat.card_pos.ne'
  have h' : (Nat.card (KerModRange fA gA) : ℚ) * Nat.card (KerModRange fC gC) *
      Nat.card (KerModRange gB fB) = (Nat.card (KerModRange fB gB) : ℚ) *
        Nat.card (KerModRange gA fA) * Nat.card (KerModRange gC fC) := by
    exact_mod_cast h
  rw [herbrandQuotient, herbrandQuotient, herbrandQuotient, div_mul_div_comm,
    div_eq_div_iff h5 (mul_ne_zero h4 h6)]
  linear_combination -h'

theorem hasHerbrandQuotient_iff_of_shortExact_of_finite [Finite C] (hi : Function.Injective i)
    (hp : Function.Surjective p) (hex : Function.Exact i p) (hfi : ∀ a, i (fA a) = fB (i a))
    (hgi : ∀ a, i (gA a) = gB (i a)) (hfp : ∀ b, p (fB b) = fC (p b))
    (hgp : ∀ b, p (gB b) = gC (p b)) (hfgB : ∀ b, fB (gB b) = 0) (hgfB : ∀ b, gB (fB b) = 0) :
    HasHerbrandQuotient fA gA ↔ HasHerbrandQuotient fB gB :=
  ⟨fun hA => HasHerbrandQuotient.of_shortExact_left_right hi hp hex hfi hgi hfp hgp hfgB hgfB hA
      (hasHerbrandQuotient_of_finite _ _),
    fun hB => HasHerbrandQuotient.of_shortExact_mid_right hi hp hex hfi hgi hfp hgp hfgB hgfB hB
      (hasHerbrandQuotient_of_finite _ _)⟩

theorem herbrandQuotient_eq_of_shortExact_of_finite [Finite C] (hi : Function.Injective i)
    (hp : Function.Surjective p) (hex : Function.Exact i p) (hfi : ∀ a, i (fA a) = fB (i a))
    (hgi : ∀ a, i (gA a) = gB (i a)) (hfp : ∀ b, p (fB b) = fC (p b))
    (hgp : ∀ b, p (gB b) = gC (p b)) (hfgB : ∀ b, fB (gB b) = 0) (hgfB : ∀ b, gB (fB b) = 0) :
    herbrandQuotient fA gA = herbrandQuotient fB gB := by
  have hfgC : ∀ c, fC (gC c) = 0 := by
    intro c
    obtain ⟨b, rfl⟩ := hp c
    rw [← hgp, ← hfp, hfgB, map_zero]
  have hgfC : ∀ c, gC (fC c) = 0 := by
    intro c
    obtain ⟨b, rfl⟩ := hp c
    rw [← hfp, ← hgp, hgfB, map_zero]
  have h := natCard_kerModRange_hexagon hi hp hex hfi hgi hfp hgp hfgB hgfB
  rw [natCard_kerModRange_eq_of_finite hfgC hgfC] at h
  have h3 : 0 < Nat.card (KerModRange gC fC) := Nat.card_pos
  have h15 : Nat.card (KerModRange fA gA) * Nat.card (KerModRange gB fB) =
      Nat.card (KerModRange fB gB) * Nat.card (KerModRange gA fA) := by
    apply Nat.eq_of_mul_eq_mul_right h3
    calc _ = Nat.card (KerModRange fA gA) * Nat.card (KerModRange gC fC) *
          Nat.card (KerModRange gB fB) := by ring
      _ = _ := h
  by_cases h4 : Finite (KerModRange gA fA)
  · have h5 : Finite (KerModRange gB fB) :=
      finite_of_exact (KerModRange.map i hgi hfi) (KerModRange.map p hgp hfp)
        (KerModRange.ker_map_eq_range_map hi hp hex hgi hfi hgp hfp hgfB)
    have h4' : (Nat.card (KerModRange gA fA) : ℚ) ≠ 0 := by exact_mod_cast Nat.card_pos.ne'
    have h5' : (Nat.card (KerModRange gB fB) : ℚ) ≠ 0 := by exact_mod_cast Nat.card_pos.ne'
    rw [herbrandQuotient, herbrandQuotient, div_eq_div_iff h4' h5']
    exact_mod_cast h15
  · have h5 : ¬ Finite (KerModRange gB fB) := fun h5 =>
      h4 (finite_of_exact (connecting hi hp hex hfi hgi hfp hgp hfgB hgfB)
        (KerModRange.map i hgi hfi) (range_connecting hi hp hex hfi hgi hfp hgp hfgB hgfB).symm)
    rw [not_finite_iff_infinite] at h4 h5
    rw [herbrandQuotient, herbrandQuotient, Nat.card_eq_zero_of_infinite (α := KerModRange gA fA),
      Nat.card_eq_zero_of_infinite (α := KerModRange gB fB)]
    simp

end ShortExact

section FiniteIndex

variable {A B : Type*} [AddCommGroup A] [AddCommGroup B]

theorem hasHerbrandQuotient_iff_of_injective_of_finite {fA gA : A →+ A} {fB gB : B →+ B}
    {i : A →+ B} (hi : Function.Injective i) [Finite (B ⧸ i.range)]
    (hfi : ∀ a, i (fA a) = fB (i a)) (hgi : ∀ a, i (gA a) = gB (i a))
    (hfgB : ∀ b, fB (gB b) = 0) (hgfB : ∀ b, gB (fB b) = 0) :
    HasHerbrandQuotient fA gA ↔ HasHerbrandQuotient fB gB := by
  have hf : i.range ≤ i.range.comap fB := by
    rintro _ ⟨a, rfl⟩
    exact AddSubgroup.mem_comap.2 (AddMonoidHom.mem_range.2 ⟨fA a, hfi a⟩)
  have hg : i.range ≤ i.range.comap gB := by
    rintro _ ⟨a, rfl⟩
    exact AddSubgroup.mem_comap.2 (AddMonoidHom.mem_range.2 ⟨gA a, hgi a⟩)
  refine hasHerbrandQuotient_iff_of_shortExact_of_finite (p := QuotientAddGroup.mk' i.range)
    (fC := QuotientAddGroup.map _ _ fB hf) (gC := QuotientAddGroup.map _ _ gB hg) hi
    (QuotientAddGroup.mk'_surjective _) ?_ hfi hgi (fun _ => rfl) (fun _ => rfl) hfgB hgfB
  intro b
  rw [QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff, AddMonoidHom.mem_range,
    Set.mem_range]

theorem herbrandQuotient_eq_of_injective_of_finite {fA gA : A →+ A} {fB gB : B →+ B}
    {i : A →+ B} (hi : Function.Injective i) [Finite (B ⧸ i.range)]
    (hfi : ∀ a, i (fA a) = fB (i a)) (hgi : ∀ a, i (gA a) = gB (i a))
    (hfgB : ∀ b, fB (gB b) = 0) (hgfB : ∀ b, gB (fB b) = 0) :
    herbrandQuotient fA gA = herbrandQuotient fB gB := by
  have hf : i.range ≤ i.range.comap fB := by
    rintro _ ⟨a, rfl⟩
    exact AddSubgroup.mem_comap.2 (AddMonoidHom.mem_range.2 ⟨fA a, hfi a⟩)
  have hg : i.range ≤ i.range.comap gB := by
    rintro _ ⟨a, rfl⟩
    exact AddSubgroup.mem_comap.2 (AddMonoidHom.mem_range.2 ⟨gA a, hgi a⟩)
  refine herbrandQuotient_eq_of_shortExact_of_finite (p := QuotientAddGroup.mk' i.range)
    (fC := QuotientAddGroup.map _ _ fB hf) (gC := QuotientAddGroup.map _ _ gB hg) hi
    (QuotientAddGroup.mk'_surjective _) ?_ hfi hgi (fun _ => rfl) (fun _ => rfl) hfgB hgfB
  intro b
  rw [QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff, AddMonoidHom.mem_range,
    Set.mem_range]

def restrictEnd (f : B →+ B) (S : AddSubgroup B) (hS : ∀ x ∈ S, f x ∈ S) : S →+ S :=
  (f.comp S.subtype).codRestrict S fun x => hS x x.2

@[simp]
theorem restrictEnd_apply (f : B →+ B) (S : AddSubgroup B) (hS : ∀ x ∈ S, f x ∈ S) (x : S) :
    (restrictEnd f S hS x : B) = f x :=
  rfl

theorem hasHerbrandQuotient_restrictEnd_iff {f g : B →+ B} (S : AddSubgroup B) [S.FiniteIndex]
    (hfS : ∀ x ∈ S, f x ∈ S) (hgS : ∀ x ∈ S, g x ∈ S) (hfg : ∀ b, f (g b) = 0)
    (hgf : ∀ b, g (f b) = 0) :
    HasHerbrandQuotient (restrictEnd f S hfS) (restrictEnd g S hgS) ↔ HasHerbrandQuotient f g := by
  have : Finite (B ⧸ S.subtype.range) := by rw [AddSubgroup.range_subtype]; infer_instance
  exact hasHerbrandQuotient_iff_of_injective_of_finite S.subtype_injective (fun _ => rfl)
    (fun _ => rfl) hfg hgf

theorem herbrandQuotient_restrictEnd {f g : B →+ B} (S : AddSubgroup B) [S.FiniteIndex]
    (hfS : ∀ x ∈ S, f x ∈ S) (hgS : ∀ x ∈ S, g x ∈ S) (hfg : ∀ b, f (g b) = 0)
    (hgf : ∀ b, g (f b) = 0) :
    herbrandQuotient (restrictEnd f S hfS) (restrictEnd g S hgS) = herbrandQuotient f g := by
  have : Finite (B ⧸ S.subtype.range) := by rw [AddSubgroup.range_subtype]; infer_instance
  exact herbrandQuotient_eq_of_injective_of_finite S.subtype_injective (fun _ => rfl)
    (fun _ => rfl) hfg hgf

end FiniteIndex

end GroundTheory.GroupCoh
