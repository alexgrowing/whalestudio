import ReciprocityTheory.ClassFieldTheory.LocalClassField.HerbrandA

namespace ReciprocityTheory.DiscreteGroups.LocalClassField.Herbrand

open Function

section Abstract

variable {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    {DA NA : A →+ A} {DB NB : B →+ B} {f : A →+ B}

def cokerMap (f : A →+ B) (fD : ∀ a, f (DA a) = DB (f a)) : B ⧸ f.range →+ B ⧸ f.range :=
  QuotientAddGroup.map _ _ DB (by
    rintro _ ⟨a, rfl⟩
    exact ⟨DA a, fD a⟩)

theorem ses_coker (hf : Injective f)
    (fD : ∀ a, f (DA a) = DB (f a)) (fN : ∀ a, f (NA a) = NB (f a))
    (DN : ∀ b, DB (NB b) = 0) (ND : ∀ b, NB (DB b) = 0) :
    SES DA NA DB NB (cokerMap f fD) (cokerMap f fN) f (QuotientAddGroup.mk' f.range) where
  inj := hf
  exact := fun b => by
    rw [QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff]; rfl
  surj := QuotientAddGroup.mk'_surjective _
  fD := fD
  fN := fN
  gD := fun _ => rfl
  gN := fun _ => rfl
  DN := DN
  ND := ND

theorem isFin_iff_of_finiteIndex (hf : Injective f) (hfi : f.range.FiniteIndex)
    (fD : ∀ a, f (DA a) = DB (f a)) (fN : ∀ a, f (NA a) = NB (f a))
    (DN : ∀ b, DB (NB b) = 0) (ND : ∀ b, NB (DB b) = 0) : IsFin DA NA ↔ IsFin DB NB :=
  ⟨fun hA => isFin_mid (ses_coker hf fD fN DN ND) hA (isFin_of_finite _ _),
    fun hB => isFin_left (ses_coker hf fD fN DN ND) hB (isFin_of_finite _ _)⟩

theorem q_eq_of_finiteIndex (hf : Injective f) (hfi : f.range.FiniteIndex)
    (fD : ∀ a, f (DA a) = DB (f a)) (fN : ∀ a, f (NA a) = NB (f a))
    (DN : ∀ b, DB (NB b) = 0) (ND : ∀ b, NB (DB b) = 0) (hA : IsFin DA NA) :
    q DA NA = q DB NB := by
  have h := ses_coker hf fD fN DN ND
  rw [q_mul h hA (isFin_of_finite _ _), q_of_finite _ _ h.DN_C h.swap.DN_C, mul_one]

end Abstract

section Cyclic

variable {k G M : Type*} [CommRing k] [Group G] [Fintype G] [AddCommGroup M] [Module k M]

def dHom (ρ : Representation k G M) (g : G) : M →+ M := (ρ g - 1 : Module.End k M).toAddMonoidHom

def nHom (ρ : Representation k G M) : M →+ M := (ρ.norm : Module.End k M).toAddMonoidHom

@[simp] theorem dHom_apply (ρ : Representation k G M) (g : G) (x : M) : dHom ρ g x = ρ g x - x := rfl

theorem nHom_apply (ρ : Representation k G M) (x : M) : nHom ρ x = ∑ c : G, ρ c x := by
  change ρ.norm x = _
  simp [Representation.norm]

theorem dHom_nHom (ρ : Representation k G M) (g : G) (x : M) : dHom ρ g (nHom ρ x) = 0 := by
  change ρ g (ρ.norm x) - ρ.norm x = 0
  rw [Representation.self_norm_apply, sub_self]

theorem nHom_dHom (ρ : Representation k G M) (g : G) (x : M) : nHom ρ (dHom ρ g x) = 0 := by
  change ρ.norm (ρ g x - x) = 0
  rw [map_sub, Representation.norm_self_apply, sub_self]

theorem mem_ker_dHom_iff (ρ : Representation k G M) (g : G) (hg : ∀ x, x ∈ Subgroup.zpowers g) (x : M) :
    x ∈ (dHom ρ g).ker ↔ ∀ c : G, ρ c x = x := by
  rw [AddMonoidHom.mem_ker, dHom_apply, sub_eq_zero,
    ← Representation.mem_invariants_iff_of_forall_mem_zpowers ρ g hg x]
  rfl

abbrev TateZerothCohomology (ρ : Representation k G M) (g : G) : Type _ := T (dHom ρ g) (nHom ρ)

abbrev H1 (ρ : Representation k G M) (g : G) : Type _ := T (nHom ρ) (dHom ρ g)

def HFin (ρ : Representation k G M) (g : G) : Prop := IsFin (dHom ρ g) (nHom ρ)

noncomputable def h (ρ : Representation k G M) (g : G) : ℚ := q (dHom ρ g) (nHom ρ)

theorem h_eq (ρ : Representation k G M) (g : G) :
    h ρ g = (Nat.card (TateZerothCohomology ρ g) : ℚ) / (Nat.card (H1 ρ g) : ℚ) := rfl

variable {A B C : Type*} [AddCommGroup A] [Module k A] [AddCommGroup B] [Module k B]
  [AddCommGroup C] [Module k C]

theorem map_dHom (ρA : Representation k G A) (ρB : Representation k G B) (g : G) (i : A →+ B)
    (hiG : ∀ c a, i (ρA c a) = ρB c (i a)) (a : A) : i (dHom ρA g a) = dHom ρB g (i a) := by
  rw [dHom_apply, dHom_apply, map_sub, hiG]

theorem map_nHom (ρA : Representation k G A) (ρB : Representation k G B) (i : A →+ B)
    (hiG : ∀ c a, i (ρA c a) = ρB c (i a)) (a : A) : i (nHom ρA a) = nHom ρB (i a) := by
  rw [nHom_apply, nHom_apply, map_sum]
  exact Finset.sum_congr rfl fun c _ => hiG c a

theorem ses_of_rep (ρA : Representation k G A) (ρB : Representation k G B) (ρC : Representation k G C)
    (g : G) (i : A →+ B) (p : B →+ C) (hi : Injective i) (hip : Function.Exact i p) (hp : Surjective p)
    (hiG : ∀ c a, i (ρA c a) = ρB c (i a)) (hpG : ∀ c b, p (ρB c b) = ρC c (p b)) :
    SES (dHom ρA g) (nHom ρA) (dHom ρB g) (nHom ρB) (dHom ρC g) (nHom ρC) i p :=
  ⟨hi, hip, hp, map_dHom ρA ρB g i hiG, map_nHom ρA ρB i hiG, map_dHom ρB ρC g p hpG,
    map_nHom ρB ρC p hpG, dHom_nHom ρB g, nHom_dHom ρB g⟩

theorem h_mul (ρA : Representation k G A) (ρB : Representation k G B) (ρC : Representation k G C)
    (g : G) (i : A →+ B) (p : B →+ C) (hi : Injective i) (hip : Function.Exact i p) (hp : Surjective p)
    (hiG : ∀ c a, i (ρA c a) = ρB c (i a)) (hpG : ∀ c b, p (ρB c b) = ρC c (p b))
    (hA : HFin ρA g) (hC : HFin ρC g) : HFin ρB g ∧ h ρB g = h ρA g * h ρC g :=
  have hs := ses_of_rep ρA ρB ρC g i p hi hip hp hiG hpG
  ⟨isFin_mid hs hA hC, q_mul hs hA hC⟩

theorem h_eq_of_finiteIndex (ρA : Representation k G A) (ρB : Representation k G B) (g : G) (i : A →+ B)
    (hi : Injective i) (hfi : i.range.FiniteIndex) (hiG : ∀ c a, i (ρA c a) = ρB c (i a)) :
    (HFin ρA g ↔ HFin ρB g) ∧ (HFin ρA g → h ρA g = h ρB g) :=
  ⟨isFin_iff_of_finiteIndex hi hfi (map_dHom ρA ρB g i hiG) (map_nHom ρA ρB i hiG) (dHom_nHom ρB g)
      (nHom_dHom ρB g),
    q_eq_of_finiteIndex hi hfi (map_dHom ρA ρB g i hiG) (map_nHom ρA ρB i hiG) (dHom_nHom ρB g)
      (nHom_dHom ρB g)⟩

theorem h_of_subsingleton (ρ : Representation k G M) (g : G) [Subsingleton (TateZerothCohomology ρ g)]
    [Subsingleton (H1 ρ g)] : HFin ρ g ∧ h ρ g = 1 := by
  refine ⟨⟨inferInstance, inferInstance⟩, ?_⟩
  rw [h_eq, Nat.card_of_subsingleton (0 : TateZerothCohomology ρ g), Nat.card_of_subsingleton (0 : H1 ρ g)]
  norm_num

theorem h_eq_card_H0hat (ρ : Representation k G M) (g : G) [Subsingleton (H1 ρ g)] :
    h ρ g = Nat.card (TateZerothCohomology ρ g) := by
  rw [h_eq, Nat.card_of_subsingleton (0 : H1 ρ g)]
  norm_num

theorem h_int (ρ : Representation ℤ G ℤ) (hρ : ∀ c x, ρ c x = x) (g : G) :
    HFin ρ g ∧ Nat.card (TateZerothCohomology ρ g) = Nat.card G ∧ Subsingleton (H1 ρ g) ∧ h ρ g = Nat.card G := by
  have hpos : 0 < Nat.card G := Nat.card_pos
  have hD : (dHom ρ g).ker = ⊤ := by
    ext x; simp [AddMonoidHom.mem_ker, hρ]
  have hNx : ∀ x, nHom ρ x = (Nat.card G : ℤ) * x := fun x => by
    rw [nHom_apply]; simp [hρ]
  have hN : (nHom ρ).range = AddSubgroup.zmultiples (Nat.card G : ℤ) := by
    ext x
    rw [Int.mem_zmultiples_iff]
    constructor
    · rintro ⟨y, rfl⟩; exact ⟨y, hNx y⟩
    · rintro ⟨y, rfl⟩; exact ⟨y, hNx y⟩
  have h0 : Nat.card (TateZerothCohomology ρ g) = Nat.card G := by
    change ((nHom ρ).range.addSubgroupOf (dHom ρ g).ker).index = _
    change (nHom ρ).range.relIndex (dHom ρ g).ker = _
    rw [hD, AddSubgroup.relIndex_top_right, hN, Int.index_zmultiples]
    simp
  have h1 : Subsingleton (H1 ρ g) := by
    have : Subsingleton (nHom ρ).ker := ⟨fun x y => by
      have hx : nHom ρ x = 0 := x.2
      have hy : nHom ρ y = 0 := y.2
      rw [hNx] at hx hy
      apply Subtype.ext
      have hne : (Nat.card G : ℤ) ≠ 0 := by exact_mod_cast hpos.ne'
      rw [(mul_eq_zero.1 hx).resolve_left hne, (mul_eq_zero.1 hy).resolve_left hne]⟩
    exact (QuotientAddGroup.mk_surjective).subsingleton
  refine ⟨⟨Nat.finite_of_card_ne_zero (by rw [h0]; exact hpos.ne'), inferInstance⟩, h0, h1, ?_⟩
  rw [h_eq_card_H0hat, h0]

end Cyclic

end ReciprocityTheory.DiscreteGroups.LocalClassField.Herbrand
