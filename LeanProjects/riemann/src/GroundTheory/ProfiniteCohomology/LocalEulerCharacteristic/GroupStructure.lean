import Mathlib
import GroundTheory.ProfiniteCohomology.LocalEulerCharacteristic.GroupStructureDefs
import GroundTheory.LocalFields.RamificationStructure
import GroundTheory.LocalFields.UnramifiedRootsOfUnity
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

section Parts

variable {Q Q' : Type*} [Group Q] [Group Q']

theorem map_coprimePart_le (p : ℕ) (f : Q →* Q') :
    (coprimePart p Q).map f ≤ coprimePart p Q' := by
  rw [coprimePart, MonoidHom.map_closure, Subgroup.closure_le]
  rintro _ ⟨x, hx, rfl⟩
  exact Subgroup.subset_closure (Nat.Coprime.coprime_dvd_left (orderOf_map_dvd f x) hx)

instance coprimePart_normal (p : ℕ) : (coprimePart p Q).Normal where
  conj_mem x hx g := by
    simpa using map_coprimePart_le p (MulAut.conj g).toMonoidHom (Subgroup.mem_map_of_mem _ hx)

instance primaryPart_normal (p : ℕ) : (primaryPart p Q).Normal where
  conj_mem x hx g := by
    have h : (primaryPart p Q).map (MulAut.conj g).toMonoidHom ≤ primaryPart p Q := by
      rw [primaryPart, MonoidHom.map_closure, Subgroup.closure_le]
      rintro _ ⟨y, ⟨n, hy⟩, rfl⟩
      exact Subgroup.subset_closure ⟨n, by rw [MulEquiv.coe_toMonoidHom, MulEquiv.orderOf_eq, hy]⟩
    simpa using h (Subgroup.mem_map_of_mem _ hx)

theorem mem_coprimePart_iff_of_comm {p : ℕ} (hQ : ∀ a b : Q, a * b = b * a) {x : Q} :
    x ∈ coprimePart p Q ↔ (orderOf x).Coprime p := by
  let S : Subgroup Q :=
    { carrier := {x | (orderOf x).Coprime p}
      one_mem' := by simp
      mul_mem' := fun {a b} ha hb ↦
        Nat.Coprime.coprime_dvd_left ((Commute.orderOf_mul_dvd_lcm (hQ a b)).trans
          (Nat.lcm_dvd_mul _ _)) (Nat.Coprime.mul_left ha hb)
      inv_mem' := fun {a} ha ↦ by simpa using ha }
  have h : coprimePart p Q = S :=
    le_antisymm ((Subgroup.closure_le S).2 fun _ hx ↦ hx) fun _ hx ↦ Subgroup.subset_closure hx
  rw [h]
  rfl

theorem mem_primaryPart_iff_of_comm {p : ℕ} (hp : p.Prime) (hQ : ∀ a b : Q, a * b = b * a)
    {x : Q} : x ∈ primaryPart p Q ↔ ∃ n : ℕ, orderOf x = p ^ n := by
  let S : Subgroup Q :=
    { carrier := {x | ∃ n : ℕ, orderOf x = p ^ n}
      one_mem' := ⟨0, by simp⟩
      mul_mem' := fun {a b} ha hb ↦ by
        obtain ⟨m, hm⟩ := ha
        obtain ⟨n, hn⟩ := hb
        have h := (Commute.orderOf_mul_dvd_lcm (hQ a b)).trans (Nat.lcm_dvd_mul _ _)
        rw [hm, hn, ← pow_add] at h
        obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow hp).1 h
        exact ⟨k, hk⟩
      inv_mem' := fun {a} ha ↦ by simpa using ha }
  have h : primaryPart p Q = S :=
    le_antisymm ((Subgroup.closure_le S).2 fun _ hx ↦ hx) fun _ hx ↦ Subgroup.subset_closure hx
  rw [h]
  rfl

theorem exists_pow_prime_pow_mem_coprimePart {p : ℕ} (hp : p.Prime) {x : Q}
    (hx : IsOfFinOrder x) : ∃ k : ℕ, x ^ p ^ k ∈ coprimePart p Q := by
  obtain ⟨e, m, hm, he⟩ :=
    Nat.exists_eq_pow_mul_and_not_dvd hx.orderOf_pos.ne' p hp.one_lt.ne'
  refine ⟨e, Subgroup.subset_closure ?_⟩
  have hdvd : p ^ e ∣ orderOf x := ⟨m, he⟩
  rw [Set.mem_ofPred_eq, orderOf_pow_of_dvd (pow_ne_zero _ hp.ne_zero) hdvd, he,
    Nat.mul_div_cancel_left _ (pow_pos hp.pos _)]
  exact ((Nat.Prime.coprime_iff_not_dvd hp).2 hm).symm

theorem exists_coprime_pow_mem_primaryPart {p : ℕ} (hp : p.Prime) {x : Q}
    (hx : IsOfFinOrder x) : ∃ m : ℕ, m.Coprime p ∧ x ^ m ∈ primaryPart p Q := by
  obtain ⟨e, m, hm, he⟩ :=
    Nat.exists_eq_pow_mul_and_not_dvd hx.orderOf_pos.ne' p hp.one_lt.ne'
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact hm (dvd_zero p)
  refine ⟨m, ((Nat.Prime.coprime_iff_not_dvd hp).2 hm).symm, Subgroup.subset_closure ⟨e, ?_⟩⟩
  have hdvd : m ∣ orderOf x := ⟨p ^ e, by rw [he, mul_comm]⟩
  rw [orderOf_pow_of_dvd hm0 hdvd, he, Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hm0)]

theorem mem_of_pow_mem_of_pow_mem {S : Subgroup Q} {x : Q} {a b : ℕ} (hab : a.Coprime b)
    (ha : x ^ a ∈ S) (hb : x ^ b ∈ S) : x ∈ S := by
  have h := Nat.gcd_eq_gcd_ab a b
  rw [hab.gcd_eq_one, Nat.cast_one] at h
  have hx : x = (x ^ a) ^ (Nat.gcdA a b) * (x ^ b) ^ (Nat.gcdB a b) := by
    rw [← zpow_natCast x a, ← zpow_natCast x b, ← zpow_mul, ← zpow_mul, ← zpow_add, ← h,
      zpow_one]
  rw [hx]
  exact mul_mem (zpow_mem ha _) (zpow_mem hb _)

theorem eq_one_of_pow_eq_one_of_coprime {p : ℕ} {x : Q} (hx : (orderOf x).Coprime p)
    (h : x ^ p = 1) : x = 1 :=
  orderOf_eq_one_iff.1 (Nat.eq_one_of_dvd_coprimes hx dvd_rfl (orderOf_dvd_of_pow_eq_one h))

theorem coprime_card_of_pow_eq_one {p : ℕ} [Fact p.Prime] [Finite Q]
    (h : ∀ x : Q, x ^ p = 1 → x = 1) : (Nat.card Q).Coprime p := by
  refine ((Nat.Prime.coprime_iff_not_dvd Fact.out).2 fun hdvd ↦ ?_).symm
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p hdvd
  have h1 := h x (hx ▸ pow_orderOf_eq_one x)
  rw [h1, orderOf_one] at hx
  exact (Fact.out : p.Prime).one_lt.ne hx

end Parts

section LemmaG

variable {G : Type*} [Group G]

theorem isCyclic_quotient_of_le {M N : Subgroup G} [M.Normal] [N.Normal] (h : M ≤ N)
    [IsCyclic (G ⧸ M)] : IsCyclic (G ⧸ N) :=
  isCyclic_of_surjective (QuotientGroup.map M N (MonoidHom.id G) h) fun y ↦ by
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective y
    exact ⟨g, rfl⟩

variable (N : Subgroup G) [N.Normal]

instance coprimeQuotientPreimage_normal (p : ℕ) : (coprimeQuotientPreimage N p).Normal :=
  (coprimePart_normal p).comap _

instance primaryQuotientPreimage_normal (p : ℕ) : (primaryQuotientPreimage N p).Normal :=
  (primaryPart_normal p).comap _

theorem le_coprimeQuotientPreimage (p : ℕ) : N ≤ coprimeQuotientPreimage N p := by
  intro x hx
  rw [coprimeQuotientPreimage, Subgroup.mem_comap, QuotientGroup.mk'_apply,
    (QuotientGroup.eq_one_iff x).2 hx]
  exact one_mem _

theorem isPGroup_quotient_coprimeQuotientPreimage [Finite G] {p : ℕ} (hp : p.Prime) :
    IsPGroup p (G ⧸ coprimeQuotientPreimage N p) := by
  intro y
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective y
  obtain ⟨k, hk⟩ :=
    exists_pow_prime_pow_mem_coprimePart hp (isOfFinOrder_of_finite (QuotientGroup.mk' N g))
  refine ⟨k, ?_⟩
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, coprimeQuotientPreimage,
    Subgroup.mem_comap, map_pow]
  exact hk

theorem exists_card_quotient_coprimeQuotientPreimage_eq_pow [Finite G] {p : ℕ} (hp : p.Prime) :
    ∃ a : ℕ, Nat.card (G ⧸ coprimeQuotientPreimage N p) = p ^ a := by
  have := Fact.mk hp
  exact IsPGroup.iff_card.1 (isPGroup_quotient_coprimeQuotientPreimage N hp)

theorem coprime_card_quotient_primaryQuotientPreimage [Finite G] {l : ℕ} (hl : l.Prime) :
    (Nat.card (G ⧸ primaryQuotientPreimage N l)).Coprime l := by
  have := Fact.mk hl
  apply coprime_card_of_pow_eq_one
  intro y hy
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective y
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, primaryQuotientPreimage,
    Subgroup.mem_comap, map_pow] at hy
  rw [QuotientGroup.eq_one_iff, primaryQuotientPreimage, Subgroup.mem_comap]
  obtain ⟨m, hm, hgm⟩ :=
    exists_coprime_pow_mem_primaryPart hl (isOfFinOrder_of_finite (QuotientGroup.mk' N g))
  exact mem_of_pow_mem_of_pow_mem hm.symm hy hgm

theorem coprime_card_coprimeQuotientPreimage_quotient [Finite G] {p : ℕ} (hp : p.Prime)
    (G₀ G₁ : Subgroup G) [G₀.Normal] [G₁.Normal] (h10 : G₁ ≤ G₀) [IsCyclic (G ⧸ G₀)]
    (hG0 : (Nat.card (G₀ ⧸ G₁.subgroupOf G₀)).Coprime p) :
    (Nat.card (coprimeQuotientPreimage G₀ p ⧸
      G₁.subgroupOf (coprimeQuotientPreimage G₀ p))).Coprime p := by
  have := Fact.mk hp
  apply coprime_card_of_pow_eq_one
  intro y hy
  obtain ⟨⟨h, hH⟩, rfl⟩ := QuotientGroup.mk_surjective y
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf,
    Subgroup.coe_pow] at hy
  rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  have hcomm : ∀ a b : G ⧸ G₀, a * b = b * a := fun a b ↦ (IsCyclic.commGroup).mul_comm a b
  have h0 : h ∈ G₀ := by
    rw [coprimeQuotientPreimage, Subgroup.mem_comap, mem_coprimePart_iff_of_comm hcomm] at hH
    have h1 := eq_one_of_pow_eq_one_of_coprime hH (by
      rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact h10 hy)
    rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
  have h1 := eq_one_of_pow_eq_one_of_coprime
    (x := (QuotientGroup.mk (⟨h, h0⟩ : G₀) : G₀ ⧸ G₁.subgroupOf G₀))
    (Nat.Coprime.coprime_dvd_left (orderOf_dvd_natCard _) hG0) (by
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf,
        Subgroup.coe_pow]
      exact hy)
  rwa [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h1

section Relative

variable (G₀ G₁ : Subgroup G) [G₁.Normal]

theorem coprimeRelPreimage_le (p : ℕ) : coprimeRelPreimage G₀ G₁ p ≤ G₀ :=
  Subgroup.map_subtype_le _

theorem mem_coprimeRelPreimage_iff {p : ℕ} {x : G} :
    x ∈ coprimeRelPreimage G₀ G₁ p ↔ ∃ hx : x ∈ G₀,
      (QuotientGroup.mk (⟨x, hx⟩ : G₀) : G₀ ⧸ G₁.subgroupOf G₀) ∈ coprimePart p _ := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, hy⟩
  · rintro ⟨hx, h⟩
    exact ⟨⟨x, hx⟩, h, rfl⟩

instance coprimeRelPreimage_normal [G₀.Normal] (p : ℕ) : (coprimeRelPreimage G₀ G₁ p).Normal where
  conj_mem x hx g := by
    rw [mem_coprimeRelPreimage_iff] at hx ⊢
    obtain ⟨hx0, hx⟩ := hx
    let c : G₀ →* G₀ :=
      { toFun := fun y ↦ ⟨g * y * g⁻¹, (inferInstance : G₀.Normal).conj_mem y y.2 g⟩
        map_one' := by ext; simp
        map_mul' := fun a b ↦ by
          ext
          simp only [Subgroup.coe_mul]
          group }
    have hc : G₁.subgroupOf G₀ ≤ (G₁.subgroupOf G₀).comap c := fun y hy ↦ by
      rw [Subgroup.mem_subgroupOf] at hy
      rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf]
      exact (inferInstance : G₁.Normal).conj_mem _ hy g
    exact ⟨(inferInstance : G₀.Normal).conj_mem x hx0 g,
      map_coprimePart_le p (QuotientGroup.map _ _ c hc) (Subgroup.mem_map_of_mem _ hx)⟩

theorem coprime_card_coprimeRelPreimage [Finite G] {l p : ℕ} (hl : l.Prime) (hp : p.Prime)
    (hlp : l ≠ p) (hG1 : IsPGroup p G₁) [IsCyclic (G₀ ⧸ G₁.subgroupOf G₀)] :
    (Nat.card (coprimeRelPreimage G₀ G₁ l)).Coprime l := by
  have := Fact.mk hl
  apply coprime_card_of_pow_eq_one
  rintro ⟨b, hb⟩ hbl
  have hbl' : b ^ l = 1 := by
    simpa using congrArg Subtype.val hbl
  obtain ⟨hb0, hb'⟩ := (mem_coprimeRelPreimage_iff G₀ G₁).1 hb
  have hcomm : ∀ a c : G₀ ⧸ G₁.subgroupOf G₀, a * c = c * a :=
    fun a c ↦ (IsCyclic.commGroup).mul_comm a c
  rw [mem_coprimePart_iff_of_comm hcomm] at hb'
  have h1 := eq_one_of_pow_eq_one_of_coprime hb' (by
    rw [← QuotientGroup.mk_pow, show (⟨b, hb0⟩ : G₀) ^ l = 1 from Subtype.ext (by simpa using hbl'),
      QuotientGroup.mk_one])
  rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h1
  obtain ⟨k, hk⟩ := hG1 ⟨b, h1⟩
  have hbk : b ^ p ^ k = 1 := by simpa using congrArg Subtype.val hk
  have hco : (orderOf b).Coprime l :=
    Nat.Coprime.coprime_dvd_left (orderOf_dvd_of_pow_eq_one hbk)
      (Nat.Coprime.pow_left k ((Nat.coprime_primes hp hl).2 hlp.symm))
  exact Subtype.ext (eq_one_of_pow_eq_one_of_coprime hco hbl')

variable [G₀.Normal]

theorem isPGroup_primaryQuotientPreimage_quotient [Finite G] {l : ℕ} (hl : l.Prime)
    [IsCyclic (G ⧸ G₀)] :
    IsPGroup l (primaryQuotientPreimage G₀ l ⧸
      (coprimeRelPreimage G₀ G₁ l).subgroupOf (primaryQuotientPreimage G₀ l)) := by
  intro y
  obtain ⟨⟨a, ha⟩, rfl⟩ := QuotientGroup.mk_surjective y
  have hcomm : ∀ a b : G ⧸ G₀, a * b = b * a := fun a b ↦ (IsCyclic.commGroup).mul_comm a b
  rw [primaryQuotientPreimage, Subgroup.mem_comap, mem_primaryPart_iff_of_comm hl hcomm] at ha
  obtain ⟨n, hn⟩ := ha
  have ha0 : a ^ l ^ n ∈ G₀ := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, ← QuotientGroup.mk'_apply, ← hn,
      pow_orderOf_eq_one]
  obtain ⟨k, hk⟩ := exists_pow_prime_pow_mem_coprimePart hl
    (isOfFinOrder_of_finite (QuotientGroup.mk (⟨a ^ l ^ n, ha0⟩ : G₀) : G₀ ⧸ G₁.subgroupOf G₀))
  have hB : (a ^ l ^ n) ^ l ^ k ∈ coprimeRelPreimage G₀ G₁ l := by
    refine (mem_coprimeRelPreimage_iff G₀ G₁).2 ⟨pow_mem ha0 _, ?_⟩
    rw [← QuotientGroup.mk_pow] at hk
    exact hk
  refine ⟨n + k, ?_⟩
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf, Subgroup.coe_pow,
    pow_add, pow_mul]
  exact hB

end Relative

end LemmaG

section Galois

open GroundTheory.LocalField ValuativeRel IntermediateField

theorem algEquiv_apply_eq_of_pow_prime_pow_apply_eq {K L : Type*} [Field K] [Field L]
    [Algebra K L] {l : ℕ} (hl : l.Prime) {ζ : L} (hζ : ζ ^ l = 1) (σ : L ≃ₐ[K] L) {n : ℕ}
    (h : (σ ^ l ^ n) ζ = ζ) : σ ζ = ζ := by
  rcases (Nat.dvd_prime hl).1 (orderOf_dvd_of_pow_eq_one hζ) with h1 | hl'
  · rw [orderOf_eq_one_iff.1 h1, map_one]
  have hprim : IsPrimitiveRoot ζ l := hl' ▸ IsPrimitiveRoot.orderOf ζ
  have : NeZero l := ⟨hl.ne_zero⟩
  obtain ⟨k, -, hk⟩ := hprim.eq_pow_of_pow_eq_one (ξ := σ ζ) (by rw [← map_pow, hζ, map_one])
  have key : ∀ m : ℕ, (σ ^ m) ζ = ζ ^ k ^ m := by
    intro m
    induction m with
    | zero => simp
    | succ m ih => rw [pow_succ, AlgEquiv.mul_apply, ← hk, map_pow, ih, ← pow_mul, ← pow_succ]
  have hmod : ∀ a : ℕ, ζ ^ a = ζ ^ (a % l) := fun a ↦ by
    conv_lhs => rw [← Nat.div_add_mod a l, pow_add, pow_mul, hζ, one_pow, one_mul]
  have hkm : k ^ l ^ n % l = k % l := by
    have := Fact.mk hl
    rw [← ZMod.natCast_eq_natCast_iff', Nat.cast_pow, ZMod.pow_card_pow]
  rw [key] at h
  calc σ ζ = ζ ^ k := hk.symm
    _ = ζ ^ (k ^ l ^ n % l) := by rw [hkm, ← hmod]
    _ = ζ := by rw [← hmod, h]

variable (K L : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]

instance isCyclic_quotient_lowerRamificationGroup_zero :
    IsCyclic ((L ≃ₐ[K] L) ⧸ lowerRamificationGroup K L 0) := by
  have : IsCyclic ((L ≃ₐ[K] L) ⧸ (residueAlgEquiv K L).ker) :=
    isCyclic_of_injective (QuotientGroup.kerLift _) (QuotientGroup.kerLift_injective _)
  exact isCyclic_of_surjective
    (QuotientGroup.quotientMulEquivOfEq (lowerRamificationGroup_zero K L).symm).toMonoidHom
    (MulEquiv.surjective _)

theorem natCast_residueField_ne_zero {l : ℕ} (hl : l.Prime) (hlp : l ≠ ringChar 𝓀[K]) :
    (l : 𝓀[L]) ≠ 0 := by
  rw [Ne, ringChar.spec, ← Algebra.ringChar_eq 𝓀[K] 𝓀[L]]
  intro h
  exact hlp ((Nat.prime_dvd_prime_iff_eq (CharP.char_is_prime 𝓀[K] _) hl).1 h).symm

variable {K L} in

theorem apply_eq_of_mem_lowerRamificationGroup_zero {m : ℕ} (hm : (m : 𝓀[L]) ≠ 0)
    {σ : L ≃ₐ[K] L} (hσ : σ ∈ lowerRamificationGroup K L 0) {ζ : L} (hζ : ζ ^ m = 1) :
    σ ζ = ζ := by
  have hm0 : m ≠ 0 := by
    rintro rfl
    simp at hm
  let z : 𝒪[L] := ⟨ζ, mem_integer_of_pow_eq_one hm0 hζ⟩
  have hz : z ^ m = 1 := Subtype.ext (by simpa [z] using hζ)
  have h := eq_of_pow_eq_one_of_residue_eq hm (x := integerAlgEquiv K L σ z) (y := z)
    (by rw [← map_pow, hz, map_one]) hz (residue_integerAlgEquiv_of_mem_zero K L hσ z)
  simpa [z] using congrArg Subtype.val h

theorem lowerRamificationGroup_one_le_coprimeQuotientPreimage :
    lowerRamificationGroup K L 1 ≤
      coprimeQuotientPreimage (lowerRamificationGroup K L 0) (ringChar 𝓀[K]) :=
  (lowerRamificationGroup_antitone K L zero_le_one).trans (le_coprimeQuotientPreimage _ _)

theorem isCyclic_quotient_coprimeQuotientPreimage_lowerRamificationGroup :
    IsCyclic ((L ≃ₐ[K] L) ⧸
      coprimeQuotientPreimage (lowerRamificationGroup K L 0) (ringChar 𝓀[K])) :=
  isCyclic_quotient_of_le (le_coprimeQuotientPreimage _ _)

theorem exists_card_quotient_coprimeQuotientPreimage_lowerRamificationGroup_eq_pow :
    ∃ a : ℕ, Nat.card ((L ≃ₐ[K] L) ⧸
      coprimeQuotientPreimage (lowerRamificationGroup K L 0) (ringChar 𝓀[K])) =
        ringChar 𝓀[K] ^ a :=
  exists_card_quotient_coprimeQuotientPreimage_eq_pow _ (CharP.char_is_prime 𝓀[K] _)

theorem coprime_card_coprimeQuotientPreimage_quotient_lowerRamificationGroup_one :
    (Nat.card (coprimeQuotientPreimage (lowerRamificationGroup K L 0) (ringChar 𝓀[K]) ⧸
      (lowerRamificationGroup K L 1).subgroupOf
        (coprimeQuotientPreimage (lowerRamificationGroup K L 0) (ringChar 𝓀[K])))).Coprime
      (ringChar 𝓀[K]) := by
  have := isCyclic_lowerRamificationGroup_zero_quotient K L
  exact coprime_card_coprimeQuotientPreimage_quotient (CharP.char_is_prime 𝓀[K] _) _ _
    (lowerRamificationGroup_antitone K L zero_le_one)
    (coprime_card_lowerRamificationGroup_zero_quotient K L)

theorem pow_eq_one_mem_fixedField_lowerRamificationGroup_one {ζ : L}
    (hζ : ζ ^ ringChar 𝓀[K] = 1) : ζ ∈ fixedField (lowerRamificationGroup K L 1) := by
  refine (mem_fixedField_iff _ _).2 fun σ hσ ↦ ?_
  obtain ⟨n, hn⟩ := isPGroup_lowerRamificationGroup_one K L ⟨σ, hσ⟩
  have hσn : σ ^ ringChar 𝓀[K] ^ n = 1 := by simpa using congrArg Subtype.val hn
  exact algEquiv_apply_eq_of_pow_prime_pow_apply_eq (CharP.char_is_prime 𝓀[K] _) hζ σ
    (by rw [hσn, AlgEquiv.one_apply])

theorem coprime_card_coprimeRelPreimage_lowerRamificationGroup {l : ℕ} (hl : l.Prime)
    (hlp : l ≠ ringChar 𝓀[K]) :
    (Nat.card (coprimeRelPreimage (lowerRamificationGroup K L 0)
      (lowerRamificationGroup K L 1) l)).Coprime l := by
  have := isCyclic_lowerRamificationGroup_zero_quotient K L
  exact coprime_card_coprimeRelPreimage _ _ hl (CharP.char_is_prime 𝓀[K] _) hlp
    (isPGroup_lowerRamificationGroup_one K L)

theorem isPGroup_primaryQuotientPreimage_quotient_lowerRamificationGroup {l : ℕ}
    (hl : l.Prime) :
    IsPGroup l (primaryQuotientPreimage (lowerRamificationGroup K L 0) l ⧸
      (coprimeRelPreimage (lowerRamificationGroup K L 0) (lowerRamificationGroup K L 1) l).subgroupOf
        (primaryQuotientPreimage (lowerRamificationGroup K L 0) l)) :=
  isPGroup_primaryQuotientPreimage_quotient _ _ hl

theorem coprime_card_quotient_primaryQuotientPreimage_lowerRamificationGroup {l : ℕ}
    (hl : l.Prime) :
    (Nat.card ((L ≃ₐ[K] L) ⧸
      primaryQuotientPreimage (lowerRamificationGroup K L 0) l)).Coprime l :=
  coprime_card_quotient_primaryQuotientPreimage _ hl

theorem pow_eq_one_mem_fixedField_primaryQuotientPreimage {l : ℕ} (hl : l.Prime)
    (hlp : l ≠ ringChar 𝓀[K]) {ζ : L} (hζ : ζ ^ l = 1) :
    ζ ∈ fixedField (primaryQuotientPreimage (lowerRamificationGroup K L 0) l) := by
  refine (mem_fixedField_iff _ _).2 fun σ hσ ↦ ?_
  have hcomm : ∀ a b : (L ≃ₐ[K] L) ⧸ lowerRamificationGroup K L 0, a * b = b * a :=
    fun a b ↦ (IsCyclic.commGroup).mul_comm a b
  rw [primaryQuotientPreimage, Subgroup.mem_comap, mem_primaryPart_iff_of_comm hl hcomm] at hσ
  obtain ⟨n, hn⟩ := hσ
  have h0 : σ ^ l ^ n ∈ lowerRamificationGroup K L 0 := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, ← QuotientGroup.mk'_apply, ← hn,
      pow_orderOf_eq_one]
  exact algEquiv_apply_eq_of_pow_prime_pow_apply_eq hl hζ σ
    (apply_eq_of_mem_lowerRamificationGroup_zero (natCast_residueField_ne_zero K L hl hlp) h0 hζ)

end Galois

end GroundTheory.ProfCoh
