import Mathlib

namespace GlobalTheory

section Defs

variable {R V : Type*} [Ring R] [AddCommGroup V] [Module R V]

noncomputable def relLength (A B : Submodule R V) : ℕ∞ :=
  Module.length R (A ⧸ B.submoduleOf A)

def LengthCommensurable (A B : Submodule R V) : Prop :=
  relLength A B ≠ ⊤ ∧ relLength B A ≠ ⊤

noncomputable def signedLength (A B : Submodule R V) : ℤ :=
  ((relLength A B).toNat : ℤ) - ((relLength B A).toNat : ℤ)

end Defs

section Basic

variable {R V : Type*} [Ring R] [AddCommGroup V] [Module R V]

theorem relLength_def (A B : Submodule R V) :
    relLength A B = Module.length R (A ⧸ B.submoduleOf A) := rfl

theorem relLength_eq_length_quotient_comap (A B : Submodule R V) :
    relLength A B = Module.length R (A ⧸ B.comap A.subtype) := rfl

theorem relLength_eq_length_range {P : Type*} [AddCommGroup P] [Module R P]
    {A B : Submodule R V} (g : A →ₗ[R] P) (hg : LinearMap.ker g = B.submoduleOf A) :
    relLength A B = Module.length R (LinearMap.range g) := by
  rw [relLength_def, ← hg]
  exact g.quotKerEquivRange.length_eq

theorem relLength_eq_length_of_surjective {P : Type*} [AddCommGroup P] [Module R P]
    {A B : Submodule R V} (g : A →ₗ[R] P) (hg : LinearMap.ker g = B.submoduleOf A)
    (hs : Function.Surjective g) : relLength A B = Module.length R P := by
  rw [relLength_eq_length_range g hg, LinearMap.range_eq_top.mpr hs, Module.length_top]

theorem relLength_eq_length_map_mkQ (A B : Submodule R V) :
    relLength A B = Module.length R (A.map B.mkQ) := by
  rw [relLength_eq_length_range (B.mkQ ∘ₗ A.subtype)
    (by rw [LinearMap.ker_comp, Submodule.ker_mkQ]; rfl), LinearMap.range_comp,
    Submodule.range_subtype]

theorem relLength_ne_top_iff {A B : Submodule R V} :
    relLength A B ≠ ⊤ ↔ IsFiniteLength R (A ⧸ B.submoduleOf A) :=
  Module.length_ne_top_iff

theorem relLength_congr_right {A B B' : Submodule R V} (h : A ⊓ B = A ⊓ B') :
    relLength A B = relLength A B' := by
  have : B.submoduleOf A = B'.submoduleOf A := by
    ext x
    have := SetLike.ext_iff.mp h (x : V)
    simpa [Submodule.submoduleOf, x.2] using this
  rw [relLength_def, relLength_def, this]

theorem relLength_congr_left {A A' B : Submodule R V} (h : A ⊔ B = A' ⊔ B) :
    relLength A B = relLength A' B := by
  have : A.map B.mkQ = A'.map B.mkQ := by
    have := congrArg (Submodule.map B.mkQ) h
    simpa [Submodule.map_sup] using this
  rw [relLength_eq_length_map_mkQ, relLength_eq_length_map_mkQ, this]

@[simp] theorem relLength_inf_right (A B : Submodule R V) :
    relLength A (A ⊓ B) = relLength A B :=
  relLength_congr_right (by rw [← inf_assoc, inf_idem])

@[simp] theorem relLength_inf_right' (A B : Submodule R V) :
    relLength A (B ⊓ A) = relLength A B := by
  rw [inf_comm, relLength_inf_right]

@[simp] theorem relLength_sup_left (A B : Submodule R V) :
    relLength (A ⊔ B) B = relLength A B :=
  relLength_congr_left (by rw [sup_assoc, sup_idem])

@[simp] theorem relLength_sup_left' (A B : Submodule R V) :
    relLength (B ⊔ A) B = relLength A B := by
  rw [sup_comm, relLength_sup_left]

theorem relLength_inf_eq_relLength_sup (A B : Submodule R V) :
    relLength A (A ⊓ B) = relLength (A ⊔ B) B := by simp

@[simp] theorem relLength_eq_zero_iff {A B : Submodule R V} : relLength A B = 0 ↔ A ≤ B := by
  rw [relLength_def, Module.length_eq_zero_iff, Submodule.Quotient.subsingleton_iff,
    Submodule.submoduleOf_eq_top]

theorem relLength_eq_zero_of_le {A B : Submodule R V} (h : A ≤ B) : relLength A B = 0 :=
  relLength_eq_zero_iff.mpr h

theorem relLength_pos_iff {A B : Submodule R V} : 0 < relLength A B ↔ ¬ A ≤ B := by
  rw [pos_iff_ne_zero, ne_eq, relLength_eq_zero_iff]

theorem relLength_self (A : Submodule R V) : relLength A A = 0 := by simp

theorem relLength_bot_left (B : Submodule R V) : relLength ⊥ B = 0 := by simp

theorem relLength_top_right (A : Submodule R V) : relLength A ⊤ = 0 := by simp

@[simp] theorem relLength_bot_right (A : Submodule R V) :
    relLength A ⊥ = Module.length R A :=
  relLength_eq_length_of_surjective (LinearMap.id : A →ₗ[R] A)
    (by simp [Submodule.submoduleOf]) Function.surjective_id

@[simp] theorem relLength_top_left (B : Submodule R V) :
    relLength ⊤ B = Module.length R (V ⧸ B) := by
  rw [relLength_eq_length_map_mkQ, Submodule.map_top, Submodule.range_mkQ, Module.length_top]

theorem relLength_mono_left {A A' : Submodule R V} (h : A ≤ A') (B : Submodule R V) :
    relLength A B ≤ relLength A' B := by
  rw [relLength_eq_length_map_mkQ, relLength_eq_length_map_mkQ]
  exact Module.length_le_of_injective (Submodule.inclusion (Submodule.map_mono h))
    (Submodule.inclusion_injective _)

theorem relLength_anti_right (A : Submodule R V) {B B' : Submodule R V} (h : B ≤ B') :
    relLength A B' ≤ relLength A B :=
  Module.length_le_of_surjective
    (Submodule.factor (Submodule.comap_mono h : B.submoduleOf A ≤ B'.submoduleOf A))
    (Submodule.factor_surjective _)

@[gcongr] theorem relLength_le_relLength {A A' B B' : Submodule R V} (hA : A ≤ A')
    (hB : B' ≤ B) : relLength A B ≤ relLength A' B' :=
  (relLength_mono_left hA B).trans (relLength_anti_right A' hB)

theorem monotone_relLength_left (B : Submodule R V) : Monotone fun A => relLength A B :=
  fun _ _ h => relLength_mono_left h B

theorem antitone_relLength_right (A : Submodule R V) : Antitone (relLength A) :=
  fun _ _ h => relLength_anti_right A h

theorem relLength_le_length_left (A B : Submodule R V) : relLength A B ≤ Module.length R A := by
  rw [← relLength_bot_right]
  exact relLength_anti_right A bot_le

theorem relLength_le_length_quotient (A B : Submodule R V) :
    relLength A B ≤ Module.length R (V ⧸ B) := by
  rw [← relLength_top_left]
  exact relLength_mono_left le_top B

end Basic

section Map

variable {R S V V' : Type*} [Ring R] [Ring S] [AddCommGroup V] [Module R V]
  [AddCommGroup V'] [Module S V'] {σ : R →+* S} [RingHomSurjective σ]

theorem length_eq_of_semilinear_bijective (f : V →ₛₗ[σ] V') (hf : Function.Bijective f) :
    Module.length R V = Module.length S V' := by
  apply WithBot.coe_injective
  rw [Module.coe_length, Module.coe_length,
    Order.krullDim_eq_of_orderIso (Submodule.orderIsoMapComapOfBijective f hf)]

theorem relLength_map_left (f : V →ₛₗ[σ] V') (A : Submodule R V) (B' : Submodule S V') :
    relLength (A.map f) B' = relLength A (B'.comap f) := by
  symm
  let g : A →ₛₗ[σ] A.map f := f.restrict fun x hx => Submodule.mem_map_of_mem hx
  refine length_eq_of_semilinear_bijective
    (Submodule.mapQ ((B'.comap f).submoduleOf A) (B'.submoduleOf (A.map f)) g
      fun x hx => hx) ⟨?_, ?_⟩
  · rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    have hx' : (Submodule.Quotient.mk (g x) : A.map f ⧸ B'.submoduleOf (A.map f)) = 0 := hx
    rw [Submodule.Quotient.mk_eq_zero] at hx' ⊢
    exact hx'
  · intro y
    obtain ⟨⟨_, x, hx, rfl⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    exact ⟨Submodule.Quotient.mk ⟨x, hx⟩, rfl⟩

theorem relLength_map_map (f : V →ₛₗ[σ] V') (A B : Submodule R V) :
    relLength (A.map f) (B.map f) = relLength A (B ⊔ LinearMap.ker f) := by
  rw [relLength_map_left, Submodule.comap_map_eq]

theorem relLength_comap_comap (f : V →ₛₗ[σ] V') (A' B' : Submodule S V') :
    relLength (A'.comap f) (B'.comap f) = relLength (LinearMap.range f ⊓ A') B' := by
  rw [← relLength_map_left, Submodule.map_comap_eq]

theorem relLength_map_of_injective (f : V →ₛₗ[σ] V') (hf : Function.Injective f)
    (A B : Submodule R V) : relLength (A.map f) (B.map f) = relLength A B := by
  rw [relLength_map_left, Submodule.comap_map_eq_of_injective hf]

theorem relLength_comap_of_le_range (f : V →ₛₗ[σ] V') {A' : Submodule S V'}
    (hA : A' ≤ LinearMap.range f) (B' : Submodule S V') :
    relLength (A'.comap f) (B'.comap f) = relLength A' B' := by
  rw [relLength_comap_comap, inf_eq_right.mpr hA]

theorem relLength_comap_of_surjective (f : V →ₛₗ[σ] V') (hf : Function.Surjective f)
    (A' B' : Submodule S V') : relLength (A'.comap f) (B'.comap f) = relLength A' B' :=
  relLength_comap_of_le_range f (by rw [LinearMap.range_eq_top.mpr hf]; exact le_top) B'

theorem lengthCommensurable_map_iff_of_injective (f : V →ₛₗ[σ] V') (hf : Function.Injective f)
    {A B : Submodule R V} :
    LengthCommensurable (A.map f) (B.map f) ↔ LengthCommensurable A B := by
  simp only [LengthCommensurable, relLength_map_of_injective f hf]

theorem LengthCommensurable.signedLength_map_of_injective {A B : Submodule R V}
    (_h : LengthCommensurable A B) (f : V →ₛₗ[σ] V') (hf : Function.Injective f) :
    signedLength (A.map f) (B.map f) = signedLength A B := by
  simp only [signedLength, relLength_map_of_injective f hf]

end Map

section Equiv

variable {R S V V' : Type*} [Ring R] [Ring S] [AddCommGroup V] [Module R V]
  [AddCommGroup V'] [Module S V'] {σ : R →+* S} {σ' : S →+* R}
  [RingHomInvPair σ σ'] [RingHomInvPair σ' σ] [RingHomSurjective σ]

theorem relLength_map_equiv (e : V ≃ₛₗ[σ] V') (A B : Submodule R V) :
    relLength (A.map (e : V →ₛₗ[σ] V')) (B.map (e : V →ₛₗ[σ] V')) = relLength A B :=
  relLength_map_of_injective _ e.injective A B

theorem relLength_comap_equiv (e : V ≃ₛₗ[σ] V') (A' B' : Submodule S V') :
    relLength (A'.comap (e : V →ₛₗ[σ] V')) (B'.comap (e : V →ₛₗ[σ] V')) = relLength A' B' :=
  relLength_comap_of_surjective _ e.surjective A' B'

theorem lengthCommensurable_map_equiv_iff (e : V ≃ₛₗ[σ] V') {A B : Submodule R V} :
    LengthCommensurable (A.map (e : V →ₛₗ[σ] V')) (B.map (e : V →ₛₗ[σ] V')) ↔
      LengthCommensurable A B :=
  lengthCommensurable_map_iff_of_injective _ e.injective

theorem LengthCommensurable.signedLength_map_equiv {A B : Submodule R V}
    (h : LengthCommensurable A B) (e : V ≃ₛₗ[σ] V') :
    signedLength (A.map (e : V →ₛₗ[σ] V')) (B.map (e : V →ₛₗ[σ] V')) = signedLength A B :=
  h.signedLength_map_of_injective _ e.injective

end Equiv

section Ambient

variable {R V : Type*} [Ring R] [AddCommGroup V] [Module R V]

theorem relLength_submoduleOf {A W : Submodule R V} (h : A ≤ W) (B : Submodule R V) :
    relLength (A.submoduleOf W) (B.submoduleOf W) = relLength A B :=
  relLength_comap_of_le_range W.subtype (by rwa [Submodule.range_subtype]) B

theorem relLength_map_subtype (W : Submodule R V) (A B : Submodule R W) :
    relLength (A.map W.subtype) (B.map W.subtype) = relLength A B :=
  relLength_map_of_injective W.subtype W.injective_subtype A B

theorem relLength_map_mkQ {N B : Submodule R V} (h : N ≤ B) (A : Submodule R V) :
    relLength (A.map N.mkQ) (B.map N.mkQ) = relLength A B := by
  rw [relLength_map_map, Submodule.ker_mkQ, sup_eq_left.mpr h]

open Pointwise in

theorem relLength_smul_smul {G : Type*} [Monoid G] [DistribMulAction G V] [SMulCommClass G R V]
    {a : G} (ha : IsSMulRegular V a) (A B : Submodule R V) :
    relLength (a • A) (a • B) = relLength A B :=
  relLength_map_of_injective (DistribSMul.toLinearMap R V a) ha A B

open Pointwise in

theorem lengthCommensurable_smul_smul_iff {G : Type*} [Monoid G] [DistribMulAction G V]
    [SMulCommClass G R V] {a : G} (ha : IsSMulRegular V a) {A B : Submodule R V} :
    LengthCommensurable (a • A) (a • B) ↔ LengthCommensurable A B :=
  lengthCommensurable_map_iff_of_injective (DistribSMul.toLinearMap R V a) ha

open Pointwise in

theorem LengthCommensurable.signedLength_smul_smul {G : Type*} [Monoid G] [DistribMulAction G V]
    [SMulCommClass G R V] {a : G} {A B : Submodule R V} (h : LengthCommensurable A B)
    (ha : IsSMulRegular V a) : signedLength (a • A) (a • B) = signedLength A B :=
  h.signedLength_map_of_injective (DistribSMul.toLinearMap R V a) ha

open Pointwise in

example (A B : Submodule ℤ (Fin 2 → ℚ)) {s : ℚ} (hs : s ≠ 0) :
    relLength (s • A) (s • B) = relLength A B :=
  relLength_smul_smul (IsSMulRegular.of_ne_zero hs) A B

end Ambient

section Signed

variable {R V : Type*} [Ring R] [AddCommGroup V] [Module R V] {A B : Submodule R V}

theorem lengthCommensurable_iff_isFiniteLength :
    LengthCommensurable A B ↔
      IsFiniteLength R (A ⧸ B.submoduleOf A) ∧ IsFiniteLength R (B ⧸ A.submoduleOf B) := by
  rw [LengthCommensurable, relLength_ne_top_iff, relLength_ne_top_iff]

@[refl] theorem LengthCommensurable.refl (A : Submodule R V) : LengthCommensurable A A := by
  simp [LengthCommensurable, relLength_self]

@[symm] theorem LengthCommensurable.symm (h : LengthCommensurable A B) :
    LengthCommensurable B A := ⟨h.2, h.1⟩

theorem lengthCommensurable_comm : LengthCommensurable A B ↔ LengthCommensurable B A :=
  ⟨.symm, .symm⟩

theorem lengthCommensurable_iff_of_ge (h : B ≤ A) :
    LengthCommensurable A B ↔ relLength A B ≠ ⊤ := by
  simp [LengthCommensurable, relLength_eq_zero_of_le h]

theorem lengthCommensurable_iff_of_le (h : A ≤ B) :
    LengthCommensurable A B ↔ relLength B A ≠ ⊤ := by
  simp [LengthCommensurable, relLength_eq_zero_of_le h]

theorem lengthCommensurable_of_length_ne_top (h : Module.length R V ≠ ⊤) (A B : Submodule R V) :
    LengthCommensurable A B := by
  have key : ∀ C D : Submodule R V, relLength C D ≠ ⊤ := fun C D =>
    ne_top_of_le_ne_top h ((relLength_le_length_left C D).trans
      (Module.length_le_of_injective C.subtype C.injective_subtype))
  exact ⟨key A B, key B A⟩

theorem lengthCommensurable_iff_inf :
    LengthCommensurable A B ↔
      LengthCommensurable A (A ⊓ B) ∧ LengthCommensurable B (A ⊓ B) := by
  rw [lengthCommensurable_iff_of_ge (inf_le_left : A ⊓ B ≤ A),
    lengthCommensurable_iff_of_ge (inf_le_right : A ⊓ B ≤ B),
    relLength_inf_right, relLength_inf_right', LengthCommensurable]

theorem lengthCommensurable_iff_sup :
    LengthCommensurable A B ↔
      LengthCommensurable (A ⊔ B) B ∧ LengthCommensurable (A ⊔ B) A := by
  rw [lengthCommensurable_iff_of_ge (le_sup_right : B ≤ A ⊔ B),
    lengthCommensurable_iff_of_ge (le_sup_left : A ≤ A ⊔ B),
    relLength_sup_left, relLength_sup_left', LengthCommensurable]

theorem signedLength_eq_of_relLength_eq {m n : ℕ} (hm : relLength A B = m)
    (hn : relLength B A = n) : signedLength A B = (m : ℤ) - n := by
  simp [signedLength, hm, hn]

@[simp] theorem signedLength_self (A : Submodule R V) : signedLength A A = 0 := sub_self _

namespace LengthCommensurable

theorem exists_signedLength_eq (h : LengthCommensurable A B) :
    ∃ m n : ℕ, relLength A B = m ∧ relLength B A = n ∧ signedLength A B = (m : ℤ) - n :=
  ⟨_, _, (ENat.coe_toNat h.1).symm, (ENat.coe_toNat h.2).symm, rfl⟩

theorem signedLength_swap (_h : LengthCommensurable A B) :
    signedLength B A = -signedLength A B := by
  simp [signedLength]

theorem signedLength_add_swap (h : LengthCommensurable A B) :
    signedLength A B + signedLength B A = 0 := by
  rw [h.signedLength_swap, add_neg_cancel]

theorem signedLength_of_ge (_h : LengthCommensurable A B) (hBA : B ≤ A) :
    signedLength A B = (relLength A B).toNat := by
  simp [signedLength, relLength_eq_zero_of_le hBA]

theorem signedLength_of_le (_h : LengthCommensurable A B) (hAB : A ≤ B) :
    signedLength A B = -((relLength B A).toNat : ℤ) := by
  simp [signedLength, relLength_eq_zero_of_le hAB]

theorem coe_toNat_signedLength_of_ge (h : LengthCommensurable A B) (hBA : B ≤ A) :
    ((signedLength A B).toNat : ℕ∞) = relLength A B := by
  rw [h.signedLength_of_ge hBA, Int.toNat_natCast, ENat.coe_toNat h.1]

theorem signedLength_eq_natCast_iff_of_ge (h : LengthCommensurable A B) (hBA : B ≤ A) {n : ℕ} :
    signedLength A B = n ↔ relLength A B = n := by
  rw [h.signedLength_of_ge hBA, Nat.cast_inj, ← ENat.coe_inj, ENat.coe_toNat h.1]

theorem signedLength_le_natCast_iff_of_ge (h : LengthCommensurable A B) (hBA : B ≤ A) {n : ℕ} :
    signedLength A B ≤ n ↔ relLength A B ≤ n := by
  rw [h.signedLength_of_ge hBA, Nat.cast_le, ← ENat.coe_le_coe, ENat.coe_toNat h.1]

theorem signedLength_nonneg (h : LengthCommensurable A B) (hBA : B ≤ A) :
    0 ≤ signedLength A B := by
  rw [h.signedLength_of_ge hBA]
  exact Int.natCast_nonneg _

theorem signedLength_nonpos (h : LengthCommensurable A B) (hAB : A ≤ B) :
    signedLength A B ≤ 0 := by
  rw [h.signedLength_of_le hAB, neg_nonpos]
  exact Int.natCast_nonneg _

theorem signedLength_eq_zero_iff_of_ge (h : LengthCommensurable A B) (hBA : B ≤ A) :
    signedLength A B = 0 ↔ A = B := by
  have := h.signedLength_eq_natCast_iff_of_ge hBA (n := 0)
  rw [Nat.cast_zero, Nat.cast_zero, relLength_eq_zero_iff] at this
  exact this.trans ⟨fun hAB => le_antisymm hAB hBA, le_of_eq⟩

theorem signedLength_le_toNat_relLength (_h : LengthCommensurable A B) :
    signedLength A B ≤ (relLength A B).toNat :=
  sub_le_self _ (Int.natCast_nonneg _)

theorem signedLength_eq_sub_inf (h : LengthCommensurable A B) :
    signedLength A B = signedLength A (A ⊓ B) - signedLength B (A ⊓ B) := by
  obtain ⟨h₁, h₂⟩ := lengthCommensurable_iff_inf.mp h
  rw [h₁.signedLength_of_ge inf_le_left, h₂.signedLength_of_ge inf_le_right,
    relLength_inf_right, relLength_inf_right', signedLength]

theorem signedLength_eq_sub_sup (h : LengthCommensurable A B) :
    signedLength A B = signedLength (A ⊔ B) B - signedLength (A ⊔ B) A := by
  obtain ⟨h₁, h₂⟩ := lengthCommensurable_iff_sup.mp h
  rw [h₁.signedLength_of_ge le_sup_right, h₂.signedLength_of_ge le_sup_left,
    relLength_sup_left, relLength_sup_left', signedLength]

theorem signedLength_le_signedLength {A' B' : Submodule R V} (h : LengthCommensurable A B)
    (h' : LengthCommensurable A' B') (hA : A ≤ A') (hB : B' ≤ B) :
    signedLength A B ≤ signedLength A' B' := by
  have h₁ := ENat.toNat_le_toNat (relLength_le_relLength hA hB) h'.1
  have h₂ := ENat.toNat_le_toNat (relLength_le_relLength hB hA) h.2
  unfold signedLength
  omega

end LengthCommensurable

end Signed

section Examples

theorem relLength_top_of_isMaximal {R : Type*} [CommRing R] (I : Ideal R) [hI : I.IsMaximal] :
    relLength (⊤ : Ideal R) I = 1 := by
  rw [relLength_top_left, Module.length_eq_one_iff, isSimpleModule_iff_isCoatom]
  exact hI.out

theorem relLength_int_top_span_prime {p : ℤ} (hp : Prime p) :
    relLength (⊤ : Ideal ℤ) (Ideal.span {p}) = 1 :=
  have := PrincipalIdealRing.isMaximal_of_irreducible hp.irreducible
  relLength_top_of_isMaximal _

example : LengthCommensurable (⊤ : Ideal ℤ) (Ideal.span {2}) ∧
    signedLength (⊤ : Ideal ℤ) (Ideal.span {2}) = 1 ∧
    signedLength (Ideal.span {2}) (⊤ : Ideal ℤ) = -1 := by
  have h₁ := relLength_int_top_span_prime Int.prime_two
  have h : LengthCommensurable (⊤ : Ideal ℤ) (Ideal.span {2}) := by
    rw [lengthCommensurable_iff_of_ge le_top, h₁]
    simp
  have h₂ : signedLength (⊤ : Ideal ℤ) (Ideal.span {2}) = 1 := by
    rw [h.signedLength_of_ge le_top, h₁]
    simp
  exact ⟨h, h₂, by rw [h.signedLength_swap, h₂]⟩

example : relLength (Ideal.span {2} : Ideal ℤ) (Ideal.span {3}) = 1 ∧
    relLength (Ideal.span {3} : Ideal ℤ) (Ideal.span {2}) = 1 ∧
    signedLength (Ideal.span {2} : Ideal ℤ) (Ideal.span {3}) = 0 := by
  have hs : (Ideal.span {2} : Ideal ℤ) ⊔ Ideal.span {3} = ⊤ := by
    rw [Ideal.sup_eq_top_iff_isCoprime]
    exact ⟨-1, 1, by norm_num⟩
  have h₁ : relLength (Ideal.span {2} : Ideal ℤ) (Ideal.span {3}) = 1 := by
    rw [← relLength_sup_left, hs]
    exact relLength_int_top_span_prime Int.prime_three
  have h₂ : relLength (Ideal.span {3} : Ideal ℤ) (Ideal.span {2}) = 1 := by
    rw [← relLength_sup_left', hs]
    exact relLength_int_top_span_prime Int.prime_two
  exact ⟨h₁, h₂, by
    rw [signedLength_eq_of_relLength_eq (m := 1) (n := 1) (by simpa using h₁) (by simpa using h₂)]
    simp⟩

example : relLength (⊤ : Submodule ℚ (ℚ × ℚ)) ⊥ = 2 := by
  rw [relLength_bot_right, Module.length_top, Module.length_prod, Module.length_eq_one]
  rfl

example : ¬ LengthCommensurable (⊤ : Ideal ℤ) ⊥ := by
  rw [lengthCommensurable_iff_of_ge bot_le, relLength_bot_right, Module.length_top,
    Module.length_ne_top_iff, isFiniteLength_iff_isNoetherian_isArtinian]
  rintro ⟨-, h⟩
  have : IsArtinianRing ℤ := h
  exact Int.not_isField (IsArtinianRing.isField_of_isDomain ℤ)

end Examples

end GlobalTheory
