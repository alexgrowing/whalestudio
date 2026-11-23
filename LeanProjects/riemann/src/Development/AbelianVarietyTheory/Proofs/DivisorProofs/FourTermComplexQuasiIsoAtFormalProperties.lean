import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PullbackBijectiveDegreesOneTwo

set_option autoImplicit false

open CategoryTheory GlobalTheory.CxCoh

namespace GlobalTheory.CxCoh.QAtFormal

universe u

variable {C : Type u} [Category.{0} C] (K : Cx C)

theorem qAt_ident (T : C) : K.QAt (𝟙 T) := by
  refine ⟨fun x _ h => ?_, fun y hy => ⟨y, hy, ?_⟩, fun x y _ h => ⟨y, ?_⟩, fun y hy => ⟨y, 0, hy, ?_⟩,
    fun x y _ h => ⟨y, ?_⟩, fun y hy => ⟨y, 0, hy, ?_⟩⟩
  · rwa [K.M0.map_id] at h
  · exact K.M0.map_id T y
  · rw [K.M1.map_id] at h; exact h.symm
  · rw [K.M1.map_id, map_zero, add_zero]
  · rw [K.M2.map_id] at h; exact h.symm
  · rw [K.M2.map_id, map_zero, add_zero]

theorem qAt_comp {T T' T'' : C} (a : T ⟶ T') (b : T' ⟶ T'') (ha : K.QAt a) (hb : K.QAt b) :
    K.QAt (a ≫ b) := by
  refine ⟨fun x hx h => ?_, fun y hy => ?_, fun x y hx h => ?_, fun y hy => ?_,
    fun x y hx h => ?_, fun y hy => ?_⟩
  · rw [K.M0.map_comp] at h
    exact ha.inj0 x hx (hb.inj0 _ (by rw [K.diffZero_natural, hx, map_zero]) h)
  · obtain ⟨x', hx', rfl⟩ := hb.surj0 y hy
    obtain ⟨x, hx, rfl⟩ := ha.surj0 x' hx'
    exact ⟨x, hx, K.M0.map_comp a b x⟩
  · rw [K.M1.map_comp] at h
    obtain ⟨w', hw'⟩ := hb.inj1 _ y (by rw [K.diffOne_natural, hx, map_zero]) h
    exact ha.inj1 x w' hx hw'.symm
  · obtain ⟨x', w', hx', rfl⟩ := hb.surj1 y hy
    obtain ⟨x, w, hx, rfl⟩ := ha.surj1 x' hx'
    refine ⟨x, K.M0.map b w + w', hx, ?_⟩
    simp only [map_add, K.M1.map_comp, K.diffZero_natural]
    abel
  · rw [K.M2.map_comp] at h
    obtain ⟨w', hw'⟩ := hb.inj2 _ y (by rw [K.diffTwo_natural, hx, map_zero]) h
    exact ha.inj2 x w' hx hw'.symm
  · obtain ⟨x', w', hx', rfl⟩ := hb.surj2 y hy
    obtain ⟨x, w, hx, rfl⟩ := ha.surj2 x' hx'
    refine ⟨x, K.M1.map b w + w', hx, ?_⟩
    simp only [map_add, K.M2.map_comp, K.diffOne_natural]
    abel

theorem qAt_of_comp_retract {T T' T'' : C} (a : T ⟶ T') (b : T' ⟶ T'') (c : T'' ⟶ T')
    (hbc : b ≫ c = 𝟙 T') (h : K.QAt (a ≫ b)) : K.QAt a := by
  have e0 : ∀ y, K.M0.map c (K.M0.map b y) = y := fun y => by
    rw [← K.M0.map_comp, hbc, K.M0.map_id]
  have e1 : ∀ y, K.M1.map c (K.M1.map b y) = y := fun y => by
    rw [← K.M1.map_comp, hbc, K.M1.map_id]
  have e2 : ∀ y, K.M2.map c (K.M2.map b y) = y := fun y => by
    rw [← K.M2.map_comp, hbc, K.M2.map_id]
  refine ⟨fun x hx hax => ?_, fun y hy => ?_, fun x y hx hxy => ?_, fun y hy => ?_,
    fun x y hx hxy => ?_, fun y hy => ?_⟩
  · exact h.inj0 x hx (by rw [K.M0.map_comp, hax, map_zero])
  · obtain ⟨x, hx, hxy⟩ := h.surj0 (K.M0.map b y) (by rw [K.diffZero_natural, hy, map_zero])
    refine ⟨x, hx, ?_⟩
    rw [K.M0.map_comp] at hxy
    simpa only [e0] using congrArg (K.M0.map c) hxy
  · exact h.inj1 x (K.M0.map b y) hx (by rw [K.M1.map_comp, hxy, K.diffZero_natural])
  · obtain ⟨x, w, hx, hw⟩ := h.surj1 (K.M1.map b y) (by rw [K.diffOne_natural, hy, map_zero])
    refine ⟨x, K.M0.map c w, hx, ?_⟩
    have := congrArg (K.M1.map c) hw
    rw [map_add, K.M1.map_comp, e1, e1, ← K.diffZero_natural] at this
    exact this
  · exact h.inj2 x (K.M1.map b y) hx (by rw [K.M2.map_comp, hxy, K.diffOne_natural])
  · obtain ⟨x, w, hx, hw⟩ := h.surj2 (K.M2.map b y) (by rw [K.diffTwo_natural, hy, map_zero])
    refine ⟨x, K.M1.map c w, hx, ?_⟩
    have := congrArg (K.M2.map c) hw
    rw [map_add, K.M2.map_comp, e2, e2, ← K.diffOne_natural] at this
    exact this

theorem qAt_of_isIso {T T' : C} (a : T ⟶ T') [IsIso a] : K.QAt a :=
  qAt_of_comp_retract K a (inv a) a (IsIso.inv_hom_id a) (by rw [IsIso.hom_inv_id]; exact qAt_ident K T)

theorem qAt_formal : ∀ (C : Type 1) [Category.{0} C] (K : Cx C),
    (∀ (T T' : C) (a : T ⟶ T') [IsIso a], K.QAt a) ∧
    (∀ (T T' T'' : C) (a : T ⟶ T') (b : T' ⟶ T''), K.QAt a → K.QAt b → K.QAt (a ≫ b)) ∧
    ∀ (T T' T'' : C) (a : T ⟶ T') (b : T' ⟶ T'') (c : T'' ⟶ T'), b ≫ c = 𝟙 T' → K.QAt (a ≫ b) → K.QAt a :=
  fun _ _ K => ⟨fun _ _ a _ => qAt_of_isIso K a, fun _ _ _ a b => qAt_comp K a b,
    fun _ _ _ a b c => qAt_of_comp_retract K a b c⟩

end GlobalTheory.CxCoh.QAtFormal
