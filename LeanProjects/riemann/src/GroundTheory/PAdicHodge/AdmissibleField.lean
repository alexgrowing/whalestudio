import Mathlib
import GroundTheory.PAdicHodge.Admissible
set_option maxSynthPendingDepth 1

namespace GroundTheory.PAdicHodge

open TensorProduct Module

section Field

variable (G F B : Type*) [Group G] [Field F] [Field B] [Algebra F B] [MulSemiringAction G B]

theorem isRegular_of_field : IsRegular G F B where
  image_fixedPoints := by
    let := IsFractionRing.mulSemiringAction G B (FractionRing B)
    have hmap : ∀ (g : G) (b : B), g • algebraMap B (FractionRing B) b =
        algebraMap B (FractionRing B) (g • b) := fun g b =>
      IsFractionRing.ringEquivOfRingEquiv_algebraMap _ b
    have hinj := IsFractionRing.injective B (FractionRing B)
    ext y
    constructor
    · rintro ⟨b, hb, rfl⟩ g
      rw [hmap, hb g]
    · intro hy
      obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective (nonZeroDivisors B) y
      have hs : (s : B) ≠ 0 := nonZeroDivisors.ne_zero s.2
      have e : IsLocalization.mk' (FractionRing B) a s =
          algebraMap B (FractionRing B) (a * (s : B)⁻¹) := by
        rw [IsLocalization.mk'_eq_iff_eq_mul, ← map_mul, mul_assoc, inv_mul_cancel₀ hs, mul_one]
      refine ⟨a * (s : B)⁻¹, fun g => hinj ?_, e.symm⟩
      rw [← hmap, ← e]
      exact hy g
  isUnit_of_mem_span b hb _ := hb.isUnit

end Field

section Coeff

variable (G F K B : Type*) [Group G] [Field F] [Field K] [CommRing B] [Algebra F K] [Algebra K B]
  [Algebra F B] [IsScalarTower F K B] [MulSemiringAction G B] [SMulCommClass G F B]
  [SMulCommClass G K B]
variable {V : Type*} [AddCommGroup V] [Module F V] (ρ : Representation F G V)

def DBK : Submodule K (B ⊗[F] V) where
  carrier := {x | ∀ g : G, baseChangeRep B ρ g x = x}
  add_mem' {x y} hx hy g := by rw [map_add, hx g, hy g]
  zero_mem' g := map_zero _
  smul_mem' k x hx g := by
    change baseChangeRep B ρ g (k • x) = k • x
    rw [← algebraMap_smul B k x, baseChangeRep_smul, hx g, smul_algebraMap]

variable {G F K B ρ} in
theorem mem_DBK {x : B ⊗[F] V} : x ∈ DBK G F K B ρ ↔ ∀ g : G, baseChangeRep B ρ g x = x :=
  Iff.rfl

theorem coe_DBK : (DBK G F K B ρ : Set (B ⊗[F] V)) = DB B ρ := rfl

def toInvariantRing : K →+* invariantRing G F B where
  toFun k := ⟨algebraMap K B k, fun g => smul_algebraMap g k⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' a b := Subtype.ext (map_mul _ a b)
  map_zero' := Subtype.ext (map_zero _)
  map_add' a b := Subtype.ext (map_add _ a b)

variable {G F K B}

omit [Algebra F K] [IsScalarTower F K B] in
@[simp]
theorem coe_toInvariantRing (k : K) : (toInvariantRing G F K B k : B) = algebraMap K B k := rfl

omit [Algebra F K] [IsScalarTower F K B] in
theorem toInvariantRing_bijective [Nontrivial B]
    (hK : ∀ b : B, (∀ g : G, g • b = b) → ∃ k : K, algebraMap K B k = b) :
    Function.Bijective (toInvariantRing G F K B) := by
  refine ⟨fun a b hab => (algebraMap K B).injective ?_, fun e => ?_⟩
  · simpa using congrArg Subtype.val hab
  · obtain ⟨k, hk⟩ := hK e e.2
    exact ⟨k, Subtype.ext hk⟩

theorem invariantRing_eq_range
    (hK : ∀ b : B, (∀ g : G, g • b = b) → ∃ k : K, algebraMap K B k = b) :
    invariantRing G F B = (IsScalarTower.toAlgHom F K B).range := by
  ext b
  constructor
  · intro hb
    obtain ⟨k, hk⟩ := hK b hb
    exact ⟨k, hk⟩
  · rintro ⟨k, rfl⟩ g
    exact smul_algebraMap g k

theorem rank_DBK [Nontrivial B]
    (hK : ∀ b : B, (∀ g : G, g • b = b) → ∃ k : K, algebraMap K B k = b) :
    Module.rank K (DBK G F K B ρ) = Module.rank (invariantRing G F B) (DB B ρ) := by
  let j : DBK G F K B ρ ≃+ DB B ρ :=
    { toFun := fun x => ⟨x, x.2⟩
      invFun := fun x => ⟨x, x.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl }
  refine rank_eq_of_equiv_equiv (toInvariantRing G F K B) j (toInvariantRing_bijective hK) ?_
  intro k x
  apply Subtype.ext
  change k • (x : B ⊗[F] V) =
    ((toInvariantRing G F K B k : invariantRing G F B) : B) • (x : B ⊗[F] V)
  rw [coe_toInvariantRing, algebraMap_smul]

theorem finrank_DBK [Nontrivial B]
    (hK : ∀ b : B, (∀ g : G, g • b = b) → ∃ k : K, algebraMap K B k = b) :
    finrank K (DBK G F K B ρ) = finrank (invariantRing G F B) (DB B ρ) := by
  simp only [Module.finrank, rank_DBK ρ hK]

variable [IsDomain B]

theorem IsRegular.finiteDimensional_DBK (h : IsRegular G F B)
    (hK : ∀ b : B, (∀ g : G, g • b = b) → ∃ k : K, algebraMap K B k = b) [FiniteDimensional F V] :
    FiniteDimensional K (DBK G F K B ρ) := by
  let := h.field
  have := h.free ρ
  have := h.finite ρ
  have : Module.Free K (DBK G F K B ρ) := Module.Free.of_divisionRing K (DBK G F K B ρ)
  exact Module.rank_lt_aleph0_iff.1 (by rw [rank_DBK ρ hK]; exact Module.rank_lt_aleph0_iff.2 ‹_›)

theorem IsRegular.finrank_DBK_le (h : IsRegular G F B)
    (hK : ∀ b : B, (∀ g : G, g • b = b) → ∃ k : K, algebraMap K B k = b) [FiniteDimensional F V] :
    finrank K (DBK G F K B ρ) ≤ finrank F V := by
  rw [finrank_DBK ρ hK]
  exact h.finrank_le ρ

theorem isAdmissible_iff_finrank_DBK
    (hK : ∀ b : B, (∀ g : G, g • b = b) → ∃ k : K, algebraMap K B k = b) :
    IsAdmissible B ρ ↔ finrank K (DBK G F K B ρ) = finrank F V := by
  rw [finrank_DBK ρ hK]
  rfl

end Coeff

end GroundTheory.PAdicHodge
