import Mathlib
import GroundTheory.FunctionField.PlaceDefs
import GroundTheory.FunctionField.PlaceBasic
import GroundTheory.FunctionField.Approximation
import GroundTheory.FunctionField.Divisor
import GroundTheory.FunctionField.DivisorDegree
import GroundTheory.FunctionField.Repartition
import GroundTheory.FunctionField.ExistsBoundDegSubFinrankL

namespace GroundTheory.FunctionField

open Module Repartition

variable {k K : Type*} [Field k] [Field K] [Algebra k K] [IsFunctionField k K]

namespace Divisor

theorem mul_mem_A {x : K} (hx : x ≠ 0) {E : Divisor k K} {a : Repartition k K} (ha : a ∈ A E) :
    Repartition.mul x a ∈ A (E - divisor x) := by
  intro v
  rw [Repartition.mul_apply, map_mul, v.valuation_eq_exp_neg_ord hx]
  calc WithZero.exp (-v.ord x) * v.valuation (a v)
      ≤ WithZero.exp (-v.ord x) * WithZero.exp (E v) := mul_le_mul' le_rfl (ha v)
    _ = WithZero.exp ((E - divisor x : Divisor k K) v) := by
      rw [← WithZero.exp_add, Finsupp.coe_sub, Pi.sub_apply, divisor_apply]
      congr 1
      ring

theorem A_sup_le (D E : Divisor k K) : A (D ⊔ E) ≤ A D ⊔ A E := by
  classical
  intro a ha
  let f : Place k K → K := fun v => if E v ≤ D v then a v else 0
  have hf : {v : Place k K | f v ∉ v.ring}.Finite :=
    a.finite_not_mem.subset fun v (hv : f v ∉ v.ring) => by
      show a v ∉ v.ring
      intro h
      apply hv
      simp only [f]
      split_ifs
      · exact h
      · exact v.ring.zero_mem
  let b := Repartition.mk f hf
  have hb : b ∈ A D := by
    intro v
    change v.valuation (f v) ≤ _
    simp only [f]
    split_ifs with h
    · have := ha v
      rwa [Finsupp.sup_apply, sup_of_le_left h] at this
    · rw [map_zero]; exact zero_le
  have hc : a - b ∈ A E := by
    intro v
    rw [Repartition.sub_apply]
    change v.valuation (a v - f v) ≤ _
    simp only [f]
    split_ifs with h
    · rw [sub_self, map_zero]; exact zero_le
    · rw [sub_zero]
      have := ha v
      rwa [Finsupp.sup_apply, sup_of_le_right (not_le.1 h).le] at this
  have : a = b + (a - b) := by abel
  rw [this]
  exact Submodule.add_mem_sup hb hc

noncomputable def weilSpace (D : Divisor k K) : Submodule k (Module.Dual k (Repartition k K)) :=
  (A D ⊔ principal k K).dualAnnihilator

theorem mem_weilSpace {D : Divisor k K} {ω : Module.Dual k (Repartition k K)} :
    ω ∈ weilSpace D ↔ (∀ a ∈ A D, ω a = 0) ∧ ∀ x : K, ω (diag x) = 0 := by
  rw [weilSpace, Submodule.mem_dualAnnihilator]
  constructor
  · intro h
    exact ⟨fun a ha => h a (Submodule.mem_sup_left ha),
      fun x => h _ (Submodule.mem_sup_right (diag_mem_principal x))⟩
  · rintro ⟨h1, h2⟩ a ha
    obtain ⟨b, hb, c, ⟨x, rfl⟩, rfl⟩ := Submodule.mem_sup.1 ha
    rw [map_add, h1 b hb, h2 x, add_zero]

theorem weilSpace_anti {D E : Divisor k K} (h : D ≤ E) : weilSpace E ≤ weilSpace D :=
  Submodule.dualAnnihilator_anti (sup_le_sup_right (A_mono h) _)

theorem weilSpace_sup {D E : Divisor k K} {ω : Module.Dual k (Repartition k K)}
    (hD : ω ∈ weilSpace D) (hE : ω ∈ weilSpace E) : ω ∈ weilSpace (D ⊔ E) := by
  rw [mem_weilSpace] at hD hE ⊢
  refine ⟨fun a ha => ?_, hD.2⟩
  obtain ⟨b, hb, c, hc, rfl⟩ := Submodule.mem_sup.1 (A_sup_le D E ha)
  rw [map_add, hD.1 b hb, hE.1 c hc, add_zero]

instance (D : Divisor k K) : FiniteDimensional k (weilSpace D) :=
  Module.Finite.equiv (Submodule.dualQuotEquivDualAnnihilator (A D ⊔ principal k K))

theorem finrank_weilSpace (D : Divisor k K) : finrank k (weilSpace D) = indexOfSpeciality D := by
  change finrank k (A D ⊔ principal k K).dualAnnihilator = _
  rw [indexOfSpeciality,
    ← (Submodule.dualQuotEquivDualAnnihilator (A D ⊔ principal k K)).finrank_eq,
    Subspace.dual_finrank_eq]

theorem exists_indexOfSpeciality_eq_zero :
    ∃ c : ℤ, ∀ D : Divisor k K, c ≤ deg D → indexOfSpeciality D = 0 := by
  obtain ⟨E₀, hE₀⟩ := exists_eq_genusInt (k := k) (K := K)
  refine ⟨deg E₀ + genusInt k K, fun D hD => ?_⟩
  have h1 := le_genusInt (D - E₀)
  rw [map_sub] at h1
  have hpos : 0 < finrank k (L (D - E₀)) := by
    have : (0 : ℤ) < finrank k (L (D - E₀)) := by linarith
    exact_mod_cast this
  obtain ⟨z, hz⟩ := finrank_pos_iff_exists_ne_zero.1 hpos
  have hz0 : (z : K) ≠ 0 := fun h => hz (Subtype.ext h)
  have hzL := (mem_L_iff_le hz0).1 z.2
  have hle : E₀ ≤ D + divisor (z : K) := by
    rw [← sub_nonneg]
    convert hzL using 1
    abel
  have hD' := eq_genusInt_of_le hE₀ hle
  rw [finrank_L_add_divisor D hz0, map_add, deg_divisor, add_zero] at hD'
  have hi := indexOfSpeciality_eq_genusInt D
  have : (indexOfSpeciality D : ℤ) = 0 := by linarith
  exact_mod_cast this

theorem exists_indexOfSpeciality_pos : ∃ D : Divisor k K, 0 < indexOfSpeciality D := by
  obtain ⟨P⟩ := Place.nonempty (k := k) (K := K)
  set N : ℕ := (2 - genusInt k K).toNat with hN
  refine ⟨-(N • Finsupp.single P 1), ?_⟩
  have h := indexOfSpeciality_eq_genusInt (-(N • Finsupp.single P 1) : Divisor k K)
  have hdeg : deg (-(N • Finsupp.single P 1) : Divisor k K) = -(N * P.deg) := by
    rw [map_neg, map_nsmul, deg_single, nsmul_eq_mul, one_mul]
  have hP : (1 : ℤ) ≤ P.deg := by exact_mod_cast P.deg_pos
  have hN' : (2 : ℤ) - genusInt k K ≤ N := Int.self_le_toNat _
  have hl : (0 : ℤ) ≤ finrank k (L (-(N • Finsupp.single P 1) : Divisor k K)) := Nat.cast_nonneg _
  have hN0 : (0 : ℤ) ≤ N := Nat.cast_nonneg _
  have : (1 : ℤ) ≤ indexOfSpeciality (-(N • Finsupp.single P 1) : Divisor k K) := by
    rw [h, hdeg]
    nlinarith
  exact_mod_cast this

end Divisor

open Divisor

variable (k K) in

def weilDifferentials : Submodule k (Module.Dual k (Repartition k K)) where
  carrier := {ω | ∃ D : Divisor k K, ω ∈ weilSpace D}
  add_mem' := by
    rintro ω₁ ω₂ ⟨D₁, h₁⟩ ⟨D₂, h₂⟩
    exact ⟨D₁ ⊓ D₂, add_mem (weilSpace_anti inf_le_left h₁) (weilSpace_anti inf_le_right h₂)⟩
  zero_mem' := ⟨0, zero_mem _⟩
  smul_mem' := by
    rintro c ω ⟨D, h⟩
    exact ⟨D, Submodule.smul_mem _ c h⟩

variable (k K) in

def WeilDifferential : Type _ := weilDifferentials k K

namespace WeilDifferential

instance : AddCommGroup (WeilDifferential k K) :=
  inferInstanceAs (AddCommGroup (weilDifferentials k K))

instance : Module k (WeilDifferential k K) := inferInstanceAs (Module k (weilDifferentials k K))

def toDual : WeilDifferential k K →ₗ[k] Module.Dual k (Repartition k K) :=
  (weilDifferentials k K).subtype

theorem toDual_injective : Function.Injective (toDual (k := k) (K := K)) :=
  Subtype.val_injective

def mk (ω : Module.Dual k (Repartition k K)) (h : ∃ D : Divisor k K, ω ∈ weilSpace D) :
    WeilDifferential k K :=
  (⟨ω, h⟩ : weilDifferentials k K)

@[simp]
theorem toDual_mk (ω : Module.Dual k (Repartition k K)) (h : ∃ D : Divisor k K, ω ∈ weilSpace D) :
    toDual (mk ω h) = ω :=
  rfl

theorem exists_mem (ω : WeilDifferential k K) : ∃ D : Divisor k K, toDual ω ∈ weilSpace D :=
  (show weilDifferentials k K from ω).2

theorem exists_comp_mul_mem (ω : WeilDifferential k K) (x : K) :
    ∃ D : Divisor k K, toDual ω ∘ₗ Repartition.mul x ∈ weilSpace D := by
  obtain ⟨D, hD⟩ := ω.exists_mem
  by_cases hx : x = 0
  · refine ⟨0, ?_⟩
    have : Repartition.mul (0 : K) = (0 : Repartition k K →ₗ[k] Repartition k K) := by
      ext a v
      simp
    rw [hx, this, LinearMap.comp_zero]
    exact zero_mem _
  · refine ⟨D + divisor x, ?_⟩
    rw [mem_weilSpace] at hD ⊢
    refine ⟨fun a ha => ?_, fun y => ?_⟩
    · rw [LinearMap.comp_apply]
      apply hD.1
      have := mul_mem_A hx ha
      rwa [add_sub_cancel_right] at this
    · rw [LinearMap.comp_apply, Repartition.mul_diag]
      exact hD.2 _

noncomputable instance : SMul K (WeilDifferential k K) :=
  ⟨fun x ω => mk (toDual ω ∘ₗ Repartition.mul x) (exists_comp_mul_mem ω x)⟩

@[simp]
theorem toDual_smul_apply (x : K) (ω : WeilDifferential k K) (a : Repartition k K) :
    toDual (x • ω) a = toDual ω (Repartition.mul x a) :=
  rfl

theorem mul_add_left (x y : K) (a : Repartition k K) :
    Repartition.mul (x + y) a = Repartition.mul x a + Repartition.mul y a := by
  ext v
  simp [add_mul]

noncomputable instance : Module K (WeilDifferential k K) :=
  Module.ofMinimalAxioms
    (fun x ω₁ ω₂ => toDual_injective <| LinearMap.ext fun a => by simp)
    (fun x y ω => toDual_injective <| LinearMap.ext fun a => by simp [mul_add_left])
    (fun x y ω => toDual_injective <| LinearMap.ext fun a => by
      simp only [toDual_smul_apply]
      rw [mul_comm x y, Repartition.mul_mul])
    (fun ω => toDual_injective <| LinearMap.ext fun a => by
      simp only [toDual_smul_apply]
      rw [Repartition.mul_one'])

theorem algebraMap_smul (c : k) (ω : WeilDifferential k K) : algebraMap k K c • ω = c • ω := by
  apply toDual_injective
  ext a
  rw [toDual_smul_apply, map_smul, LinearMap.smul_apply, ← map_smul]
  congr 1
  ext v
  simp

theorem smul_smul_scalar (c : k) (y : K) (ω : WeilDifferential k K) :
    (c • y) • ω = c • (y • ω) := by
  rw [Algebra.smul_def, mul_smul, algebraMap_smul]

noncomputable def weilMap (ω : WeilDifferential k K) : K →ₗ[k] Module.Dual k (Repartition k K) where
  toFun y := toDual (y • ω)
  map_add' y z := by rw [add_smul, map_add]
  map_smul' c y := by rw [smul_smul_scalar, map_smul, RingHom.id_apply]

@[simp]
theorem weilMap_apply (ω : WeilDifferential k K) (y : K) : weilMap ω y = toDual (y • ω) :=
  rfl

theorem smul_mem_weilSpace_iff {x : K} (hx : x ≠ 0) (ω : WeilDifferential k K) (D : Divisor k K) :
    toDual (x • ω) ∈ weilSpace D ↔ toDual ω ∈ weilSpace (D - divisor x) := by
  rw [mem_weilSpace, mem_weilSpace]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun b hb => ?_, fun y => ?_⟩
    · have hb' : Repartition.mul x⁻¹ b ∈ A D := by
        have := mul_mem_A (inv_ne_zero hx) hb
        rwa [divisor_inv, sub_neg_eq_add, sub_add_cancel] at this
      have := h1 _ hb'
      rwa [toDual_smul_apply, ← Repartition.mul_mul, mul_inv_cancel₀ hx,
        Repartition.mul_one'] at this
    · have := h2 (x⁻¹ * y)
      rwa [toDual_smul_apply, Repartition.mul_diag, ← _root_.mul_assoc, mul_inv_cancel₀ hx,
        one_mul] at this
  · rintro ⟨h1, h2⟩
    refine ⟨fun a ha => ?_, fun y => ?_⟩
    · rw [toDual_smul_apply]
      exact h1 _ (mul_mem_A hx ha)
    · rw [toDual_smul_apply, Repartition.mul_diag]
      exact h2 _

theorem exists_ne_zero : ∃ ω : WeilDifferential k K, ω ≠ 0 := by
  obtain ⟨D, hD⟩ := exists_indexOfSpeciality_pos (k := k) (K := K)
  rw [← finrank_weilSpace] at hD
  have hne : weilSpace D ≠ ⊥ := by
    intro h
    rw [h] at hD
    simp at hD
  obtain ⟨φ, hφmem, hφ⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  refine ⟨mk φ ⟨D, hφmem⟩, fun h => hφ ?_⟩
  have := congrArg toDual h
  rwa [toDual_mk, map_zero] at this

noncomputable def toQuotDual (D : Divisor k K) :
    weilSpace D ≃ₗ[k] Module.Dual k (Repartition k K ⧸ (A D ⊔ principal k K)) :=
  (Submodule.dualQuotEquivDualAnnihilator (A D ⊔ principal k K)).symm

theorem exists_smul_eq {ω₁ : WeilDifferential k K} (h₁ : ω₁ ≠ 0) (ω₂ : WeilDifferential k K) :
    ∃ x : K, x • ω₁ = ω₂ := by
  classical
  by_contra hcon
  push Not at hcon
  obtain ⟨D₁, hD₁⟩ := ω₁.exists_mem
  obtain ⟨D₂, hD₂⟩ := ω₂.exists_mem
  obtain ⟨P⟩ := Place.nonempty (k := k) (K := K)
  set s := genusInt k K with hs
  set N : ℕ := (3 * s - deg D₁ - deg D₂).toNat + 1 with hN
  set B : Divisor k K := N • Finsupp.single P 1 with hB
  have hmem : ∀ {ω : WeilDifferential k K} {D : Divisor k K}, toDual ω ∈ weilSpace D →
      ∀ y ∈ L (B + D), weilMap ω y ∈ weilSpace (-B) := by
    intro ω D hD y hy
    rw [weilMap_apply]
    by_cases hy0 : y = 0
    · rw [hy0, zero_smul, map_zero]
      exact zero_mem _
    rw [smul_mem_weilSpace_iff hy0]
    refine weilSpace_anti ?_ hD
    have := (mem_L_iff_le hy0).1 hy
    rw [← sub_nonneg]
    convert this using 1
    abel
  let Φ₀ : L (B + D₁) × L (B + D₂) →ₗ[k] Module.Dual k (Repartition k K) :=
    ((weilMap ω₁) ∘ₗ (L (B + D₁)).subtype).coprod ((weilMap ω₂) ∘ₗ (L (B + D₂)).subtype)
  have hΦ₀ : ∀ p, Φ₀ p ∈ weilSpace (-B) := fun p =>
    add_mem (hmem hD₁ _ p.1.2) (hmem hD₂ _ p.2.2)
  have hΦ₀inj : Function.Injective Φ₀ := by
    refine (injective_iff_map_eq_zero Φ₀).2 ?_
    rintro ⟨⟨y, hy⟩, ⟨z, hz⟩⟩ hp
    have hsum : y • ω₁ + z • ω₂ = 0 := by
      apply toDual_injective
      rw [map_add, map_zero]
      exact hp
    by_cases hz0 : z = 0
    · subst hz0
      rw [zero_smul, add_zero, smul_eq_zero] at hsum
      rcases hsum with rfl | h
      · rfl
      · exact absurd h h₁
    · exfalso
      apply hcon (-(y / z))
      have h' : z • ω₂ = -(y • ω₁) := eq_neg_of_add_eq_zero_right hsum
      have e : (-(y / z)) • ω₁ = z⁻¹ • (z • ω₂) := by
        rw [h', smul_neg, smul_smul, neg_smul, div_eq_inv_mul]
      rw [e, smul_smul, inv_mul_cancel₀ hz0, one_smul]
  let Φ := (toQuotDual (-B)).toLinearMap ∘ₗ LinearMap.codRestrict (weilSpace (-B)) Φ₀ hΦ₀
  have hΦ : Function.Injective Φ :=
    (toQuotDual (-B)).injective.comp fun p q h => hΦ₀inj (congrArg Subtype.val h)
  have hfin := LinearMap.finrank_le_finrank_of_injective hΦ
  rw [Module.finrank_prod, Subspace.dual_finrank_eq] at hfin
  change _ ≤ indexOfSpeciality (-B) at hfin
  have hi := indexOfSpeciality_eq_genusInt (-B)
  have hP : (1 : ℤ) ≤ P.deg := by exact_mod_cast P.deg_pos
  have hdegB : deg B = N * P.deg := by rw [hB, map_nsmul, deg_single, nsmul_eq_mul, one_mul]
  have hNb : 3 * s - deg D₁ - deg D₂ + 1 ≤ (N : ℤ) := by
    have := Int.self_le_toNat (3 * s - deg D₁ - deg D₂)
    rw [hN]
    push_cast
    linarith
  have hN0 : (0 : ℤ) ≤ N := Nat.cast_nonneg _
  have hBN : (N : ℤ) ≤ deg B := by rw [hdegB]; nlinarith
  have hl0 : finrank k (L (-B)) = 0 := by
    rw [L_eq_bot_of_deg_neg (by rw [map_neg]; linarith)]
    simp
  have h1 := le_genusInt (B + D₁)
  have h2 := le_genusInt (B + D₂)
  rw [map_add] at h1 h2
  rw [hl0, map_neg] at hi
  have : ((finrank k (L (B + D₁)) + finrank k (L (B + D₂)) : ℕ) : ℤ) ≤
      indexOfSpeciality (-B) := by exact_mod_cast hfin
  push_cast at this hi
  rw [← hs] at h1 h2 hi
  linarith

theorem exists_deg_lt {ω : WeilDifferential k K} (hω : ω ≠ 0) :
    ∃ c : ℤ, ∀ D : Divisor k K, toDual ω ∈ weilSpace D → deg D < c := by
  obtain ⟨c, hc⟩ := exists_indexOfSpeciality_eq_zero (k := k) (K := K)
  refine ⟨c, fun D hD => ?_⟩
  by_contra hle
  push Not at hle
  have h0 : finrank k (Repartition k K ⧸ (A D ⊔ principal k K)) = 0 := hc D hle
  have hsub : Subsingleton (Repartition k K ⧸ (A D ⊔ principal k K)) :=
    Module.finrank_zero_iff.1 h0
  have h1 : toQuotDual D ⟨toDual ω, hD⟩ = 0 :=
    LinearMap.ext fun q => by simp [Subsingleton.elim q 0]
  have h2 : (⟨toDual ω, hD⟩ : weilSpace D) = 0 :=
    (toQuotDual D).injective (by rw [h1, map_zero])
  exact hω (toDual_injective (by rw [map_zero]; exact congrArg Subtype.val h2))

theorem exists_divisor {ω : WeilDifferential k K} (hω : ω ≠ 0) :
    ∃ W : Divisor k K, ∀ D : Divisor k K, toDual ω ∈ weilSpace D ↔ D ≤ W := by
  classical
  obtain ⟨c, hc⟩ := exists_deg_lt hω
  obtain ⟨D₀, hD₀⟩ := ω.exists_mem
  obtain ⟨n, ⟨W, hW, rfl⟩, hmax⟩ :=
    Int.exists_greatest_of_bdd (P := fun n => ∃ D, toDual ω ∈ weilSpace D ∧ deg D = n)
      ⟨c, fun n ⟨D, hD, hn⟩ => hn ▸ (hc D hD).le⟩ ⟨deg D₀, D₀, hD₀, rfl⟩
  refine ⟨W, fun D => ⟨fun hD => ?_, fun h => weilSpace_anti h hW⟩⟩
  have hsup := weilSpace_sup hD hW
  have h1 := hmax _ ⟨_, hsup, rfl⟩
  have h2 : 0 ≤ (D ⊔ W) - W := sub_nonneg.2 le_sup_right
  have h3 : deg ((D ⊔ W) - W) = 0 := by
    have := deg_nonneg h2
    rw [map_sub] at this ⊢
    linarith
  have h4 := eq_zero_of_deg_eq_zero h2 h3
  have : D ⊔ W = W := sub_eq_zero.1 h4
  rw [← this]
  exact le_sup_left

open Classical in

noncomputable def divisor (ω : WeilDifferential k K) : Divisor k K :=
  if h : ω = 0 then 0 else Classical.choose (exists_divisor h)

theorem mem_weilSpace_iff_le_divisor {ω : WeilDifferential k K} (hω : ω ≠ 0) (D : Divisor k K) :
    toDual ω ∈ weilSpace D ↔ D ≤ ω.divisor := by
  rw [divisor, dif_neg hω]
  exact Classical.choose_spec (exists_divisor hω) D

theorem smul_mem_weilSpace_iff_mem_L {ω : WeilDifferential k K} (hω : ω ≠ 0) (D : Divisor k K)
    (y : K) : toDual (y • ω) ∈ weilSpace D ↔ y ∈ L (ω.divisor - D) := by
  by_cases hy : y = 0
  · rw [hy, zero_smul, map_zero]
    exact ⟨fun _ => zero_mem _, fun _ => zero_mem _⟩
  rw [smul_mem_weilSpace_iff hy, mem_weilSpace_iff_le_divisor hω, mem_L_iff_le hy,
    ← sub_nonneg]
  constructor <;> intro h <;> convert h using 1 <;> abel

noncomputable def dualityEquiv {ω : WeilDifferential k K} (hω : ω ≠ 0) (D : Divisor k K) :
    L (ω.divisor - D) ≃ₗ[k] Module.Dual k (Repartition k K ⧸ (A D ⊔ principal k K)) :=
  LinearEquiv.ofBijective
    ((toQuotDual D).toLinearMap ∘ₗ LinearMap.codRestrict (weilSpace D)
      ((weilMap ω) ∘ₗ (L (ω.divisor - D)).subtype)
      (fun y => (smul_mem_weilSpace_iff_mem_L hω D y).2 y.2))
    ⟨(toQuotDual D).injective.comp fun y z h => by
        have h' : toDual ((y : K) • ω) = toDual ((z : K) • ω) := by
          have := congrArg Subtype.val h
          exact this
        exact Subtype.ext (smul_left_injective K hω (toDual_injective h')),
      fun f => by
        set φ := (toQuotDual D).symm f with hφ
        obtain ⟨y, hy⟩ := exists_smul_eq hω (mk (φ : Module.Dual k (Repartition k K)) ⟨D, φ.2⟩)
        have hyD : toDual (y • ω) = φ := by rw [hy, toDual_mk]
        have hyL : y ∈ L (ω.divisor - D) :=
          (smul_mem_weilSpace_iff_mem_L hω D y).1 (hyD ▸ φ.2)
        refine ⟨⟨y, hyL⟩, ?_⟩
        have : LinearMap.codRestrict (weilSpace D) ((weilMap ω) ∘ₗ (L (ω.divisor - D)).subtype)
            (fun y => (smul_mem_weilSpace_iff_mem_L hω D y).2 y.2) ⟨y, hyL⟩ = φ :=
          Subtype.ext hyD
        rw [LinearMap.comp_apply, this, hφ, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]⟩

end WeilDifferential

end GroundTheory.FunctionField
