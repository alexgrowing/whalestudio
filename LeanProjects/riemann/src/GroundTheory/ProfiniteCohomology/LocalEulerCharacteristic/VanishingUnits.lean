import Mathlib
import GroundTheory.ProfiniteCohomology.LocalEulerCharacteristic.UnitsPower
import GroundTheory.LocalFields.UnitsBasic
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open GroundTheory.LocalField ValuativeRel IsLocalRing

section Group

variable {G : Type*} [CommGroup G]

theorem mul_inv_mem_of_iterate_eq {l m : ℕ} (P O : Subgroup G) (s : G →* G)
    (hPl : ∀ y : G, y ^ l ∈ P) (hO : ∀ x : G, s x * x⁻¹ ∈ O)
    (hOP : ∀ e ∈ O, s e * e⁻¹ ∈ P) (hm : m.Coprime l) (hsm : ∀ x : G, s^[m] x = x) (x : G) :
    s x * x⁻¹ ∈ P := by
  have hPn : P.Normal := Subgroup.normal_of_isMulCommutative P
  have hq : ∀ a b : G, a * b⁻¹ ∈ P → (a : G ⧸ P) = b := fun a b h => by
    rw [QuotientGroup.eq]
    have := P.inv_mem h
    rwa [mul_inv_rev, inv_inv, mul_comm] at this
  set c := s x * x⁻¹ with hc
  have hOs : ∀ e ∈ O, s e ∈ O := fun e he => by
    have := O.mul_mem (hO e) he
    rwa [inv_mul_cancel_right] at this
  have hcO : ∀ j : ℕ, s^[j] c ∈ O := fun j => by
    induction j with
    | zero => exact hO x
    | succ j ih => rw [Function.iterate_succ_apply']; exact hOs _ ih
  have hcj : ∀ j : ℕ, ((s^[j] c : G) : G ⧸ P) = c := fun j => by
    induction j with
    | zero => rfl
    | succ j ih => rw [Function.iterate_succ_apply', hq _ _ (hOP _ (hcO j)), ih]
  have hsx : s x = x * c := by rw [hc, mul_comm (s x), mul_inv_cancel_left]
  have hxj : ∀ j : ℕ, ((s^[j] x : G) : G ⧸ P) = (x : G ⧸ P) * (c : G ⧸ P) ^ j := fun j => by
    induction j with
    | zero => simp
    | succ j ih =>
      rw [Function.iterate_succ_apply, hsx, iterate_map_mul, QuotientGroup.mk_mul, ih,
        hcj, pow_succ, mul_assoc]
  have h1 : (c : G ⧸ P) ^ m = 1 := by
    have h := hxj m
    rw [hsm] at h
    exact mul_left_cancel (h.symm.trans (mul_one _).symm)
  have h2 : (c : G ⧸ P) ^ l = 1 := by
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    exact hPl c
  have h3 : (c : G ⧸ P) = 1 := by
    have h := (pow_gcd_eq_one (a := (c : G ⧸ P))).2 ⟨h1, h2⟩
    rwa [Nat.Coprime.gcd_eq_one hm, pow_one] at h
  exact (QuotientGroup.eq_one_iff c).1 h3

end Group

section LocalField

variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

theorem exists_map_units_eq_mul_pow {l m : ℕ} (hl : (l : 𝓀[F]) ≠ 0) (σ : F ≃+* F)
    (hval : ∀ x : F, valuation F (σ x) = valuation F x)
    (hin : ∀ x : F, valuation F x ≤ 1 → valuation F (σ x - x) < 1)
    (hm : m.Coprime l) (hσm : ∀ x : F, σ^[m] x = x) (u : Fˣ) :
    ∃ y : Fˣ, Units.map (σ : F →* F) u = u * y ^ l := by
  set s : Fˣ →* Fˣ := Units.map (σ : F →* F) with hs_def
  have hs : ∀ x : Fˣ, ((s x : Fˣ) : F) = σ x := fun x => rfl
  let P : Subgroup Fˣ := (powMonoidHom l : Fˣ →* Fˣ).range
  let O : Subgroup Fˣ :=
    { carrier := {x | valuation F (x : F) = 1}
      one_mem' := by simp
      mul_mem' := fun {a b} ha hb => by
        simp only [Set.mem_ofPred_eq, Units.val_mul, map_mul] at ha hb ⊢
        rw [ha, hb, mul_one]
      inv_mem' := fun {a} ha => by
        simp only [Set.mem_ofPred_eq, Units.val_inv_eq_inv_val, map_inv₀] at ha ⊢
        rw [ha, inv_one] }
  have hmemO : ∀ x : Fˣ, x ∈ O ↔ valuation F (x : F) = 1 := fun x => Iff.rfl
  have hv0 : ∀ x : Fˣ, valuation F (x : F) ≠ 0 := fun x => (valuation F).ne_zero_iff.2 x.ne_zero
  have hO : ∀ x : Fˣ, s x * x⁻¹ ∈ O := fun x => by
    rw [hmemO, Units.val_mul, hs, map_mul, Units.val_inv_eq_inv_val, map_inv₀, hval,
      mul_inv_cancel₀ (hv0 x)]
  have hOP : ∀ e ∈ O, s e * e⁻¹ ∈ P := fun e he => by
    rw [hmemO] at he
    set t := s e * e⁻¹ with ht
    have htv : valuation F (t : F) = 1 := (hmemO t).1 (hO e)
    have ht1 : valuation F ((t : F) - 1) < 1 := by
      have e1 : (t : F) - 1 = (σ e - e) * (e : F)⁻¹ := by
        rw [ht, Units.val_mul, hs, Units.val_inv_eq_inv_val, sub_mul,
          mul_inv_cancel₀ e.ne_zero]
      rw [e1, map_mul, map_inv₀, he, inv_one, mul_one]
      exact hin _ he.le
    have hnt : normalizedValuation F (t : F) = 1 := by
      rw [← map_one (normalizedValuation F), normalizedValuation_eq_iff, map_one]
      exact htv
    obtain ⟨t', ht'⟩ := mem_range_unitsIncl_iff.2 hnt
    have ht'F : ((t' : 𝒪[F]) : F) = t := by rw [← coe_unitsIncl, ht']
    have hmem : t' ∈ unitFiltration F 1 := by
      rw [mem_unitFiltration, pow_one, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      intro hu
      have h1 := valuation_unit hu.unit
      rw [IsUnit.unit_spec] at h1
      have h2 : (((t' : 𝒪[F]) - 1 : 𝒪[F]) : F) = (t : F) - 1 := by
        push_cast
        rw [ht'F]
      rw [h2] at h1
      exact (lt_irrefl _ (h1 ▸ ht1))
    obtain ⟨z, -, hz⟩ := exists_pow_eq_of_mem_unitFiltration_one hl hmem
    refine ⟨unitsIncl F z, ?_⟩
    rw [powMonoidHom_apply, ← map_pow, hz, ht']
  have hiter : ∀ (j : ℕ) (x : Fˣ), ((s^[j] x : Fˣ) : F) = σ^[j] (x : F) := fun j => by
    induction j with
    | zero => intro x; rfl
    | succ j ih =>
      intro x
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', hs, ih]
  have hsm : ∀ x : Fˣ, s^[m] x = x := fun x => Units.ext (by rw [hiter, hσm])
  obtain ⟨y, hy⟩ := mul_inv_mem_of_iterate_eq P O s (fun y => ⟨y, rfl⟩) hO hOP hm hsm u
  refine ⟨y, ?_⟩
  rw [powMonoidHom_apply] at hy
  rw [hy, mul_comm (s u), mul_inv_cancel_left]

end LocalField

end GroundTheory.ProfCoh
