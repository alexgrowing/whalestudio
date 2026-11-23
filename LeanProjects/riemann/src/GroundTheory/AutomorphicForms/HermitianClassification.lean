import Mathlib
import GroundTheory.AutomorphicForms.HermitianDisc
import GroundTheory.AutomorphicForms.HermitianWittExtension
import GroundTheory.AutomorphicForms.HermitianSplit
import GroundTheory.LocalFields.HerbrandLocal
import GroundTheory.LocalFields.FiniteExtension
import GroundTheory.LocalFields.UnramifiedHensel

noncomputable section

namespace GroundTheory.Automorphic

open Module GroundTheory.LocalField ValuativeRel IsLocalRing Polynomial

theorem mem_or_mul_inv_mem_of_natCard_eq_two {G : Type*} [CommGroup G] {N : Subgroup G}
    (hN : Nat.card (G ⧸ N) = 2) {t : G} (ht : t ∉ N) (u : G) : u ∈ N ∨ u * t⁻¹ ∈ N := by
  by_contra H
  push Not at H
  obtain ⟨y, -, hy⟩ := (Nat.card_eq_two_iff' (1 : G ⧸ N)).1 hN
  have h1 : (QuotientGroup.mk t : G ⧸ N) ≠ 1 := by rwa [Ne, QuotientGroup.eq_one_iff]
  have h2 : (QuotientGroup.mk u : G ⧸ N) ≠ 1 := by rw [Ne, QuotientGroup.eq_one_iff]; exact H.1
  have h3 := QuotientGroup.eq.1 ((hy _ h1).trans (hy _ h2).symm)
  apply H.2
  rwa [mul_comm]

section General

variable {F E : Type*} [Field F] [Field E] [Algebra F E] [Algebra.IsQuadraticExtension F E]

theorem norm_algebraMap_quadratic (t : F) : Algebra.norm F (algebraMap F E t) = t ^ 2 := by
  rw [Algebra.norm_algebraMap, Algebra.IsQuadraticExtension.finrank_eq_two]

theorem norm_inv_quadratic (z : E) : Algebra.norm F z⁻¹ = (Algebra.norm F z)⁻¹ := by
  by_cases hz : z = 0
  · rw [hz, inv_zero, Algebra.norm_zero, inv_zero]
  · exact eq_inv_of_mul_eq_one_left (by rw [← map_mul, inv_mul_cancel₀ hz, map_one])

theorem mem_range_normUnits_iff (u : Fˣ) :
    u ∈ (normUnits F E).range ↔ ∃ z : E, Algebra.norm F z = u := by
  constructor
  · rintro ⟨w, rfl⟩
    exact ⟨w, (coe_normUnits w).symm⟩
  · rintro ⟨z, hz⟩
    have hz0 : z ≠ 0 := by rintro rfl; rw [Algebra.norm_zero] at hz; exact u.ne_zero hz.symm
    exact ⟨Units.mk0 z hz0, Units.ext (by rw [coe_normUnits, Units.val_mk0, hz])⟩

theorem exists_norm_add_norm_ne (hN : Nat.card (Fˣ ⧸ (normUnits F E).range) = 2)
    (hsq : ∃ m : ℕ, 0 < m ∧ ∃ s : F, s ^ 2 = -(m : F)) :
    ∃ x y : E, ∀ z : E, Algebra.norm F x + Algebra.norm F y ≠ Algebra.norm F z := by
  by_contra H
  push Not at H

  have hmul : ∀ a b : F, (∃ z : E, Algebra.norm F z = a) → (∃ z : E, Algebra.norm F z = b) →
      ∃ z : E, Algebra.norm F z = a * b := by
    rintro a b ⟨z, rfl⟩ ⟨w, rfl⟩
    exact ⟨z * w, map_mul _ _ _⟩
  have hinv : ∀ a : F, (∃ z : E, Algebra.norm F z = a) → ∃ z : E, Algebra.norm F z = a⁻¹ := by
    rintro a ⟨z, rfl⟩
    exact ⟨z⁻¹, norm_inv_quadratic z⟩
  have hadd : ∀ a b : F, (∃ z : E, Algebra.norm F z = a) → (∃ z : E, Algebra.norm F z = b) →
      ∃ z : E, Algebra.norm F z = a + b := by
    rintro a b ⟨z, rfl⟩ ⟨w, rfl⟩
    obtain ⟨u, hu⟩ := H z w
    exact ⟨u, hu.symm⟩
  by_cases hm1 : ∃ w : E, Algebra.norm F w = -1
  ·
    obtain ⟨y, hy1, -⟩ := (Nat.card_eq_two_iff' (1 : Fˣ ⧸ (normUnits F E).range)).1 hN
    obtain ⟨t, rfl⟩ := QuotientGroup.mk_surjective y
    have ht : t ∉ (normUnits F E).range := by rwa [Ne, QuotientGroup.eq_one_iff] at hy1
    have htR : ¬ ∃ z : E, Algebra.norm F z = t := fun H' => ht ((mem_range_normUnits_iff t).2 H')
    have h1t : (1 : F) + t ≠ 0 := by
      intro h0
      apply htR
      obtain ⟨w, hw⟩ := hm1
      exact ⟨w, by rw [hw]; linear_combination -h0⟩
    rcases mem_or_mul_inv_mem_of_natCard_eq_two hN ht (Units.mk0 _ h1t) with h | h
    · obtain ⟨z, hz⟩ := (mem_range_normUnits_iff _).1 h
      apply htR
      obtain ⟨z', hz'⟩ := hadd _ _ ⟨z, hz⟩ hm1
      exact ⟨z', by rw [hz', Units.val_mk0]; ring⟩
    · obtain ⟨z, hz⟩ := (mem_range_normUnits_iff _).1 h
      rw [Units.val_mul, Units.val_mk0, Units.val_inv_eq_inv_val] at hz
      obtain ⟨z', hz'⟩ := hadd _ _ ⟨z, hz⟩ hm1
      obtain ⟨z'', hz''⟩ := hinv _ ⟨z', hz'⟩
      apply htR
      refine ⟨z'', ?_⟩
      rw [hz'']
      have ht0 : (t : F) ≠ 0 := t.ne_zero
      field_simp
      ring
  ·
    have hk : ∀ k : ℕ, ∃ z : E, Algebra.norm F z = ((k + 1 : ℕ) : F) := by
      intro k
      induction k with
      | zero => exact ⟨1, by simp⟩
      | succ k ih =>
        obtain ⟨z, hz⟩ := hadd _ _ ih ⟨1, map_one _⟩
        exact ⟨z, by rw [hz]; push_cast; ring⟩
    obtain ⟨m, hm, s, hs⟩ := hsq
    apply hm1
    by_cases hm0 : (m : F) = 0
    · have hm2 : 2 ≤ m := by
        rcases Nat.lt_or_ge m 2 with h | h
        · interval_cases m; simp at hm0
        · exact h
      obtain ⟨z, hz⟩ := hk (m - 2)
      refine ⟨z, ?_⟩
      rw [hz]
      have : ((m - 2 + 1 : ℕ) : F) = (m : F) - 1 := by
        rw [show m - 2 + 1 = m - 1 by omega, Nat.cast_sub (by omega), Nat.cast_one]
      rw [this, hm0, zero_sub]
    · obtain ⟨z, hz⟩ := hk (m - 1)
      rw [show m - 1 + 1 = m by omega] at hz
      obtain ⟨w, hw⟩ := hinv _ ⟨z, hz⟩
      refine ⟨algebraMap F E s * w, ?_⟩
      rw [map_mul, norm_algebraMap_quadratic, hs, hw]
      field_simp

end General

section Local

variable (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

theorem exists_sq_eq_neg_natCast : ∃ m : ℕ, 0 < m ∧ ∃ s : F, s ^ 2 = -(m : F) := by
  set p := ringChar 𝓀[F]
  have hp : p ≠ 0 := CharP.char_ne_zero_of_finite 𝓀[F] p
  have hpm : (p : 𝒪[F]) ∈ 𝓂[F] := by
    rw [← residue_eq_zero_iff, map_natCast]
    exact ringChar.Nat.cast_ringChar
  set P : 𝒪[F][X] := X ^ 2 + X + C (p : 𝒪[F])
  have hP : P.Monic := by
    simp only [P]
    monicity!
  have h1 : P.eval 0 ∈ 𝓂[F] := by simpa [P] using hpm
  have h2 : IsUnit (P.derivative.eval 0) := by
    simp [P]
  obtain ⟨x, hx, -⟩ := HenselianLocalRing.is_henselian P hP 0 h1 h2
  have hx' : (x : F) ^ 2 + x + p = 0 := by
    have := congrArg (fun y : 𝒪[F] => (y : F)) hx.eq_zero
    simpa [P] using this
  refine ⟨4 * p - 1, by omega, 2 * x + 1, ?_⟩
  rw [Nat.cast_sub (by omega)]
  push_cast
  linear_combination 4 * hx'

variable {F}
variable {E : Type*} [Field E] [Algebra F E] [Algebra.IsQuadraticExtension F E]
  [Algebra.IsSeparable F E]

theorem natCard_quotient_range_normUnits_eq_two :
    Nat.card (Fˣ ⧸ (normUnits F E).range) = 2 := by
  obtain ⟨_, _, _, _⟩ := exists_isNonarchimedeanLocalField_valuativeExtension F E
  rw [natCard_units_quotient_range_normUnits, Algebra.IsQuadraticExtension.finrank_eq_two]

theorem exists_mul_norm_add_mul_norm_eq (a b c : Fˣ) :
    ∃ x y : E, (a : F) * Algebra.norm F x + b * Algebra.norm F y = c := by
  have hN := natCard_quotient_range_normUnits_eq_two (F := F) (E := E)
  set N := (normUnits F E).range
  obtain ⟨x₀, y₀, hxy⟩ := exists_norm_add_norm_ne hN (exists_sq_eq_neg_natCast F)
  obtain ⟨f, hf⟩ : ∃ f, f = Algebra.norm F x₀ + Algebra.norm F y₀ := ⟨_, rfl⟩
  have hf0 : f ≠ 0 := fun h0 => hxy 0 (by rw [Algebra.norm_zero, ← hf]; exact h0)
  have hfN : Units.mk0 f hf0 ∉ N := fun h => by
    obtain ⟨z, hz⟩ := (mem_range_normUnits_iff _).1 h
    exact hxy z (by rw [← hf, hz, Units.val_mk0])
  by_cases hca : c * a⁻¹ ∈ N
  · obtain ⟨z, hz⟩ := (mem_range_normUnits_iff _).1 hca
    refine ⟨z, 0, ?_⟩
    rw [hz, Algebra.norm_zero, mul_zero, add_zero, Units.val_mul, Units.val_inv_eq_inv_val]
    field_simp
  by_cases hcb : c * b⁻¹ ∈ N
  · obtain ⟨z, hz⟩ := (mem_range_normUnits_iff _).1 hcb
    refine ⟨0, z, ?_⟩
    rw [hz, Algebra.norm_zero, mul_zero, zero_add, Units.val_mul, Units.val_inv_eq_inv_val]
    field_simp

  have hba : b * a⁻¹ ∈ N := by
    rcases mem_or_mul_inv_mem_of_natCard_eq_two hN hca (c * b⁻¹) with h | h
    · exact absurd h hcb
    · have h' : c * b⁻¹ * (c * a⁻¹)⁻¹ = (b * a⁻¹)⁻¹ := by
        apply Units.ext
        have := a.ne_zero
        have := b.ne_zero
        have := c.ne_zero
        simp only [Units.val_mul, Units.val_inv_eq_inv_val]
        field_simp
      rw [h'] at h
      simpa using N.inv_mem h
  have hcaf : c * a⁻¹ * (Units.mk0 f hf0)⁻¹ ∈ N :=
    (mem_or_mul_inv_mem_of_natCard_eq_two hN hfN (c * a⁻¹)).resolve_left hca
  obtain ⟨t, ht⟩ := (mem_range_normUnits_iff _).1 hba
  obtain ⟨z, hz⟩ := (mem_range_normUnits_iff _).1 hcaf
  have ht0 : t ≠ 0 := by
    rintro rfl; rw [Algebra.norm_zero] at ht; exact (Units.ne_zero _) ht.symm
  simp only [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_mk0] at ht hz
  refine ⟨x₀ * z, y₀ * z * t⁻¹, ?_⟩
  rw [map_mul, map_mul, map_mul, norm_inv_quadratic, hz, ht]
  have ha : (a : F) ≠ 0 := a.ne_zero
  have hb : (b : F) ≠ 0 := b.ne_zero
  have key : (a : F) * (Algebra.norm F x₀ * ((c : F) * (a : F)⁻¹ * f⁻¹)) +
      (b : F) * (Algebra.norm F y₀ * ((c : F) * (a : F)⁻¹ * f⁻¹) * ((b : F) * (a : F)⁻¹)⁻¹) =
      c * f⁻¹ * (Algebra.norm F x₀ + Algebra.norm F y₀) := by
    field_simp
  rw [key, ← hf, mul_assoc, inv_mul_cancel₀ hf0, mul_one]

namespace HermitianForm

variable {V V' : Type*} [AddCommGroup V] [Module E V] [AddCommGroup V'] [Module E V']

theorem exists_toSesq_self_eq [FiniteDimensional E V] (h : HermitianForm F E V)
    (hV : 2 ≤ finrank E V) (c : Fˣ) : ∃ v, h.toSesq v v = algebraMap F E c := by
  have : Nontrivial V := Module.nontrivial_of_finrank_pos (R := E) (by omega)
  obtain ⟨v₁, hv₁⟩ := h.exists_apply_self_ne_zero
  obtain ⟨a, ha⟩ := h.toSesq_self_mem_range v₁
  have ha0 : a ≠ 0 := by rintro rfl; rw [map_zero] at ha; exact hv₁ ha.symm
  obtain ⟨W, h₀, ⟨e, he⟩, hW⟩ := h.exists_isometric_prod_ofUnit (a := Units.mk0 a ha0) ha.symm
  have hW' := hW inferInstance
  have : Nontrivial W := Module.nontrivial_of_finrank_pos (R := E) (by omega)
  obtain ⟨w, hw⟩ := h₀.exists_apply_self_ne_zero
  obtain ⟨b, hb⟩ := h₀.toSesq_self_mem_range w
  have hb0 : b ≠ 0 := by rintro rfl; rw [map_zero] at hb; exact hw hb.symm
  obtain ⟨x, y, hxy⟩ := exists_mul_norm_add_mul_norm_eq (E := E) (Units.mk0 a ha0)
    (Units.mk0 b hb0) c
  refine ⟨e (x, y • w), ?_⟩
  rw [he, prod_apply, ofUnit_apply, h₀.toSesq_smul_left, h₀.toSesq_smul_right, ← hb, ← hxy]
  simp only [Units.val_mk0, map_add, map_mul]
  rw [← mul_conj (F := F) x, ← mul_conj (F := F) y]
  ring

theorem disc_eq_of_isometric_prod_ofUnit [FiniteDimensional E V] (h : HermitianForm F E V)
    {W : Submodule E V} {h₀ : HermitianForm F E W} {a : Fˣ}
    (H : Isometric ((ofUnit (E := E) a).prod h₀) h) :
    h.disc = QuotientGroup.mk a * h₀.disc := by
  rw [← H.disc_eq, disc_prod, disc_ofUnit]

theorem isometric_iff [FiniteDimensional E V] [FiniteDimensional E V'] (h : HermitianForm F E V)
    (h' : HermitianForm F E V') :
    Isometric h h' ↔ finrank E V = finrank E V' ∧ h.disc = h'.disc := by
  refine ⟨fun H => ⟨H.finrank_eq, H.disc_eq⟩, fun ⟨hdim, hdisc⟩ => ?_⟩
  suffices key : ∀ n : ℕ, ∀ (U : Type _) (U' : Type _) [AddCommGroup U] [Module E U]
      [FiniteDimensional E U] [AddCommGroup U'] [Module E U'] [FiniteDimensional E U'],
      finrank E U = n → finrank E U' = n → ∀ (k : HermitianForm F E U)
      (k' : HermitianForm F E U'), k.disc = k'.disc → Isometric k k' from
    key _ V V' rfl hdim.symm h h' hdisc
  intro n
  induction n with
  | zero =>
    intro U U' _ _ _ _ _ _ hU hU' k k' _
    have : Subsingleton U := Module.finrank_zero_iff.1 hU
    refine ⟨LinearEquiv.ofFinrankEq U U' (hU.trans hU'.symm), fun x y => ?_⟩
    rw [Subsingleton.elim x 0, Subsingleton.elim y 0]
    simp only [LinearEquiv.map_zero, LinearMap.map_zero, LinearMap.zero_apply]
  | succ n ih =>
    intro U U' _ _ _ _ _ _ hU hU' k k' hkk

    obtain ⟨c, ⟨v, hv⟩, ⟨v', hv'⟩⟩ : ∃ c : Fˣ, (∃ v, k.toSesq v v = algebraMap F E c) ∧
        (∃ v', k'.toSesq v' v' = algebraMap F E c) := by
      rcases Nat.lt_or_ge n 1 with hn | hn
      · have hn0 : n = 0 := by omega
        subst hn0
        have : Nontrivial U := Module.nontrivial_of_finrank_eq_succ hU
        have : Nontrivial U' := Module.nontrivial_of_finrank_eq_succ hU'
        obtain ⟨v, hv⟩ := k.exists_apply_self_ne_zero
        obtain ⟨a, ha⟩ := k.toSesq_self_mem_range v
        have ha0 : a ≠ 0 := by rintro rfl; rw [map_zero] at ha; exact hv ha.symm
        obtain ⟨v', hv'⟩ := k'.exists_apply_self_ne_zero
        obtain ⟨a', ha'⟩ := k'.toSesq_self_mem_range v'
        have ha0' : a' ≠ 0 := by rintro rfl; rw [map_zero] at ha'; exact hv' ha'.symm
        obtain ⟨W, k₀, Hk, hW⟩ := k.exists_isometric_prod_ofUnit (a := Units.mk0 a ha0) ha.symm
        obtain ⟨W', k₀', Hk', hW'⟩ :=
          k'.exists_isometric_prod_ofUnit (a := Units.mk0 a' ha0') ha'.symm
        have d1 : k.disc = QuotientGroup.mk (Units.mk0 a ha0) := by
          rw [k.disc_eq_of_isometric_prod_ofUnit Hk,
            k₀.disc_of_finrank_eq_zero (by have := hW inferInstance; omega)]
          exact mul_one (M := Fˣ ⧸ (normUnits F E).range) _
        have d2 : k'.disc = QuotientGroup.mk (Units.mk0 a' ha0') := by
          rw [k'.disc_eq_of_isometric_prod_ofUnit Hk',
            k₀'.disc_of_finrank_eq_zero (by have := hW' inferInstance; omega)]
          exact mul_one (M := Fˣ ⧸ (normUnits F E).range) _
        rw [d1, d2] at hkk
        obtain ⟨u, hu⟩ := QuotientGroup.eq.1 hkk.symm
        refine ⟨Units.mk0 a ha0, ⟨v, ha.symm⟩, ⟨(u : E) • v', ?_⟩⟩
        rw [k'.toSesq_smul_left, k'.toSesq_smul_right, ← ha', ← mul_assoc,
          mul_comm (conj F E (u : E)), mul_conj, ← map_mul, ← coe_normUnits, hu]
        congr 1
        simp only [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_mk0]
        field_simp
      · refine ⟨1, k.exists_toSesq_self_eq (by omega) 1, k'.exists_toSesq_self_eq (by omega) 1⟩
    obtain ⟨W, k₀, Hk, hW⟩ := k.exists_isometric_prod_ofUnit hv
    obtain ⟨W', k₀', Hk', hW'⟩ := k'.exists_isometric_prod_ofUnit hv'
    have hWn : finrank E W = n := by have := hW inferInstance; omega
    have hWn' : finrank E W' = n := by have := hW' inferInstance; omega
    have hd : k₀.disc = k₀'.disc := by
      have d1 := k.disc_eq_of_isometric_prod_ofUnit Hk
      have d2 := k'.disc_eq_of_isometric_prod_ofUnit Hk'
      rw [d1, d2] at hkk
      have := congrArg ((QuotientGroup.mk c : Fˣ ⧸ (normUnits F E).range)⁻¹ * ·) hkk
      simpa only [inv_mul_cancel_left] using this
    exact (Hk.symm.trans ((Isometric.refl _).prod (ih W W' hWn hWn' k₀ k₀' hd))).trans Hk'

end HermitianForm

end Local

end GroundTheory.Automorphic

end
