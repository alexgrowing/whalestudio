import Formalism.LocalRingCardinality.DataHost
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.HostFacts
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.InertiaGaloisSymmetry.CycBasic

open NumberField IntermediateField

noncomputable section

namespace UpperTheory.InertGen

open Formalism.HC Formalism.FrobeniusOrbits Formalism.BasicNotions

section Raw

variable {φ : Frame} (H : HostRaw φ)

def inertG (l : ℕ) : Subgroup (H.E ≃ₐ[ℚ] H.E) :=
  ((ZMod.unitsMap (Nat.ordCompl_dvd H.condN l)).ker).map (H.gal.symm.toMonoidHom.comp H.art)

theorem mem_inertG_iff (l : ℕ) (σ : H.E ≃ₐ[ℚ] H.E) : σ ∈ inertG H l ↔
    ∃ u : (ZMod H.condN)ˣ, (u : ZMod H.condN).val ≡ 1 [MOD ordCompl[l] H.condN] ∧ H.gal σ = H.art u := by
  have hN : NeZero H.condN := by
    refine ⟨?_⟩
    have h1 := H.QS_pos
    have h2 := H.q_prime.pos
    have h3 : 0 < H.d := by
      have := H.d_mod_four
      omega
    exact (Nat.mul_pos (Nat.mul_pos h1 h2) h3).ne'
  simp only [inertG, Subgroup.mem_map, MonoidHom.mem_ker, MonoidHom.comp_apply,
    MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_eq]
  constructor
  · rintro ⟨x, hx, hxσ⟩
    refine ⟨x, ?_, hxσ.symm⟩
    have h := congrArg (fun y : (ZMod (ordCompl[l] H.condN))ˣ => (y : ZMod (ordCompl[l] H.condN))) hx
    simp only [ZMod.unitsMap_val, Units.val_one, ZMod.cast_eq_val] at h
    exact (ZMod.natCast_eq_natCast_iff _ _ _).1 (by rw [h, Nat.cast_one])
  · rintro ⟨x, hx, hxσ⟩
    refine ⟨x, ?_, hxσ.symm⟩
    ext
    simp only [ZMod.unitsMap_val, Units.val_one, ZMod.cast_eq_val]
    rw [← Nat.cast_one (R := ZMod (ordCompl[l] H.condN))]
    exact (ZMod.natCast_eq_natCast_iff _ _ _).2 hx

def inertField (l : ℕ) : IntermediateField ℚ H.E := fixedField (inertG H l)

theorem mem_inertField_iff (l : ℕ) (x : H.E) : x ∈ inertField H l ↔
    ∀ u : (ZMod H.condN)ˣ, (u : ZMod H.condN).val ≡ 1 [MOD ordCompl[l] H.condN] →
      H.gal.symm (H.art u) x = x := by
  unfold inertField
  rw [IntermediateField.mem_fixedField_iff]
  constructor
  · intro h u hu
    exact h _ ((mem_inertG_iff H l _).2 ⟨u, hu, H.gal.apply_symm_apply _⟩)
  · intro h σ hσ
    obtain ⟨u, hu, e⟩ := (mem_inertG_iff H l σ).1 hσ
    have := h u hu
    rwa [← e, MulEquiv.symm_apply_apply] at this

theorem exists_gen (l : ℕ) : ∃ θ : H.E, ℚ⟮θ⟯ = inertField H l := by
  obtain ⟨α, hα⟩ := Field.exists_primitive_element ℚ (inertField H l)
  refine ⟨α, ?_⟩
  have := congrArg (IntermediateField.lift (F := inertField H l)) hα
  exact (IntermediateField.lift_adjoin_simple ℚ (inertField H l) α).symm.trans
    (this.trans (IntermediateField.lift_top ℚ (inertField H l)))

def thetaAt (l : ℕ) : H.E := (exists_gen H l).choose

theorem adjoin_thetaAt (l : ℕ) : ℚ⟮thetaAt H l⟯ = inertField H l := (exists_gen H l).choose_spec

theorem thetaAt_mem (l : ℕ) : thetaAt H l ∈ inertField H l := by
  rw [← adjoin_thetaAt]; exact mem_adjoin_simple_self _ _

theorem image_inertField {Ω : Type} [Field Ω] [IsAlgClosed Ω] (J : H.E →+* Ω) {l : ℕ} :
    ∃ z : Ω, z ^ ordCompl[l] H.condN = 1 ∧ ∀ x ∈ inertField H l, J x ∈ Subfield.closure {z} := by
  have hg := Der.cyc_isGalois H.condN
  obtain ⟨Ψ, hΨ⟩ : ∃ Ψ : Cond.Cyc H.condN →+* Ω, ∀ x, Ψ (Der.emb H x) = J x := by
    let _ : Algebra H.E (Cond.Cyc H.condN) := (Der.emb H).toRingHom.toAlgebra
    let _ : Algebra H.E Ω := J.toAlgebra
    have : IsScalarTower ℚ H.E (Cond.Cyc H.condN) :=
      IsScalarTower.of_algebraMap_eq fun x => ((Der.emb H).commutes x).symm
    have : Algebra.IsAlgebraic H.E (Cond.Cyc H.condN) := Algebra.IsAlgebraic.tower_top (K := ℚ) H.E
    let f : Cond.Cyc H.condN →ₐ[H.E] Ω := IsAlgClosed.lift
    exact ⟨f, fun x => f.commutes x⟩
  have hN : H.condN ≠ 0 := H.condN_ne_zero
  set w : Cond.Cyc H.condN := Cond.z H.condN ^ ordProj[l] H.condN with hw
  have hwp : IsPrimitiveRoot w (ordCompl[l] H.condN) :=
    (Cond.z_spec H.condN).pow (Nat.pos_of_ne_zero hN) (Nat.ordProj_mul_ordCompl_eq_self _ _).symm
  have hwN : w ^ H.condN = 1 := (hwp.pow_eq_one_iff_dvd _).2 (Nat.ordCompl_dvd _ _)
  refine ⟨Ψ w, by rw [← map_pow, hwp.pow_eq_one, map_one], fun x hx => ?_⟩
  have h1 : Der.emb H x ∈ ℚ⟮w⟯ := by
    rw [← IsGalois.fixedField_fixingSubgroup ℚ⟮w⟯, IntermediateField.mem_fixedField_iff]
    intro τ hτ
    obtain ⟨u, rfl⟩ := (Der.tauN H.condN).surjective τ
    have h2 := (IntermediateField.mem_fixingSubgroup_iff _ _).1 hτ w (mem_adjoin_simple_self _ _)
    rw [Der.tauN_root _ _ _ hwN] at h2
    have h3 : (u : ZMod H.condN).val ≡ 1 [MOD ordCompl[l] H.condN] := by
      have hw0 : w ≠ 0 := hwp.ne_zero (Nat.ordCompl_pos l hN).ne'
      rw [Nat.modEq_iff_dvd, ← hwp.zpow_eq_one_iff_dvd, zpow_sub₀ hw0, zpow_natCast, zpow_natCast, h2, pow_one,
        div_self hw0]
    rw [← Der.emb_art, (mem_inertField_iff H l x).1 hx u h3]
  have h4 : (ℚ⟮w⟯).toSubfield ≤ (Subfield.closure {Ψ w}).comap Ψ := by
    rw [IntermediateField.adjoin_toSubfield, Subfield.closure_le]
    rintro y (⟨r, rfl⟩ | rfl)
    · show Ψ (algebraMap ℚ _ r) ∈ Subfield.closure {Ψ w}
      have : CharZero Ω := (RingHom.charZero_iff J.injective).1 inferInstance
      rw [eq_ratCast, map_ratCast]
      exact SubfieldClass.ratCast_mem _ r
    · exact Subfield.subset_closure rfl
  rw [← hΨ]
  exact h4 h1

end Raw

variable {R : Ranks} (H : Host R)

theorem sqq_ne_zero : H.sqq ≠ 0 := by
  intro h
  have h1 := H.sqq_sq
  rw [h] at h1
  have h2 : (H.q : H.E) = 0 := by simpa using h1.symm
  exact H.q_prime.ne_zero (by exact_mod_cast h2)

private theorem sign_eq_one {E : Type} [Field E] [CharZero E] {s : ℤˣ} {a : E} (ha : a ≠ 0)
    (h : ((s : ℤ) : E) * a = a) : s = 1 := by
  have h1 : ((s : ℤ) : E) = 1 := mul_right_cancel₀ ha (by rw [h, one_mul])
  have h2 : (s : ℤ) = 1 := by exact_mod_cast h1
  exact Units.ext h2

theorem art_eq_one_of_q (u : (ZMod H.condN)ˣ) (hu : (u : ZMod H.condN).val ≡ 1 [MOD H.QS * H.d])
    (h : (H.art u).1.1 = 1) : H.art u = 1 := by
  have hq := H.q_prime
  haveI : Fact H.q.Prime := ⟨hq⟩
  have hjac : jacobiSym (((u : ZMod H.condN).val : ℕ) : ℤ) H.q = 1 := by
    rw [← H.flPS u, h]
    rfl
  obtain ⟨w, hw⟩ := ZMod.isSquare_of_jacobiSym_eq_one hjac
  obtain ⟨k, hk1, hk2⟩ := Nat.chineseRemainder H.coprime_QSd_q 1 w.val
  have key : ∀ a : ℕ, a ≡ 1 [MOD H.QS * H.d] → a ≡ w.val * w.val [MOD H.q] →
      a ≡ k * k [MOD H.condN] := by
    intro a ha1 ha2
    show a ≡ k * k [MOD H.QS * H.q * H.d]
    have hc : H.QS * H.q * H.d = H.QS * H.d * H.q := by ring
    rw [hc]
    apply (Nat.modEq_and_modEq_iff_modEq_mul H.coprime_QSd_q).1
    constructor
    · exact ha1.trans (by simpa using (hk1.mul hk1).symm)
    · exact ha2.trans (hk2.mul hk2).symm
  have e1 : (u : ZMod H.condN).val ≡ w.val * w.val [MOD H.q] := by
    apply (ZMod.natCast_eq_natCast_iff _ _ _).1
    rw [Nat.cast_mul, ZMod.natCast_zmod_val]
    exact_mod_cast hw
  have hmod := key _ hu e1
  have hsq : (u : ZMod H.condN) = (k : ZMod H.condN) * (k : ZMod H.condN) := by
    rw [← ZMod.natCast_zmod_val (u : ZMod H.condN), ← Nat.cast_mul]
    exact (ZMod.natCast_eq_natCast_iff _ _ _).2 hmod
  have hxu : IsUnit ((k : ZMod H.condN)) := isUnit_of_mul_isUnit_left (hsq ▸ u.isUnit)
  have hu2 : u = hxu.unit ^ 2 := by
    ext
    simp [pow_two, hsq]
  have hx1 : (hxu.unit : ZMod H.condN).val ≡ 1 [MOD H.QS * H.d] := by
    rw [IsUnit.unit_spec, ZMod.val_natCast]
    have hd : H.QS * H.d ∣ H.condN := ⟨H.q, by show H.QS * H.q * H.d = _; ring⟩
    exact ((Nat.mod_modEq k H.condN).of_dvd hd).trans hk1
  rw [hu2, map_pow, H.art_q _ hx1]

theorem ordCompl_q : ordCompl[H.q] H.condN = H.QS * H.d := by
  have hq := H.q_prime
  have hnd : ¬ H.q ∣ H.QS * H.d := by
    intro hd
    have h1 : H.q ∣ Nat.gcd (H.QS * H.d) H.q := Nat.dvd_gcd hd dvd_rfl
    rw [H.coprime_QSd_q.gcd_eq_one] at h1
    exact hq.one_lt.ne' (Nat.dvd_one.1 h1)
  have hc : H.condN = (H.QS * H.d) * H.q := by
    unfold Formalism.HC.HostRaw.condN
    ring
  rw [hc, Nat.ordCompl_mul, Nat.factorization_eq_zero_of_not_dvd hnd, hq.factorization_self]
  simp [hq.pos]

theorem ordCompl_d : ordCompl[H.d] H.condN = H.QS * H.q := by
  have hN : H.condN = H.d ^ 1 * (H.QS * H.q) := by unfold HostRaw.condN; ring
  rw [hN]
  exact Nat.ordCompl_pow_mul_of_not_dvd 1 H.d_prime H.d_not_dvd_QSq

theorem adjoin_thetaAt_top {l : ℕ} (hl : l.Prime) (hS : ¬ l ∣ H.QS) :
    IntermediateField.adjoin ℚ ({thetaAt H.toHostRaw l, H.sqq, H.sqd} : Set H.E) = ⊤ := by
  have hg := H.galois
  set M := IntermediateField.adjoin ℚ ({thetaAt H.toHostRaw l, H.sqq, H.sqd} : Set H.E) with hM
  have hbot : M.fixingSubgroup = ⊥ := by
    rw [eq_bot_iff]
    intro σ hσ
    have h1 : σ ∈ inertG H.toHostRaw l := by
      rw [← IntermediateField.fixingSubgroup_fixedField (inertG H.toHostRaw l)]
      refine IntermediateField.fixingSubgroup_antitone ?_ hσ
      show inertField H.toHostRaw l ≤ M
      rw [← adjoin_thetaAt]
      exact IntermediateField.adjoin.mono _ _ _ (by simp)
    rw [IntermediateField.mem_fixingSubgroup_iff] at hσ
    have h2 := hσ H.sqq (IntermediateField.subset_adjoin _ _ (by simp))
    have h3 := hσ H.sqd (IntermediateField.subset_adjoin _ _ (by simp))
    rw [H.gal_sqq] at h2
    rw [H.gal_sqd] at h3
    have h2' := sign_eq_one (sqq_ne_zero H) h2
    have h3' := sign_eq_one H.sqd_ne_zero h3
    obtain ⟨u, hu, e⟩ := (mem_inertG_iff _ l σ).1 h1
    rw [Subgroup.mem_bot, ← H.gal.map_eq_one_iff, e]
    rw [e] at h2' h3'
    by_cases hq : l = H.q
    · subst hq
      rw [ordCompl_q] at hu
      exact art_eq_one_of_q H u hu h2'
    by_cases hd : l = H.d
    · subst hd
      rw [ordCompl_d] at hu
      rcases H.art_d u hu with h | h
      · exact h
      · rw [h] at h3'
        exact absurd h3' (by show (-1 : ℤˣ) ≠ 1; decide)
    have hN : ¬ l ∣ H.condN := (H.not_dvd_condN_iff hl).2 ⟨hS, hq, hd⟩
    rw [Nat.factorization_eq_zero_of_not_dvd hN, pow_zero, Nat.div_one] at hu
    have : u = 1 := by
      apply Units.ext
      have := (ZMod.natCast_eq_natCast_iff _ _ _).2 hu
      simpa using this
    rw [this, map_one]
  rw [← IsGalois.fixedField_fixingSubgroup M, hbot, IntermediateField.fixedField_bot]

end UpperTheory.InertGen

end
