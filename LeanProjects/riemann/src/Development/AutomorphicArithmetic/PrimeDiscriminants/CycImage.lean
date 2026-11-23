import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.HostFacts
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.InertiaGaloisSymmetry.CycGrp

open NumberField IntermediateField

noncomputable section

namespace Formalism.HC.HostRaw

open Formalism.FrobeniusOrbits Formalism.HC.Der

variable {φ : Frame} (H : HostRaw φ)

theorem emb_mem_adjoin_of_fixed {m : ℕ} (hm : m ∣ H.condN) (x : H.E)
    (hx : ∀ u : (ZMod H.condN)ˣ, (u : ZMod H.condN).val ≡ 1 [MOD m] → H.gal.symm (H.art u) x = x) :
    emb H x ∈ adjoin ℚ {y : Cond.Cyc H.condN | y ^ m = 1} := by
  have := cyc_isGalois H.condN
  rw [← IsGalois.fixedField_fixingSubgroup (adjoin ℚ {y : Cond.Cyc H.condN | y ^ m = 1}), mem_fixedField_iff]
  intro τ hτ
  obtain ⟨u, rfl⟩ := (tauN H.condN).surjective τ
  rw [← emb_art, hx u]
  obtain ⟨k, hk⟩ := hm
  have hz : IsPrimitiveRoot ((H.cycZeta : Cond.Cyc H.condN) ^ k) m :=
    H.cycZeta_prim.pow (Nat.pos_of_ne_zero H.condN_ne_zero) (hk.trans (mul_comm _ _))
  have h1 := (mem_fixingSubgroup_iff _ _).1 hτ _ (subset_adjoin _ _ (show _ ^ m = 1 from hz.pow_eq_one))
  rw [tauN_root _ _ _ (hz.pow_eq_one_iff_dvd _ |>.2 ⟨k, hk⟩)] at h1
  obtain ⟨w, hw⟩ := hz.isUnit (Nat.pos_of_ne_zero fun h => H.condN_ne_zero (by rw [hk, h, zero_mul])).ne'
  rw [hz.eq_orderOf, ← hw, orderOf_units, ← pow_eq_pow_iff_modEq, pow_one]
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, hw]
  exact h1

theorem image_mem_of_fixed {Ω : Type} [Field Ω] [IsAlgClosed Ω] (J : H.E →+* Ω) (M : Subfield Ω) {m : ℕ}
    (hm : m ∣ H.condN) (hM : ∀ y : Ω, y ^ m = 1 → y ∈ M) (x : H.E)
    (hx : ∀ u : (ZMod H.condN)ˣ, (u : ZMod H.condN).val ≡ 1 [MOD m] → H.gal.symm (H.art u) x = x) :
    J x ∈ M := by
  let _ : Algebra H.E (Cond.Cyc H.condN) := (emb H).toRingHom.toAlgebra
  have : IsScalarTower ℚ H.E (Cond.Cyc H.condN) := IsScalarTower.of_algebraMap_eq fun x => ((emb H).commutes x).symm
  have : Algebra.IsAlgebraic H.E (Cond.Cyc H.condN) := Algebra.IsAlgebraic.tower_top (K := ℚ) H.E
  let _ : Algebra H.E Ω := J.toAlgebra
  let Ψ : Cond.Cyc H.condN →ₐ[H.E] Ω := IsAlgClosed.lift
  have h1 : Ψ (emb H x) = J x := Ψ.commutes x
  rw [← h1]
  have h2 := H.emb_mem_adjoin_of_fixed hm x hx
  generalize emb H x = z at h2
  induction h2 using adjoin_induction with
  | mem y hy => exact hM _ (by rw [← map_pow, show y ^ m = 1 from hy, map_one])
  | algebraMap r =>
    rw [eq_ratCast, map_ratCast]
    exact SubfieldClass.ratCast_mem M r
  | add a b _ _ ha hb => rw [map_add]; exact M.add_mem ha hb
  | inv a _ ha => rw [map_inv₀]; exact M.inv_mem ha
  | mul a b _ _ ha hb => rw [map_mul]; exact M.mul_mem ha hb

theorem art_eq_one_of_modEq (u : (ZMod H.condN)ˣ) (hu : (u : ZMod H.condN).val ≡ 1 [MOD H.condN]) : H.art u = 1 := by
  have h1 : u = 1 := by
    apply Units.ext
    rw [← ZMod.natCast_zmod_val (u : ZMod H.condN), (ZMod.natCast_eq_natCast_iff _ _ _).2 hu]
    simp
  rw [h1, map_one]

theorem image_mem_of_roots {Ω : Type} [Field Ω] [IsAlgClosed Ω] (J : H.E →+* Ω) (M : Subfield Ω)
    (hM : ∀ y : Ω, y ^ H.condN = 1 → y ∈ M) (x : H.E) : J x ∈ M :=
  H.image_mem_of_fixed J M dvd_rfl hM x fun u hu => by rw [H.art_eq_one_of_modEq u hu, map_one]; rfl

def congrGal (m : ℕ) : Subgroup (H.E ≃ₐ[ℚ] H.E) :=
  Subgroup.closure {σ | ∃ u : (ZMod H.condN)ˣ, (u : ZMod H.condN).val ≡ 1 [MOD m] ∧ H.gal σ = H.art u}

theorem mem_congrGal_iff {m : ℕ} (hm : m ∣ H.condN) (σ : H.E ≃ₐ[ℚ] H.E) :
    σ ∈ H.congrGal m ↔ ∃ u : (ZMod H.condN)ˣ, (u : ZMod H.condN).val ≡ 1 [MOD m] ∧ H.gal σ = H.art u := by
  refine ⟨fun h => ?_, fun h => Subgroup.subset_closure h⟩
  simp only [val_modEq_one_iff hm]
  induction h using Subgroup.closure_induction with
  | mem τ hτ => simpa only [Set.mem_setOf_eq, val_modEq_one_iff hm] using hτ
  | one => exact ⟨1, map_one _, by rw [map_one, map_one]⟩
  | mul a b _ _ ha hb =>
    obtain ⟨u, h1, h2⟩ := ha
    obtain ⟨v, h3, h4⟩ := hb
    exact ⟨u * v, by rw [map_mul, h1, h3, one_mul], by rw [map_mul, map_mul, h2, h4]⟩
  | inv a _ ha =>
    obtain ⟨u, h1, h2⟩ := ha
    exact ⟨u⁻¹, by rw [map_inv, h1, inv_one], by rw [map_inv, map_inv, h2]⟩

theorem exists_thM (m : ℕ) : ∃ θ : H.E, ℚ⟮θ⟯ = fixedField (H.congrGal m) := by
  obtain ⟨a, ha⟩ := Field.exists_primitive_element ℚ (fixedField (H.congrGal m))
  refine ⟨a, ?_⟩
  have h1 := IntermediateField.lift_adjoin_simple ℚ (fixedField (H.congrGal m)) a
  have h2 := congrArg IntermediateField.lift ha
  exact h1.symm.trans (h2.trans (IntermediateField.lift_top ℚ (fixedField (H.congrGal m))))

def thM (m : ℕ) : H.E := (H.exists_thM m).choose

theorem adjoin_thM (m : ℕ) : ℚ⟮H.thM m⟯ = fixedField (H.congrGal m) := (H.exists_thM m).choose_spec

theorem fix_thM_iff (m : ℕ) (σ : H.E ≃ₐ[ℚ] H.E) : σ (H.thM m) = H.thM m ↔ σ ∈ H.congrGal m := by
  rw [← fixingSubgroup_fixedField (H.congrGal m), ← H.adjoin_thM, IntermediateField.mem_fixingSubgroup_iff]
  refine ⟨fun h x hx => ?_, fun h => h _ (mem_adjoin_simple_self _ _)⟩
  have : ℚ⟮H.thM m⟯ ≤ fixedField (Subgroup.zpowers σ) := by
    rw [adjoin_simple_le_iff, mem_fixedField_iff]
    intro τ hτ
    exact (Subgroup.zpowers_le.2 (show σ ∈ MulAction.stabilizer _ (H.thM m) from h)) hτ
  exact (mem_fixedField_iff _ _).1 (this hx) σ (Subgroup.mem_zpowers σ)

theorem thM_image_mem {Ω : Type} [Field Ω] [IsAlgClosed Ω] (J : H.E →+* Ω) (M : Subfield Ω) {m : ℕ}
    (hm : m ∣ H.condN) (hM : ∀ y : Ω, y ^ m = 1 → y ∈ M) : J (H.thM m) ∈ M :=
  H.image_mem_of_fixed J M hm hM _ fun u hu =>
    (H.fix_thM_iff m _).2 ((H.mem_congrGal_iff hm _).2 ⟨u, hu, H.gal.apply_symm_apply _⟩)

theorem ordCompl_q : ordCompl[H.q] H.condN = H.QS * H.d := by
  rw [show H.condN = H.q ^ 1 * (H.QS * H.d) by ring]
  exact D7.ordCompl_eq H.q_prime _ ((Nat.Prime.coprime_iff_not_dvd H.q_prime).mp H.coprime_QSd_q.symm)

theorem art_eq_one_of_jacobi (u : (ZMod H.condN)ˣ) (hu : (u : ZMod H.condN).val ≡ 1 [MOD H.QS * H.d])
    (hj : jacobiSym (((u : ZMod H.condN).val : ℕ) : ℤ) H.q = 1) : H.art u = 1 := by
  have : Fact H.q.Prime := ⟨H.q_prime⟩
  have hc := H.coprime_QSd_q
  obtain ⟨r, hr⟩ := ZMod.isSquare_of_jacobiSym_eq_one hj
  have hcop : Nat.Coprime (u : ZMod H.condN).val H.q := (ZMod.val_coe_unit_coprime u).coprime_dvd_right H.q_dvd_condN
  have hr2 : (u : ZMod H.condN).val ≡ r.val * r.val [MOD H.q] := by
    rw [← ZMod.natCast_eq_natCast_iff]
    push_cast at hr ⊢
    rw [hr, ZMod.natCast_zmod_val]
  have hrc : Nat.Coprime r.val H.q := Nat.Coprime.coprime_mul_left (k := r.val) (hr2.gcd_eq.symm.trans hcop)
  obtain ⟨n, hn1, hn2⟩ := Nat.chineseRemainder hc 1 r.val
  have hN : H.QS * H.d * H.q = H.condN := mul_right_comm _ _ _
  obtain ⟨v, hv⟩ := exists_unit_modEq (dvd_refl H.condN) n
    (hN ▸ Nat.Coprime.mul_right (hn1.gcd_eq.trans (Nat.coprime_one_left _)) (hn2.gcd_eq.trans hrc))
  have hv1 : (v : ZMod H.condN).val ≡ 1 [MOD H.QS * H.d] := (hv.of_dvd ⟨H.q, hN.symm⟩).trans hn1
  have huv : u = v ^ 2 := by
    have h1 : (u : ZMod H.condN).val ≡ n * n [MOD H.condN] := by
      have h2 := (Nat.modEq_and_modEq_iff_modEq_mul hc).1
        ⟨hu.trans (hn1.mul hn1).symm, hr2.trans (hn2.mul hn2).symm⟩
      rwa [hN] at h2
    apply Units.ext
    rw [← ZMod.natCast_zmod_val (u : ZMod H.condN), (ZMod.natCast_eq_natCast_iff _ _ _).2 h1,
      Units.val_pow_eq_pow_val, ← ZMod.natCast_zmod_val (v : ZMod H.condN), (ZMod.natCast_eq_natCast_iff _ _ _).2 hv]
    push_cast
    ring
  rw [huv, map_pow, H.art_q v hv1]

theorem eq_one_of_mem_congrGal (hps : H.PsQ) {l : ℕ} (hl : l.Prime) (hlS : ¬ l ∣ H.QS) (σ : H.E ≃ₐ[ℚ] H.E)
    (hσ : σ ∈ H.congrGal (ordCompl[l] H.condN)) (h1 : (H.gal σ).1.1 = 1) (h2 : (H.gal σ).1.2 = 1) : σ = 1 := by
  obtain ⟨u, hu, hg⟩ := (H.mem_congrGal_iff (Nat.ordCompl_dvd _ _) σ).1 hσ
  rw [← H.gal.map_eq_one_iff, hg]
  rw [hg] at h1 h2
  by_cases hq : l = H.q
  · rw [hq, H.ordCompl_q] at hu
    refine H.art_eq_one_of_jacobi u hu ?_
    rw [← hps u, h1, Units.val_one]
  by_cases hd : l = H.d
  · rw [hd, ordCompl_d] at hu
    refine (H.art_d u hu).resolve_right fun h => ?_
    rw [h] at h2
    exact absurd h2 (by show ¬ (-1 : ℤˣ) = 1; decide)
  · have hN : ¬ l ∣ H.condN := (H.not_dvd_condN_iff hl).2 ⟨hlS, hq, hd⟩
    rw [Nat.factorization_eq_zero_of_not_dvd hN, pow_zero, Nat.div_one] at hu
    exact H.art_eq_one_of_modEq u hu

end Formalism.HC.HostRaw

end
