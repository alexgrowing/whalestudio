import Development.WeilBound.ThetaLifts.SphericalLattices.LocCommSt
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HaarInvVolumeConjModularCharacterStatement

noncomputable section

namespace PositivityTheory.Sph.M2

open Matrix Formalism.UG GlobalTheory.CompanionTheory.VacLoc.BigCellLocal
open scoped Pointwise

section Asm

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

theorem asm_ordL_eq (x : L) : ordL x = -WithZero.log (Valued.v x : WithZero (Multiplicative ℤ)) := by
  unfold ordL
  split_ifs with h
  · rw [h]; simp
  · congr 1
    conv_rhs => rw [← WithZero.coe_unzero h]
    rfl

theorem asm_ordL_mul {x y : L} (hx : x ≠ 0) (hy : y ≠ 0) : ordL (x * y) = ordL x + ordL y := by
  have hx' : (Valued.v x : WithZero (Multiplicative ℤ)) ≠ 0 := by simpa using hx
  have hy' : (Valued.v y : WithZero (Multiplicative ℤ)) ≠ 0 := by simpa using hy
  rw [asm_ordL_eq, asm_ordL_eq, asm_ordL_eq, map_mul, WithZero.log_mul hx' hy']
  ring

theorem asm_ordL_pow (x : L) (n : ℕ) : ordL (x ^ n) = n * ordL x := by
  rw [asm_ordL_eq, asm_ordL_eq, map_pow, WithZero.log_pow]
  simp

theorem asm_ordL_unit {x y : L} (hx : x ∈ intL L) (hy : y ∈ intL L) (h : x * y = 1) : ordL x = 0 := by
  have hx' : (Valued.v x : WithZero (Multiplicative ℤ)) ≤ 1 := hx
  have hy' : (Valued.v y : WithZero (Multiplicative ℤ)) ≤ 1 := hy
  have h1 : (Valued.v x : WithZero (Multiplicative ℤ)) * Valued.v y = 1 := by rw [← map_mul, h, map_one]
  have h2 : (Valued.v x : WithZero (Multiplicative ℤ)) = 1 := by
    refine le_antisymm hx' ?_
    calc (1 : WithZero (Multiplicative ℤ)) = Valued.v x * Valued.v y := h1.symm
      _ ≤ Valued.v x * 1 := mul_le_mul_right hy' _
      _ = _ := mul_one _
  rw [asm_ordL_eq, h2]; simp

variable {c : L →+* L} {m : ℕ}

def asmT (p : GL (Fin m ⊕ Fin m) L) : Matrix (Fin m) (Fin m) L :=
  (p : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) L).toBlocks₁₁

theorem asm_low {p : GL (Fin m ⊕ Fin m) L} (hp : p ∈ PW L c m) :
    (p : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) L).toBlocks₂₁ = 0 :=
  GlobalTheory.LGrp.mem_blockQ_two.1 hp.2

theorem asmT_mul (a : GL (Fin m ⊕ Fin m) L) {b : GL (Fin m ⊕ Fin m) L} (hb : b ∈ PW L c m) :
    asmT (a * b) = asmT a * asmT b := by
  unfold asmT
  rw [Units.val_mul]
  conv_lhs => rw [← fromBlocks_toBlocks (a : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) L),
    ← fromBlocks_toBlocks (b : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) L), fromBlocks_multiply, toBlocks_fromBlocks₁₁,
    asm_low hb, Matrix.mul_zero, add_zero]

theorem asmT_one : asmT (1 : GL (Fin m ⊕ Fin m) L) = 1 := by
  unfold asmT
  rw [Units.val_one, ← fromBlocks_one, toBlocks_fromBlocks₁₁]

theorem asmT_det_mul_inv {p : GL (Fin m ⊕ Fin m) L} (hp : p ∈ PW L c m) :
    (asmT p).det * (asmT p⁻¹).det = 1 := by
  rw [← det_mul, ← asmT_mul p (inv_mem hp), mul_inv_cancel, asmT_one, det_one]

theorem asmT_det_ne {p : GL (Fin m ⊕ Fin m) L} (hp : p ∈ PW L c m) : (asmT p).det ≠ 0 :=
  left_ne_zero_of_mul_eq_one (asmT_det_mul_inv hp)

theorem asmT_det_int {k : GL (Fin m ⊕ Fin m) L} (hk : k ∈ IntGL L m) : (asmT k).det ∈ intL L := by
  obtain ⟨g, rfl⟩ := hk
  have e : asmT (Matrix.GeneralLinearGroup.map (intL L).subtype g) =
      (intL L).subtype.mapMatrix (g : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) (intL L)).toBlocks₁₁ := by
    ext i j; rfl
  rw [e, ← RingHom.map_det]
  exact Subtype.property _

theorem asm_ord_K {k : GL (Fin m ⊕ Fin m) L} (hk : k ∈ KPW L c m) : ordL (asmT k).det = 0 :=
  asm_ordL_unit (asmT_det_int hk.2.2) (asmT_det_int (inv_mem hk.2.2)) (asmT_det_mul_inv hk.1)

theorem asm_ord_mul {a b : GL (Fin m ⊕ Fin m) L} (ha : a ∈ PW L c m) (hb : b ∈ PW L c m) :
    ordL (asmT (a * b)).det = ordL (asmT a).det + ordL (asmT b).det := by
  rw [asmT_mul a hb, det_mul, asm_ordL_mul (asmT_det_ne ha) (asmT_det_ne hb)]

theorem ord_det_uniformizer_image_eq {ϖ : L} {q : ℕ} (h : IsUnramInv ϖ c q) (x : Lˣ) (hx : (x : L) = ϖ) :
    ordL (asmT (zW L m x)).det = m := by
  have e : asmT (zW L m x) = (x : L) • (1 : Matrix (Fin m) (Fin m) L) := toBlocks_fromBlocks₁₁ _ _ _ _
  have o : ordL ϖ = 1 := by
    rw [asm_ordL_eq, h.2.2.2.1]
    rfl
  rw [e, det_smul, det_one, mul_one, Fintype.card_fin, asm_ordL_pow, hx, o, mul_one]

end Asm

theorem asm_smul {G : Type} [Group G] (K : Subgroup G) (p : G) :
    MulAut.conj p • K = K.map (MulAut.conj p).toMonoidHom := rfl

theorem asm_relIndex {G : Type} [Group G] (K : Subgroup G) (p : G) :
    K.relIndex (K.map (MulAut.conj p).toMonoidHom) = (K.map (MulAut.conj p⁻¹).toMonoidHom).relIndex K := by
  have h := Subgroup.relIndex_map_map_of_injective (f := (MulAut.conj p⁻¹).toMonoidHom) K
    (K.map (MulAut.conj p).toMonoidHom) (MulAut.conj p⁻¹).injective
  have e : (K.map (MulAut.conj p).toMonoidHom).map (MulAut.conj p⁻¹).toMonoidHom = K := by
    rw [← asm_smul, ← asm_smul, ← mul_smul, ← map_mul, inv_mul_cancel, map_one, one_smul]
  rw [e] at h
  exact h.symm

theorem asm_conj_self {G : Type} [Group G] (K : Subgroup G) {k : G} (hk : k ∈ K) : MulAut.conj k • K = K :=
  Subgroup.conj_smul_eq_self_of_mem hk

theorem locMod_of (h1 : LocCommSt) (h2 : ZCountSt) (h3 : GenSt) : LocModSt := by
  intro L _ _ ϖ c q hU m p hp
  have hq : (0 : ℝ) < q := by
    have := hU.2.2.2.2.2.1
    exact_mod_cast (by omega : 0 < q)
  obtain ⟨hmul, hpos, -, -⟩ := GlobalTheory.T.haarInvVolume_conj_modular_character (PW L c m) (KPW L c m) inf_le_left
    (fun h hh => ⟨(h1 L ϖ c q hU m h hh).2, (h1 L ϖ c q hU m h hh).1⟩)
  have key := h3 L ϖ c q hU m
    (fun a => GlobalTheory.HL.invVol (KPW L c m) (MulAut.conj a • KPW L c m) *
      (q : ℝ) ^ (-(2 * (m : ℤ) * ordL (asmT a).det)))
    (fun a ha b hb => by
      rw [hmul a ha b hb, asm_ord_mul ha hb, mul_add, neg_add, zpow_add₀ hq.ne']
      ring)
    (fun a ha => mul_pos (hpos a ha) (zpow_pos hq _))
    (fun k hk => by
      rw [asm_conj_self _ hk, asm_ord_K hk, GlobalTheory.HL.invVol, Subgroup.relIndex_self]
      simp)
    (fun x hx => by
      obtain ⟨hle, hi⟩ := h2 L ϖ c q hU m x hx
      rw [ord_det_uniformizer_image_eq hU x hx, asm_smul, GlobalTheory.HL.invVol, hi, Subgroup.relIndex_eq_one.2 hle, Nat.cast_one, div_one,
        Nat.cast_pow, ← zpow_natCast, ← zpow_add₀ hq.ne']
      push_cast
      rw [add_neg_cancel, zpow_zero])
    p hp
  have hb := (h1 L ϖ c q hU m p hp).2
  rw [asm_relIndex] at hb
  have hb' : ((((KPW L c m).map (MulAut.conj p⁻¹).toMonoidHom).relIndex (KPW L c m) : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast hb
  simp only [asm_smul, GlobalTheory.HL.invVol, asm_relIndex] at key
  rw [div_mul_eq_mul_div, div_eq_one_iff_eq hb'] at key
  rw [← key, mul_comm]
  rfl

end PositivityTheory.Sph.M2

end
