import Mathlib
import GroundTheory.ArithmeticGeometry.AbelianVarieties.DualQuadratic
import GroundTheory.ArithmeticGeometry.AbelianVarieties.WeilPairingTate
set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.Abelian

open Polynomial WeierstrassCurve PadicInt

universe u

variable {F : Type u} [Field F] [IsAlgClosed F] [DecidableEq F]

namespace TateCharpoly

variable {E E' E'' : WeierstrassCurve F} [E.IsElliptic] [E'.IsElliptic] [E''.IsElliptic]

theorem homPt_homComp (R : isogHom E' E'') (Q : isogHom E E') :
    homPt (homComp R Q) = (homPt R).comp (homPt Q) := by
  by_cases hQ : Q = 0
  · subst hQ
    rw [homComp_zero_right, homPt_zero, homPt_zero, AddMonoidHom.comp_zero]
  by_cases hR : R = 0
  · subst hR
    rw [homComp_zero_left, homPt_zero, homPt_zero, AddMonoidHom.zero_comp]
  obtain ⟨φ, rfl⟩ : ∃ φ : Isogeny E E', φ.toHom = Q := ⟨isogOfHom Q hQ, rfl⟩
  obtain ⟨ψ, rfl⟩ : ∃ ψ : Isogeny E' E'', ψ.toHom = R := ⟨isogOfHom R hR, rfl⟩
  rw [Isogeny.homComp_toHom, homPt_toHom, homPt_toHom, homPt_toHom]
  ext P
  rw [AddMonoidHom.comp_apply, Isogeny.pointHom_apply, Isogeny.pointHom_apply,
    Isogeny.pointHom_apply, Isogeny.pointMap_comp]

theorem homId_eq_mulIsogeny : (homId : isogEnd E) = (mulIsogeny E 1 one_ne_zero).toHom := by
  rw [mulIsogeny_toHom, one_smul]

theorem homPt_homId : homPt (homId : isogEnd E) = AddMonoidHom.id _ := by
  rw [homId_eq_mulIsogeny, homPt_toHom]
  ext P
  rw [Isogeny.pointHom_apply, Isogeny.pointMap_mulIsogeny, one_smul, AddMonoidHom.id_apply]

theorem homPt_zsmul_homId (n : ℤ) (P : E.toAffine.Point) :
    homPt (n • (homId : isogEnd E)) P = n • P := by
  rw [← homPointHom_apply, map_zsmul, homPointHom_apply, homPt_homId]
  rfl

theorem homDeg_homId : homDeg (homId : isogEnd E) = 1 := by
  rw [homId_eq_mulIsogeny, homDeg_toHom, degree_mulIsogeny]
  norm_num

theorem homDeg_nonneg (Q : isogHom E E') : 0 ≤ homDeg Q := by
  by_cases h : Q = 0
  · rw [h, homDeg_zero]
  · exact (homDeg_pos h).le

theorem homDeg_neg (Q : isogHom E E') : homDeg (-Q) = homDeg Q := by
  rw [← neg_one_zsmul, homDeg_zsmul]
  ring

theorem degBilin_homId (a : isogEnd E) :
    degBilin a homId = 1 + homDeg a - homDeg (homId - a) := by
  have h := degBilin_zsmul_right (-1) a homId
  rw [neg_one_zsmul, smul_eq_mul, neg_one_mul] at h
  have e1 : homDeg (homId - a) = homDeg (a + -homId) := by
    rw [← homDeg_neg, neg_sub, sub_eq_add_neg]
  have e2 : degBilin a (-homId) = homDeg (a + -homId) - homDeg a - homDeg (-homId : isogEnd E) := rfl
  rw [homDeg_neg, homDeg_homId] at e2
  rw [e1, ← neg_neg (degBilin a homId), ← h, e2]
  ring

end TateCharpoly

open TateCharpoly

variable {E : WeierstrassCurve F} [E.IsElliptic] (ℓ : ℕ) [hℓ : Fact ℓ.Prime]

noncomputable def endTate : isogEnd E →+* Module.End ℤ_[ℓ] (TateModule ℓ E.toAffine.Point) where
  toFun a := TateModule.map (homPt a)
  map_one' := LinearMap.ext fun t => Subtype.ext <| funext fun k => by
    rw [TateModule.map_apply]
    show homPt (homId : isogEnd E) _ = _
    rw [homPt_homId]
    rfl
  map_mul' a b := LinearMap.ext fun t => Subtype.ext <| funext fun k => by
    rw [Module.End.mul_apply, TateModule.map_apply, TateModule.map_apply, TateModule.map_apply,
      isogEnd_mul_def, homPt_homComp, AddMonoidHom.comp_apply]
  map_zero' := LinearMap.ext fun t => Subtype.ext <| funext fun k => by
    rw [TateModule.map_apply, homPt_zero, AddMonoidHom.zero_apply]
    rfl
  map_add' a b := LinearMap.ext fun t => Subtype.ext <| funext fun k => by
    rw [LinearMap.add_apply, TateModule.map_apply, AddSubgroup.coe_add, Pi.add_apply,
      TateModule.map_apply, TateModule.map_apply, homPt_add, AddMonoidHom.add_apply]

theorem endTate_apply (a : isogEnd E) (t : TateModule ℓ E.toAffine.Point) (k : ℕ) :
    ((endTate ℓ a t : TateModule ℓ E.toAffine.Point) : ℕ → E.toAffine.Point) k =
      homPt a ((t : ℕ → E.toAffine.Point) k) :=
  rfl

variable {ℓ}

theorem weilPairing_homPt_homPt {n : ℕ} (hn : (n : F) ≠ 0) (a : isogEnd E) {P Q : E.toAffine.Point}
    (hP : n • P = 0) (hQ : n • Q = 0) :
    weilPairing E n (homPt a P) (homPt a Q) = weilPairing E n P Q ^ (homDeg a).toNat := by
  have hQ' : n • homPt a Q = 0 := by rw [← map_nsmul, hQ, map_zero]
  rw [← weilPairing_homDualFun a hn hP hQ']
  have e : homPt (homDualFun a) (homPt a Q) = (homDeg a).toNat • Q := by
    have h1 : homPt (homDualFun a) (homPt a Q) = homPt (homComp (homDual a) a) Q := by
      rw [homPt_homComp]; rfl
    rw [h1, homComp_homDual_self, homPt_zsmul_homId, ← natCast_zsmul,
      Int.toNat_of_nonneg (homDeg_nonneg a)]
  rw [e, weilPairing_nsmul_right hn hP hQ]

theorem det_endTate (hℓF : (ℓ : F) ≠ 0) (a : isogEnd E) :
    LinearMap.det (endTate ℓ a) = ((homDeg a : ℤ) : ℤ_[ℓ]) := by
  classical
  have hkF : ∀ k : ℕ, ((ℓ ^ k : ℕ) : F) ≠ 0 := fun k => by push_cast; exact pow_ne_zero k hℓF
  obtain ⟨b⟩ := tateModule_basis E ℓ hℓF
  have hcard := card_nsmul_pow_eq_zero E ℓ hℓF
  set A := E.toAffine.Point
  set e : ℕ → A → A → F := fun k => weilPairing E (ℓ ^ k) with he
  have hl : ∀ k P Q R, ℓ ^ k • P = 0 → ℓ ^ k • Q = 0 → ℓ ^ k • R = 0 →
      e k (P + Q) R = e k P R * e k Q R :=
    fun k _ _ _ hP hQ hR => weilPairing_add_left (hkF k) hP hQ hR
  have hr : ∀ k P Q R, ℓ ^ k • P = 0 → ℓ ^ k • Q = 0 → ℓ ^ k • R = 0 →
      e k P (Q + R) = e k P Q * e k P R :=
    fun k _ _ _ hP hQ hR => weilPairing_add_right (hkF k) hP hQ hR
  have hself : ∀ k P, ℓ ^ k • P = 0 → e k P P = 1 := fun k _ hP => weilPairing_self (hkF k) hP
  have hpow : ∀ k P Q, ℓ ^ k • P = 0 → ℓ ^ k • Q = 0 → e k P Q ^ ℓ ^ k = 1 :=
    fun k _ _ hP hQ => weilPairing_pow_eq_one (hkF k) hP hQ
  have hnd : ∀ k P, ℓ ^ k • P = 0 → (∀ Q, ℓ ^ k • Q = 0 → e k P Q = 1) → P = 0 :=
    fun k _ hP h => eq_zero_of_forall_weilPairing_eq_one' (hkF k) hP h
  set m := (homDeg a).toNat with hmdef
  have hm : homDeg a = (m : ℤ) := (Int.toNat_of_nonneg (homDeg_nonneg a)).symm
  set M := LinearMap.toMatrix b b (endTate ℓ a) with hM
  rw [← LinearMap.det_toMatrix b, Matrix.det_fin_two]

  have hcomp : ∀ (x y : ℤ_[ℓ]) k, ((x • b 0 + y • b 1 : TateModule ℓ A) : ℕ → A) k =
      (toZModPow k x).val • ((b 0 : TateModule ℓ A) : ℕ → A) k +
        (toZModPow k y).val • ((b 1 : TateModule ℓ A) : ℕ → A) k := by
    intro x y k
    rw [AddSubgroup.coe_add, Pi.add_apply, TateModule.smul_apply, TateModule.smul_apply]

  have hcol : ∀ j, endTate ℓ a (b j) = M 0 j • b 0 + M 1 j • b 1 := by
    intro j
    conv_lhs => rw [← b.sum_repr (endTate ℓ a (b j))]
    rw [Fin.sum_univ_two, hM, LinearMap.toMatrix_apply, LinearMap.toMatrix_apply]

  have hgen : ∀ k R, ℓ ^ k • R = 0 → ∃ x y : ℤ_[ℓ],
      R = (toZModPow k x).val • ((b 0 : TateModule ℓ A) : ℕ → A) k +
        (toZModPow k y).val • ((b 1 : TateModule ℓ A) : ℕ → A) k := by
    intro k R hR
    obtain ⟨t, ht⟩ := exists_tateModule_apply_eq hcard k R hR
    refine ⟨b.repr t 0, b.repr t 1, ?_⟩
    rw [← ht, ← hcomp]
    conv_lhs => rw [← b.sum_repr t]
    rw [Fin.sum_univ_two]
  refine PadicInt.ext_of_toZModPow.mp fun k => ?_
  set P := ((b 0 : TateModule ℓ A) : ℕ → A) k with hPdef
  set Q := ((b 1 : TateModule ℓ A) : ℕ → A) k with hQdef
  have hP : ℓ ^ k • P = 0 := TateModule.pow_nsmul (b 0) k
  have hQ : ℓ ^ k • Q = 0 := TateModule.pow_nsmul (b 1) k
  have hN : ℓ ^ k ≠ 0 := pow_ne_zero k hℓ.out.ne_zero
  set ζ := e k P Q with hζ
  have hz : ζ ^ ℓ ^ k = 1 := hpow k P Q hP hQ

  have hφ : ∀ j, homPt a (((b j : TateModule ℓ A) : ℕ → A) k) =
      (toZModPow k (M 0 j)).val • P + (toZModPow k (M 1 j)).val • Q := by
    intro j
    rw [← endTate_apply ℓ a (b j) k, hcol j, hcomp]
  have hφP := hφ 0
  have hφQ := hφ 1
  have hdeg : e k (homPt a P) (homPt a Q) = ζ ^ m :=
    weilPairing_homPt_homPt (hkF k) a hP hQ
  have hcomb := pairing_comb (ℓ ^ k) (e k) (hl k) (hr k) (hpow k) (hself k) hN hP hQ
    (toZModPow k (M 0 0)).val (toZModPow k (M 1 0)).val (toZModPow k (M 0 1)).val
    (toZModPow k (M 1 1)).val
  rw [← hφP, ← hφQ, hdeg, ← pow_add] at hcomb

  have hfin : IsOfFinOrder ζ := isOfFinOrder_iff_pow_eq_one.mpr ⟨ℓ ^ k, Nat.pos_of_ne_zero hN, hz⟩
  have hord : orderOf ζ = ℓ ^ k := by
    cases k with
    | zero => simpa using hz
    | succ n =>
      refine orderOf_eq_prime_pow ?_ hz
      intro hn
      have hX : ℓ ^ (n + 1) • (ℓ ^ n • P) = 0 := nsmul_nsmul_eq_zero _ hP _
      have hXP : e (n + 1) (ℓ ^ n • P) P = 1 := by
        rw [pairing_nsmul_left _ (e (n + 1)) (hl _) (hpow _) hN hP hP, hself _ P hP, one_pow]
      have hXQ : e (n + 1) (ℓ ^ n • P) Q = 1 := by
        rw [pairing_nsmul_left _ (e (n + 1)) (hl _) (hpow _) hN hP hQ]
        exact hn
      have h0 : ℓ ^ n • P = 0 := by
        refine hnd (n + 1) _ hX fun R hR => ?_
        obtain ⟨x, y, rfl⟩ := hgen (n + 1) R hR
        rw [hr _ _ _ _ hX (nsmul_nsmul_eq_zero _ hP _) (nsmul_nsmul_eq_zero _ hQ _),
          pairing_nsmul_right _ (e (n + 1)) (hr _) (hpow _) hN hX hP,
          pairing_nsmul_right _ (e (n + 1)) (hr _) (hpow _) hN hX hQ, hXP, hXQ, one_pow,
          one_pow, one_mul]
      have h1 : ((b 0 : TateModule ℓ A) : ℕ → A) 1 = 0 := by
        rw [← TateModule.pow_nsmul_add (b 0) 1 n, add_comm]
        exact h0
      exact TateModule.basis_apply_one_ne_zero b 0 h1
  have hmod := (hfin.pow_eq_pow_iff_modEq).mp hcomb
  rw [hord] at hmod
  have hz' := (ZMod.natCast_eq_natCast_iff _ _ _).mpr hmod
  push_cast [ZMod.natCast_zmod_val] at hz'
  rw [map_sub, map_mul, map_mul, hm, Int.cast_natCast, map_natCast]
  linear_combination -hz'

namespace TateCharpoly

theorem det_one_sub_fin_two {R : Type*} [CommRing R] (M : Matrix (Fin 2) (Fin 2) R) :
    (1 - M).det = 1 - M.trace + M.det := by
  rw [Matrix.det_fin_two, Matrix.det_fin_two, Matrix.trace_fin_two]
  simp only [Matrix.sub_apply, Matrix.one_apply_eq, Matrix.one_apply_ne (show (0 : Fin 2) ≠ 1 by decide),
    Matrix.one_apply_ne (show (1 : Fin 2) ≠ 0 by decide)]
  ring

theorem degBilin_one (a : isogEnd E) : degBilin a 1 = 1 + homDeg a - homDeg (1 - a) :=
  degBilin_homId a

end TateCharpoly

theorem trace_endTate (hℓF : (ℓ : F) ≠ 0) (a : isogEnd E) :
    LinearMap.trace ℤ_[ℓ] _ (endTate ℓ a) = ((1 + homDeg a - homDeg (1 - a) : ℤ) : ℤ_[ℓ]) := by
  classical
  obtain ⟨b⟩ := tateModule_basis E ℓ hℓF
  have h1 := det_endTate hℓF a
  have h2 := det_endTate hℓF (1 - a)
  rw [← LinearMap.det_toMatrix b] at h1 h2
  rw [map_sub, map_one, map_sub, LinearMap.toMatrix_one, det_one_sub_fin_two, h1] at h2
  rw [LinearMap.trace_eq_matrix_trace ℤ_[ℓ] b]
  push_cast
  linear_combination -h2

theorem trace_endTate_eq_degBilin (hℓF : (ℓ : F) ≠ 0) (a : isogEnd E) :
    LinearMap.trace ℤ_[ℓ] _ (endTate ℓ a) = ((degBilin a 1 : ℤ) : ℤ_[ℓ]) := by
  rw [trace_endTate hℓF, degBilin_one]

instance TateCharpoly.instFreeTateModule [hℓF : Fact ((ℓ : F) ≠ 0)] :
    Module.Free ℤ_[ℓ] (TateModule ℓ E.toAffine.Point) :=
  tateModule_free E ℓ hℓF.out

instance TateCharpoly.instFiniteTateModule [hℓF : Fact ((ℓ : F) ≠ 0)] :
    Module.Finite ℤ_[ℓ] (TateModule ℓ E.toAffine.Point) :=
  Module.Finite.of_basis (tateModule_basis E ℓ hℓF.out).some

theorem charpoly_endTate [hℓF : Fact ((ℓ : F) ≠ 0)] (a : isogEnd E) :
    (endTate ℓ a).charpoly =
      X ^ 2 - C ((degBilin a 1 : ℤ) : ℤ_[ℓ]) * X + C ((homDeg a : ℤ) : ℤ_[ℓ]) := by
  classical
  obtain ⟨b⟩ := tateModule_basis E ℓ hℓF.out
  rw [← LinearMap.charpoly_toMatrix (endTate ℓ a) b, Matrix.charpoly_fin_two,
    ← LinearMap.trace_eq_matrix_trace, LinearMap.det_toMatrix, trace_endTate_eq_degBilin hℓF.out,
    det_endTate hℓF.out]

end GroundTheory.Arith.Abelian
