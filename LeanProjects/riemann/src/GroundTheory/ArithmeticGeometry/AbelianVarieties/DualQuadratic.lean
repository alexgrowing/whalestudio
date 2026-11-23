import Mathlib
import GroundTheory.ArithmeticGeometry.AbelianVarieties.DualWeil

namespace GroundTheory.Arith.Abelian

open Polynomial WeierstrassCurve WeierstrassCurve.Affine IntermediateField

universe u

variable {F : Type u} [Field F] [IsAlgClosed F] [DecidableEq F] {E E' : WeierstrassCurve F}
  [E.IsElliptic] [E'.IsElliptic]

noncomputable def homDeg (Q : isogHom E E') : ℤ :=
  open Classical in if h : Q = 0 then 0 else ((isogOfHom Q h).degree : ℤ)

theorem homDeg_toHom (φ : Isogeny E E') : homDeg φ.toHom = φ.degree := by
  rw [homDeg, dif_neg φ.toHom_ne_zero]
  rfl

theorem homDeg_zero : homDeg (0 : isogHom E E') = 0 := by rw [homDeg, dif_pos rfl]

theorem homDeg_pos {Q : isogHom E E'} (hQ : Q ≠ 0) : 0 < homDeg Q := by
  rw [homDeg, dif_neg hQ]
  exact_mod_cast (isogOfHom Q hQ).degree_pos

theorem mulIsogeny_toHom (n : ℤ) (hn : n ≠ 0) :
    (mulIsogeny E n hn).toHom = n • (homId : isogEnd E) :=
  Subtype.ext (by rw [Isogeny.toHom_val, Isogeny.mulIsogeny_val]; rfl)

theorem homComp_homDual_self (Q : isogHom E E') : homComp (homDual Q) Q = homDeg Q • homId := by
  by_cases h : Q = 0
  · subst h
    rw [homComp_zero_right, homDeg_zero, zero_smul]
  · rw [← isogOfHom_toHom Q h, homDual_toHom, Isogeny.homComp_toHom, Isogeny.dual_comp,
      mulIsogeny_toHom, homDeg_toHom]

theorem eq_zero_of_zsmul_homId {n : ℤ} (h : n • (homId : isogEnd E) = 0) : n = 0 := by
  by_contra hn
  rw [← mulIsogeny_toHom n hn] at h
  exact (mulIsogeny E n hn).toHom_ne_zero h

theorem cross_eq (Q₁ Q₂ : isogHom E E') :
    homComp (homDual Q₁) Q₂ + homComp (homDual Q₂) Q₁ =
      (homDeg (Q₁ + Q₂) - homDeg Q₁ - homDeg Q₂) • homId := by
  have h := homComp_homDual_self (Q₁ + Q₂)
  rw [map_add, homComp_add_left, homComp_add_right, homComp_add_right, homComp_homDual_self,
    homComp_homDual_self] at h
  rw [sub_smul, sub_smul, ← h]
  abel

noncomputable def degBilin (Q₁ Q₂ : isogHom E E') : ℤ := homDeg (Q₁ + Q₂) - homDeg Q₁ - homDeg Q₂

theorem degBilin_smul_homId (Q₁ Q₂ : isogHom E E') :
    degBilin Q₁ Q₂ • (homId : isogEnd E) =
      homComp (homDual Q₁) Q₂ + homComp (homDual Q₂) Q₁ :=
  (cross_eq Q₁ Q₂).symm

theorem degBilin_add_left (Q₁ Q₁' Q₂ : isogHom E E') :
    degBilin (Q₁ + Q₁') Q₂ = degBilin Q₁ Q₂ + degBilin Q₁' Q₂ := by
  apply sub_eq_zero.mp
  apply eq_zero_of_zsmul_homId (E := E)
  rw [sub_smul, add_smul, degBilin_smul_homId, degBilin_smul_homId, degBilin_smul_homId, map_add,
    homComp_add_left, homComp_add_right]
  abel

theorem degBilin_comm (Q₁ Q₂ : isogHom E E') : degBilin Q₁ Q₂ = degBilin Q₂ Q₁ := by
  rw [degBilin, degBilin, add_comm]; ring

theorem degBilin_add_right (Q₁ Q₂ Q₂' : isogHom E E') :
    degBilin Q₁ (Q₂ + Q₂') = degBilin Q₁ Q₂ + degBilin Q₁ Q₂' := by
  rw [degBilin_comm, degBilin_add_left, degBilin_comm Q₂, degBilin_comm Q₂']

theorem degBilin_zsmul_left (c : ℤ) (Q₁ Q₂ : isogHom E E') :
    degBilin (c • Q₁) Q₂ = c • degBilin Q₁ Q₂ :=
  (AddMonoidHom.mk' (fun Q => degBilin Q Q₂) (fun a b => degBilin_add_left a b Q₂)).map_zsmul c Q₁

theorem degBilin_zsmul_right (c : ℤ) (Q₁ Q₂ : isogHom E E') :
    degBilin Q₁ (c • Q₂) = c • degBilin Q₁ Q₂ :=
  (AddMonoidHom.mk' (fun Q => degBilin Q₁ Q) (fun a b => degBilin_add_right Q₁ a b)).map_zsmul c Q₂

theorem homDeg_zsmul (n : ℤ) (Q : isogHom E E') : homDeg (n • Q) = n ^ 2 * homDeg Q := by
  by_cases hn : n = 0
  · subst hn; rw [zero_smul, homDeg_zero]; ring
  by_cases hQ : Q = 0
  · subst hQ; rw [smul_zero, homDeg_zero, mul_zero]
  set φ := isogOfHom Q hQ
  have e : n • Q = ((mulIsogeny E' n hn).comp φ).toHom := by
    refine Subtype.ext ?_
    rw [Isogeny.toHom_val, Isogeny.mulIsogeny_comp_val]
    rfl
  rw [e, homDeg_toHom, Isogeny.degree_comp, degree_mulIsogeny, ← isogOfHom_toHom Q hQ,
    homDeg_toHom]
  push_cast
  rw [sq_abs]

noncomputable def degForm : QuadraticForm ℤ (isogHom E E') where
  toFun := homDeg
  toFun_smul a Q := by rw [homDeg_zsmul, smul_eq_mul]; ring
  exists_companion' := ⟨LinearMap.mk₂ ℤ degBilin degBilin_add_left degBilin_zsmul_left
    degBilin_add_right degBilin_zsmul_right,
    fun Q₁ Q₂ => by rw [LinearMap.mk₂_apply, degBilin]; ring⟩

namespace Isogeny

theorem exists_dual (φ : Isogeny E E') :
    ∃ ψ : Isogeny E' E,
      ψ.comp φ = mulIsogeny E φ.degree (Nat.cast_ne_zero.mpr φ.degree_pos.ne') ∧
      φ.comp ψ = mulIsogeny E' φ.degree (Nat.cast_ne_zero.mpr φ.degree_pos.ne') ∧
      ψ.degree = φ.degree :=
  ⟨φ.dual, φ.dual_comp, φ.comp_dual, φ.degree_dual⟩

end Isogeny

end GroundTheory.Arith.Abelian
