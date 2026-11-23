import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Definitions.Degenerations.RigGen
import Development.AbelianVarietyTheory.BlockTheory.CMModuli.UniformityLowerBounds
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaPtEqUnitMulTh

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ThetaCompare

private theorem pow_eq_one_of_three_pow_relations {G : Type*} [CommGroup G] (M : ℕ) (U0 Ax Ap A0 F R : G)
    (h1 : U0 ^ M * (Ax ^ M * Ap) = A0 ^ M * A0) (h2 : F ^ M * A0 = Ap * R ^ M) (h3 : A0 = R ^ M * R⁻¹) :
    (U0 * Ax * F * (R ^ M)⁻¹) ^ M = 1 := by
  rw [mul_pow, mul_pow, mul_pow, inv_pow, mul_inv_eq_one]
  apply mul_right_cancel (b := Ap * A0)
  calc U0 ^ M * Ax ^ M * F ^ M * (Ap * A0) = (U0 ^ M * (Ax ^ M * Ap)) * (F ^ M * A0) := by ac_rfl
    _ = (A0 ^ M * A0) * (Ap * R ^ M) := by rw [h1, h2]
    _ = (A0 ^ M * R ^ M) * (Ap * A0) := by ac_rfl
    _ = (R ^ M) ^ M * (Ap * A0) := by
      congr 1
      rw [h3, mul_pow, inv_pow, _root_.mul_assoc, inv_mul_cancel, _root_.mul_one]

open CommPairing in

theorem normalised_root_stalk {S : Scheme.{0}} (hG : GlobalFnsSt) (P : PolAV S) {T : Over S} {m : ℕ} (hm : Odd m)
    {rig : LB.Gen (P.L.pull (eSec P.A))} {th : LB.Sec (LPow P.A P.L 1 T)} {x p : T ⟶ P.A} (hx : x ^ m = p)
    {fr : LB.Gen (LB.LinComb P.L (Y := T.left) (K := Fin 1) (fun _ => p.left) (fun _ => 1))}
    (hfr : IsTorsFrame P rig m p fr) {t v : Γ(T.left, ⊤)} (ht : IsValueAt P.A P.L 1 th p fr t)
    (a : ℤ) (ha : a = (m : ℤ) ^ 2) {s₁ s₂ : LB.Sec (LPow P.A P.L a T)}
    (h₁ : GlobalTheory.IndefiniteRowSideFullHecke.UniformityLowerBounds.IsMulPull P rig m a th s₁) {U : ThetaGrp P.A P.L a T}
    (hU : SymLift P.A P.L a (m ^ 2) x U) (hs₂ : IsActOf P.A P.L a U s₁ s₂)
    (h₃ : GlobalTheory.IndefiniteRowSideFullHecke.UniformityLowerBounds.IsValueZero P rig a s₂ v) (y : T.left) :
    ∃ ξ : (T.left.presheaf.stalk y)ˣ, ξ ^ (m ^ 2) = 1 ∧ gs (𝟙 _) y ⊤ v = ξ.val * gs (𝟙 _) y ⊤ t := by
  subst ha
  unfold IsActOf at hs₂
  obtain ⟨α, hα, hαn, htw⟩ := h₁
  obtain ⟨τ₀, -, hτ₀, hval⟩ := h₃
  obtain ⟨J, hJ, -⟩ := exists_good (L := P.L) P.isLB y (Empty.elim : Empty → (T.left ⟶ P.A.left)) Empty.elim
    (fun a => a.elim) (fun a => a.elim)
  have hxM : x ^ (m ^ 2) = 1 := by rw [sq, pow_mul, hx, hfr.1]
  have hR : ∀ k : ℕ, val rig T.hom y J ^ (k : ℤ) = val rig T.hom y J ^ k := fun k => zpow_natCast _ _
  have e1 := sval_valueAt hval hJ
  have e2 := sval_twist hs₂ (ptSecT P.A 1).left hJ
  have hpt : (ptSecT P.A (U.pt * 1)).left = (ptSecT P.A x).left := by rw [_root_.mul_one, hU.pt_eq]
  rw [pt_translT, hpt] at e2
  have e3 := sval_twist htw (ptSecT P.A x).left hJ
  rw [pt_mulT, hx] at e3
  have e4 := sval_valueAt ht hJ
  have e5 : val τ₀ (𝟙 _) y J = val rig T.hom y J ^ (m ^ 2) := by
    rw [val_corr hJ hτ₀, val_rigT rig _ hJ, ← Nat.cast_pow, hR]
  have F1 := frame_pow hG P hm hα hxM hU hJ
  rw [hx] at F1
  have F2 := torsFrame_pow hG P hα hfr hJ
  have F3 := val_corr hJ hαn (𝟙 _)
  rw [val_pull hJ, val_mul hJ, val_inv, val_rigT rig _ hJ, val_rigT rig _ hJ, Category.id_comp] at F3
  have F3' : val α (ptSecT P.A 1).left y J = val rig T.hom y J ^ (m ^ 2) * (val rig T.hom y J)⁻¹ := by
    rw [F3, zpow_one, ← hR, Nat.cast_pow]
  refine ⟨tval U (ptSecT P.A 1).left y J * val α (ptSecT P.A x).left y J * val fr (𝟙 _) y J *
    (val rig T.hom y J ^ (m ^ 2))⁻¹, pow_eq_one_of_three_pow_relations _ _ _ _ _ _ _ F1 F2 F3', ?_⟩
  calc gs (𝟙 _) y ⊤ v = gs (𝟙 _) y ⊤ v * (val τ₀ (𝟙 _) y J).val * (val τ₀ (𝟙 _) y J)⁻¹.val := by
        rw [_root_.mul_assoc, Units.mul_inv, _root_.mul_one]
    _ = _ := by
        rw [← e1, e2, e3, e4, e5, show tval U (ptSecT P.A 1).left y J = val U.φ (ptSecT P.A 1).left y J from rfl]
        simp only [Units.val_mul]
        ring

end GlobalTheory.ThetaCompare

namespace GlobalTheory

end GlobalTheory
