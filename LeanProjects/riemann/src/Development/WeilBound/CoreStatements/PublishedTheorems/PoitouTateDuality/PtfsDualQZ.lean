import Mathlib
import GroundTheory.ProfiniteCohomology.PoitouTate.PoitouTateNineTermGs

noncomputable section

open GroundTheory.ProfCoh

namespace PositivityTheory.Lit1.PTN

theorem nsmul_eq_zero_of_zmod {N : ℕ} {X : Type} [AddCommGroup X] [Module (ZMod N) X] (a : X) :
    N • a = 0 := by
  rw [← Nat.cast_smul_eq_nsmul (ZMod N), ZMod.natCast_self, zero_smul]

def dualQZ {N : ℕ} [NeZero N] {X Y : Type} [AddCommGroup X] [Module (ZMod N) X] [AddCommGroup Y]
    (E : X ≃+ Y) : Module.Dual (ZMod N) X ≃+ (Y →+ QZ) where
  toFun φ := (zmodToQZ N).comp (φ.toAddMonoidHom.comp E.symm.toAddMonoidHom)
  invFun ψ := (zmodOfQZ (ψ.comp E.toAddMonoidHom) (fun a => by
      rw [← map_nsmul, nsmul_eq_zero_of_zmod, map_zero])).toZModLinearMap N
  left_inv φ := LinearMap.ext fun a => zmodToQZ_injective (by
    simp [zmodToQZ_zmodOfQZ])
  right_inv ψ := AddMonoidHom.ext fun y => by
    simp [zmodToQZ_zmodOfQZ]
  map_add' φ φ' := AddMonoidHom.ext fun y => by simp

theorem dualQZ_apply {N : ℕ} [NeZero N] {X Y : Type} [AddCommGroup X] [Module (ZMod N) X]
    [AddCommGroup Y] (E : X ≃+ Y) (φ : Module.Dual (ZMod N) X) (y : Y) :
    dualQZ E φ y = zmodToQZ N (φ (E.symm y)) := rfl

end PositivityTheory.Lit1.PTN
