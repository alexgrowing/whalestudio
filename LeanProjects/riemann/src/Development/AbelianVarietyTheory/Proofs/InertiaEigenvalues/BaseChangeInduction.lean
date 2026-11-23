import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeCrystallineLattices
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ConductorExponents

namespace GlobalTheory.BaseChangeInduction

theorem baseChange_induction {A B M N : Type} [CommRing A] [CommRing B] [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module B N] {f : A →+* B} {u : M →ₛₗ[f] N} (h : GlobalTheory.Prism.SemiBC u)
    (p : N → Prop) (hzero : p 0) (hadd : ∀ y z, p y → p z → p (y + z))
    (hsmul : ∀ (r : B) (y : N), p y → p (r • y)) (himg : ∀ x : M, p (u x)) (y : N) : p y := by
  let S : Submodule B N :=
    { carrier := {n | p n}
      zero_mem' := hzero
      add_mem' := fun {a b} ha hb => hadd a b ha hb
      smul_mem' := fun r n hn => hsmul r n hn }
  have hq : S.mkQ = 0 := by
    refine (h (N ⧸ S) 0).unique (fun x => ?_) (fun x => rfl)
    exact (Submodule.Quotient.mk_eq_zero S).2 (himg x)
  have hy : S.mkQ y = 0 := by rw [hq]; rfl
  exact (Submodule.Quotient.mk_eq_zero S).1 hy

end GlobalTheory.BaseChangeInduction
