import Mathlib
import Development.AutomorphicArithmetic.IntegralCasts.CrystallinePeriods.Period
import Development.AutomorphicArithmetic.IntegralCasts.CrystallinePeriods.Action
import Development.AutomorphicArithmetic.IntegralCasts.CrystallinePeriods.Embedding
import Development.WeilBound.CoreStatements.CrystallinePeriodRings.ExistsMapEqOfPowMul

noncomputable section

open GroundTheory.PAdicHodge

namespace Cmp6

variable (l : ℕ) [Fact l.Prime]

abbrev OC : Type := ↥(PadicComplexInt l)
abbrev NC : Type := ↥(normInteger ℂ_[l])

abbrev e : OC l ≃+* NC l := Formalism.Per6.intEquiv l

theorem gamma_eq_dpow (n : ℕ) (x : Reformulated.AutPerF.Ainf l (NC l)) :
    Reformulated.AutPerF.AinfInv.gamma n (algebraMap (Reformulated.AutPerF.Ainf l (NC l)) (Reformulated.AutPerF.AinfInv l (NC l)) x) =
      ACris.dpow n x := by
  symm
  rw [ACris.dpow_eq_iff]
  exact Reformulated.AutPerF.AinfInv.factorial_mul_gamma n _

theorem acrisZero_eq : Reformulated.AutPerF.acrisZero l (NC l) = ACris.ACrisZero ℂ_[l] l := by
  unfold Reformulated.AutPerF.acrisZero ACris.ACrisZero
  congr 1
  ext y
  constructor
  · rintro ⟨n, x, hx, rfl⟩
    exact ⟨n, x, RingHom.mem_ker.2 hx, (gamma_eq_dpow l n x).symm⟩
  · rintro ⟨n, x, hx, rfl⟩
    exact ⟨n, x, RingHom.mem_ker.1 hx, (gamma_eq_dpow l n x).symm⟩

def zeroEquiv : Reformulated.AutPerF.AcrisZero l (NC l) ≃+* ACris.ACrisZero ℂ_[l] l :=
  (Subalgebra.equivOfEq _ _ (acrisZero_eq l)).toRingEquiv

def acrisNHom : Reformulated.AutPerF.Acris l (NC l) →+* ACris.ACris ℂ_[l] l :=
  Reformulated.AutPerF.adicMap _ _ (zeroEquiv l).toRingHom (Reformulated.AutPerF.span_natCast_le_comap l _)

def acrisNInv : ACris.ACris ℂ_[l] l →+* Reformulated.AutPerF.Acris l (NC l) :=
  Reformulated.AutPerF.adicMap _ _ (zeroEquiv l).symm.toRingHom (Reformulated.AutPerF.span_natCast_le_comap l _)

def acrisN : Reformulated.AutPerF.Acris l (NC l) ≃+* ACris.ACris ℂ_[l] l :=
  RingEquiv.ofRingHom (acrisNHom l) (acrisNInv l)
    (RingHom.ext fun x => by
      change acrisNHom l (acrisNInv l x) = x
      exact (Reformulated.AutPerF.adicMap_adicMap _ _ _ _ _ (RingHom.id _) _ _
        (Reformulated.AutPerF.span_natCast_le_comap l _) (fun a => (zeroEquiv l).apply_symm_apply a) x).trans
        (Reformulated.AutPerF.adicMap_eq_id _ _ _ (fun _ => rfl) x))
    (RingHom.ext fun x => by
      change acrisNInv l (acrisNHom l x) = x
      exact (Reformulated.AutPerF.adicMap_adicMap _ _ _ _ _ (RingHom.id _) _ _
        (Reformulated.AutPerF.span_natCast_le_comap l _) (fun a => (zeroEquiv l).symm_apply_apply a) x).trans
        (Reformulated.AutPerF.adicMap_eq_id _ _ _ (fun _ => rfl) x))

def acrisO : Reformulated.AutPerF.Acris l (OC l) ≃+* Reformulated.AutPerF.Acris l (NC l) :=
  RingEquiv.ofRingHom (Reformulated.AutPerF.Acris.map l (e l).toRingHom)
    (Reformulated.AutPerF.Acris.map l (e l).symm.toRingHom)
    (RingHom.ext fun x => by
      rw [RingHom.comp_apply, RingHom.id_apply, Reformulated.AutPerF.Acris.map_map,
        show (e l).toRingHom.comp (e l).symm.toRingHom = RingHom.id _ from
          RingHom.ext fun y => (e l).apply_symm_apply y, Reformulated.AutPerF.Acris.map_id])
    (RingHom.ext fun x => by
      rw [RingHom.comp_apply, RingHom.id_apply, Reformulated.AutPerF.Acris.map_map,
        show (e l).symm.toRingHom.comp (e l).toRingHom = RingHom.id _ from
          RingHom.ext fun y => (e l).symm_apply_apply y, Reformulated.AutPerF.Acris.map_id])

def cA : Reformulated.AutPerF.Acris l (OC l) ≃+* ACris.ACris ℂ_[l] l := (acrisO l).trans (acrisN l)

theorem cA_apply (x : Reformulated.AutPerF.Acris l (OC l)) :
    cA l x = acrisNHom l (Reformulated.AutPerF.Acris.map l (e l).toRingHom x) := rfl

end Cmp6
