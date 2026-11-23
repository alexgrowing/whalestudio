import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.LatCDefs
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.GalOCOkToOC

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open GroundTheory.PAdicHodge Formalism.Per6 DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Lat

namespace GlobalTheory.CompanionTheory.LatC.Red

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} {M : ℕ}

theorem ι_lam_ainf (h : LevHyp l K M) (k : ℕ) (w : Ainf l) :
    (lev h k).ι ((lev h k).lam (algebraMap (Ainf l) (Acris l) w)) = fk l k w := by
  show pk l k (ACris.iota ℂ_[l] l (algebraMap (Ainf l) (Acris l) w)) = _
  rw [ACris.iota_algebraMap]
  rfl

theorem pk_mem_of_theta (k : ℕ) {d : BdRp l} (hd : IsPerfectoidField.thetaBDeRhamPlusField (K := ℂ_[l]) l d = 0) :
    pk l k d ∈ IB (fk l k) (xi0 l) := by
  have h1 : d ∈ RingHom.ker (IsPerfectoidField.thetaBDeRhamPlusField (K := ℂ_[l]) l) := hd
  rw [IsPerfectoidField.ker_thetaBDeRhamPlusField, ker_thetaBDeRhamPlus ker_theta0,
    Ideal.mem_span_singleton'] at h1
  obtain ⟨c, rfl⟩ := h1
  rw [map_mul]
  exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)

theorem xi_and_sub_mem_I (h : LevHyp l K M) (k : ℕ) :
    (lev h k).lam (algebraMap (Ainf l) (Acris l) (xi0 l)) ∈ (lev h k).I ∧
      ∀ (a : OK l K) (w : Ainf l), theta0 l w = okToOC l K a →
        algebraMap (OK l K) (lev h k).A a - (lev h k).lam (algebraMap (Ainf l) (Acris l) w) ∈ (lev h k).I := by
  refine ⟨?_, fun a w hw => ?_⟩
  · show (lev h k).ι _ ∈ IB (fk l k) (xi0 l)
    rw [ι_lam_ainf]
    exact Ideal.mem_span_singleton_self _
  · show (lev h k).ι _ ∈ IB (fk l k) (xi0 l)
    have e : (lev h k).ι (algebraMap (OK l K) (lev h k).A a) = pk l k (kP l K (a : K)) := rfl
    have e2 : (lev h k).ι ((lev h k).lam (algebraMap (Ainf l) (Acris l) w)) =
        pk l k (wittToBDeRhamPlus (normInteger ℂ_[l]) l w) := ι_lam_ainf h k w
    have e3 : (lev h k).ι (algebraMap (OK l K) (lev h k).A a -
        (lev h k).lam (algebraMap (Ainf l) (Acris l) w)) =
        pk l k (kP l K (a : K) - wittToBDeRhamPlus (normInteger ℂ_[l]) l w) := by
      rw [map_sub, e, e2, map_sub]
    rw [e3]
    apply pk_mem_of_theta
    rw [map_sub, IsPerfectoidField.thetaBDeRhamPlusField_wittToBDeRhamPlus, sub_eq_zero]
    have := thetaAlgHom_algClToBdR l (K.val (a : K))
    rw [thetaAlgHom_apply] at this
    refine this.trans ?_
    show _ = ((theta0 l w : OC l) : ℂ_[l])
    rw [hw]
    rfl

end GlobalTheory.CompanionTheory.LatC.Red
