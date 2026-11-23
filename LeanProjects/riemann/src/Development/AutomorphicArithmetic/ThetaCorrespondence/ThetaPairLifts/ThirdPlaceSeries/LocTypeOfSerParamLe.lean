import Development.DiscreteGroups.GlobalIrreducibility.LocTypeOfSerParamLe
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LocComp

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace DiscreteGroups.sglob.DzType.Rt
open Polynomial GlobalTheory.GLq GlobalTheory.GLp Formalism.BasicNotions Formalism.MainNotions.N Formalism.MainNotions.ArithmeticCylinders GlobalTheory.SerSys
open scoped Classical
attribute [local instance] GlobalTheory.SerSys.factTypePrime
variable {g : ℕ} [Fact g.Prime]
theorem locType_of_serParamLe_alt {D : D7} {S : ∀ k, Sys (D.host.g k)} {rc : Corr D} (hC : _root_.GlobalTheory.SerSys.LocalCompatibility D rc)
    (hP : ∀ k v, SerParamLe D.R.nV (S k).e (D.ntypes.teichC k) fun n π => D.naut.inePol (rc k v n π) (D.ntypes.tg k v)) :
    LocType D S := by
  intro i P k v
  obtain ⟨μ, χ, hμ, h1, h2⟩ := hC.2 i k v
  obtain ⟨π, hπ, h3, h4⟩ := h2 P
  obtain ⟨f, hf, hm, hd, -⟩ := Loc.exists_charIn (S k) χ 1
  obtain ⟨c, rfl⟩ : ∃ c, f = X - C c := ⟨-f.coeff 0, by rw [C_neg, sub_neg_eq_add]; exact hm.eq_X_add_C hd⟩
  refine ⟨π, χ, c, fun F hF a ha h0 => h4.exists_parVec hF ha h0, Loc.charIn_pow _ χ hf _, ?_,
    fun f' hf' => h3 ▸ hP k v _ le_rfl π hπ f' hf'⟩
  rw [h1, ← Loc.prod_linear]
  exact hP k v 1 (one_le_nV D) _ (Loc.irrSm_det hμ) _ ((Loc.has_det hμ (S k) _).2 hf)
theorem locType_of_labTie_locComp_labParamLe {D : D7} {L : ∀ k, LabelDatum (D.host.g k)} {S : ∀ k, Sys (D.host.g k)} {rc : Corr D}
    (hL : LabTie D L) (hS : ∀ k, (S k).IsOf (L k)) (hC : _root_.GlobalTheory.SerSys.LocalCompatibility D rc) (hP : LabParamLe D.R.nV D L rc) :
    LocType D S :=
  _root_.DiscreteGroups.sglob.DzType.Rt.locType_of_serParamLe_alt hC fun k v => by
    rw [← (hL k).1, show (S k).e = eSerC (L k) from _root_.funext fun n => _root_.funext (hS k n)]
    exact hP k v
end DiscreteGroups.sglob.DzType.Rt
end
end
