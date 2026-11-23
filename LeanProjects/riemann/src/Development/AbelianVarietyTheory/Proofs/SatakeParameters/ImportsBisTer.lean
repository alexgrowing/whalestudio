import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Formalism.SharpRestriction.LevelLetterCocycles.ExistsInertiaCharpolyFactorOfTameType
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LabelSettingTameGenerator
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsOfFinOrderFbar

noncomputable section

namespace GlobalTheory.TieLabAt

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField
  IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem main : ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (P : Pin hL D),
    Formalism.MainNotions.SumRepresentations.tieLab D ∧ LabTame D.nd D.naut ∧ IotaRed D ∧ GlobalTheory.RowCopy.RbarTie D := by
  intro hL D P
  let γ : Fin 2 → PlE D.host → G D.host.E D.nd.Om := fun k => Function.extend (D.naut.plGw k) (D.ntypes.tg k) (fun _ => 1)
  have hγ : ∀ k v, γ k (D.naut.plGw k v) = D.ntypes.tg k v := fun k v => (D.naut.plGw_inj k).extend_apply _ _ v
  have hT : GlobalTheory.LabLaws.LabTie P.T D.ntypes.teichC γ := by
    intro k v
    rw [hγ k v]
    exact ⟨D.ntypes.teichC_inj k, D.ntypes.tg_gen k v, P.lab k v⟩
  refine ⟨GlobalTheory.LabLaws.tieLab_of_labTie hT, GlobalTheory.LabLaws.labTame_of_labTie hT, ?_, ⟨P.ty.rbarSS, P.ty.rbar⟩⟩
  intro i
  refine ⟨P.ty.plB (D.nd.w i), P.ty.plκ (D.nd.w i), fun y => P.ty.plB_loc i y, fun k v x => ?_⟩
  haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
  have hm := GlobalTheory.ParRay.mem_of_monoidHom (P.ty.plB (D.nd.w i)) (D.ntypes.teichC k) x
  refine ⟨hm, ?_⟩
  rw [P.ty.plB_iota i k v x]
  unfold redThrough
  exact dif_pos hm

end GlobalTheory.TieLabAt

end
