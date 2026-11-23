import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.GaugeTopology.SSmoothW
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic
open scoped ValuativeRel

namespace GlobalTheory.CompanionTheory.LocalChar

theorem sInv : Ad3.LFS.SInv := by
  intro F _ _ _ _ _ _ ν hν
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · exact continuous_inv.comp hν.1
  · intro x
    rw [MonoidHom.inv_apply, Units.val_inv_eq_inv_val, norm_inv, hν.2 x, inv_one]
  · intro hu x hx
    have h : ν x = 1 := hu hx
    rw [MonoidHom.mem_ker, MonoidHom.inv_apply, h, inv_one]

end GlobalTheory.CompanionTheory.LocalChar
