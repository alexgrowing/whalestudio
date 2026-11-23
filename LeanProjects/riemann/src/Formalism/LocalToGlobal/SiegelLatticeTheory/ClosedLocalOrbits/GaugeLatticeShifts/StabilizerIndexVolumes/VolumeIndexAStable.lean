import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.PairVal
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.StabilizerIndexVolumes.VolumeIndexFiniteNonzero
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.StabilizerIndexVolumes.StClosed
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.StabilizerIndexVolumes.AtNormRep

noncomputable section

open scoped Classical

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.TermDef Formalism.L2.SG.PairVal

namespace Formalism.L2.SG.Pf.StabilizerIndexVolumes

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem closure_subset_StSet (hSt : StClosed) {E : Type} [Field E] [NumberField E] {n : ℕ}
    (W : Matrix (Fin n) (Fin n) E) (K : Set (Matrix.GeneralLinearGroup (Fin n) E))
    (hK : K ⊆ StSet W) : ((Subgroup.closure K : Subgroup _) : Set _) ⊆ StSet W := by
  obtain ⟨h1, hm, hi⟩ := hSt E n W
  intro x hx
  induction hx using Subgroup.closure_induction with
  | mem x hx => exact hK hx
  | one => exact h1
  | mul x y _ _ hx hy => exact hm x hx y hy
  | inv x _ hx => exact hi x hx

theorem volume_index_a_stable (D : D7) (u u' : D.what₂.Word)
    (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E))
    (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V))
    (δ : ∀ p : Formalism.MainNotions.S.LocalSplitGroups.PlF D, (D.s.atP p).Fp)
    (M : ∀ p : Formalism.MainNotions.S.LocalSplitGroups.PlF D, Formalism.MainNotions.S.Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) :
    AinSt D u u' F0 what₂ δ M := by
  intro hSt _ _ t w F' L U _ _ _ _
  apply closure_subset_StSet hSt
  rintro a ⟨h1, b, hb, hab, _⟩
  exact ⟨h1, b, hb, hab⟩

example (D : D7) (u u' : D.what₂.Word)
    (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E))
    (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V))
    (δ : ∀ p : Formalism.MainNotions.S.LocalSplitGroups.PlF D, (D.s.atP p).Fp)
    (M : ∀ p : Formalism.MainNotions.S.LocalSplitGroups.PlF D, Formalism.MainNotions.S.Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) :
    AinSt D u u' F0 what₂ δ M := volume_index_a_stable D u u' F0 what₂ δ M

end Formalism.L2.SG.Pf.StabilizerIndexVolumes
