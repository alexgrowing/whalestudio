import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.GoodChi

open Formalism.BasicNotions GlobalTheory.Mem GlobalTheory.MemN NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial

namespace GlobalTheory.MemN

theorem nonempty_nbc_of_isEmpty_loc :
    ∀ (R : Ranks) (H : Host R) (what₂ : Rows.Data R) (nd : NData R H what₂) (A : NAut nd),
      IsEmpty nd.Loc → Nonempty (NBC A) := by
  intro R H what₂ nd A hL
  exact ⟨{
    AU := fun _ => Empty
    multAU := fun _ x => x.elim
    sphAU := fun _ x => x.elim
    locAU := fun _ x => x.elim
    satAU := fun _ x => x.elim
    satAU_card := fun _ x => x.elim
    Wt := fun _ => Empty
    infW := fun _ x => x.elim
    infW_card := fun _ x => x.elim
    wtAU := fun _ x => x.elim
    infW_alg := fun _ x => x.elim
    embAV := fun i => hL.elim i
    embAV_inj := fun i => hL.elim i
    embAV_loc := fun i => hL.elim i
    embAV_sat := fun i => hL.elim i
    embAV_sph := fun i => hL.elim i
    embAV_inf := fun i => hL.elim i }⟩

end GlobalTheory.MemN
