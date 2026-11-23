import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RowsRestWordColumnUnitBaseTuple

noncomputable section

namespace GlobalTheory.Mem

open Formalism.BasicNotions NumberField IsDedekindDomain

structure LocStage where
  loc : LocTheory
  locA : ∀ (l : ℕ) [Fact l.Prime], LocAinf l (loc l)
  locT : ∀ (l : ℕ) [Fact l.Prime], LocTied l (loc l) (locA l)

structure NStage (B : Base) (C : Cols B) (W : RowsRest B C) extends LocStage where
  nd : NData B.R B.host W.what₂
  ntw : NTw B.R B.host W.what₂ B.LL0 nd
  naut : NAut nd
  nbc : NBC naut
  nexp : NExp B.R B.host W.what₂ B.LL0 nd ntw
  ntypes : NTypes naut
  nStage_trivialCharacter_compat : ntypes.IdempotentMatchesAction
  nStage_trivialCharacter_coeff_eq : ∀ g : G0g nd, B.embLL ((nexp.eLL0 g : ↥B.LL0) : B.LL) = ntypes.e0.coeff g
  nth : NTh B.R B.host W.what₂ B.LL0 nd ntw nexp
  nbr : ∀ (i : nd.Loc) (w : HeightOneSpectrum (𝓞 B.host.E)), w ∈ Formalism.BasicNotions.placesOver B.host.E (nd.l i) →
    Formalism.BasicNotions.LocBridge (nd.l i) B.host.E nd.Om (ReciprocityTheory.Gal.Dec (F := B.host.E) (nd.plOm.1 w)) (nd.O i)
  nbr_ind : ∀ (i : nd.Loc) (w : HeightOneSpectrum (𝓞 B.host.E)) (hw : w ∈ Formalism.BasicNotions.placesOver B.host.E (nd.l i))
    (x : nd.Om), x ∈ nd.plOm.1 w ↔ ‖(nbr i w hw).j x‖ ≤ 1
  self_good : ∀ (i : nd.Loc) (w : HeightOneSpectrum (𝓞 B.host.E)) (hw : w ∈ Formalism.BasicNotions.placesOver B.host.E (nd.l i)),
    Formalism.BasicNotions.Loc.GoodCoef B.host.condN (nbr i w hw).LL
  ntwbr : ∀ (i : ntw.Tw) (w : HeightOneSpectrum (𝓞 B.host.E)), w ∈ Formalism.BasicNotions.placesOver B.host.E (ntw.l i) →
    Formalism.BasicNotions.LocBridge (ntw.l i) B.host.E nd.Om (ReciprocityTheory.Gal.Dec (F := B.host.E) (nd.plOm.1 w)) (ntw.O0 i)
  ntwbr_ind : ∀ (i : ntw.Tw) (w : HeightOneSpectrum (𝓞 B.host.E)) (hw : w ∈ Formalism.BasicNotions.placesOver B.host.E (ntw.l i))
    (x : nd.Om), x ∈ nd.plOm.1 w ↔ ‖(ntwbr i w hw).j x‖ ≤ 1
  loc_tie : Formalism.MainNotions.N.LocTie nd naut loc nbr
  bc_tie : Formalism.MainNotions.N.BcTie nd naut ntypes
  rbar_tie : Formalism.MainNotions.N.RbarTie nd naut ntypes
  mtpar_tie : Formalism.MainNotions.N.MtParTie nd naut ntypes
  Z_tie : ∀ i x, x ∈ nd.Z i ↔ x ∈ Formalism.MainNotions.N.ZN nd naut i
  Zgood_tie : ∀ i x, x ∈ nd.Zgood i ↔ x ∈ Formalism.MainNotions.N.ZgoodN nd naut i
  etaJ_tie : ∀ j w, 1 ≤ j → j ≤ B.R.m → W.etaJ j w = ∑ i ∈ nd.locs j w, nd.etaLoc i

end GlobalTheory.Mem

end
