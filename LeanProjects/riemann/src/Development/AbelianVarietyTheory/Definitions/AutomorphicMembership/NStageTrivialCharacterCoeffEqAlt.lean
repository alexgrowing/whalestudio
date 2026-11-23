import Mathlib
import Formalism.LocalToGlobal.UnitaryNorms.CharTied
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AssembleLattice

noncomputable section

namespace GlobalTheory.HeightCounting

open Formalism.BasicNotions Formalism.L2.Host NumberField IsDedekindDomain

def rowsEta {R : Ranks} (what₂ : Rows.Data R) (η : ℕ → what₂.places.Pl → ℚ) (hη : ∀ j w, 0 ≤ η j w) : Rows.Data R :=
  { what₂ with etaJ := η, etaJ_nonneg := hη }

structure NLay0 (R : Ranks) (H : Host R) (what₂ : Rows.Data R) [NumberField what₂.LL] [StarRing what₂.LL]
    (LL0 : IntermediateField ℚ what₂.LL) where
  loc : LocTheory
  locA : ∀ (l : ℕ) [Fact l.Prime], LocAinf l (loc l)
  locT : ∀ (l : ℕ) [Fact l.Prime], LocTied l (loc l) (locA l)
  nd : NData R H what₂
  ntw : NTw R H what₂ LL0 nd
  naut : NAut nd
  nbc : NBC naut
  nexp : NExp R H what₂ LL0 nd ntw
  ntypes : NTypes naut
  nStage_trivialCharacter_compat : ntypes.IdempotentMatchesAction
  nStage_trivialCharacter_coeff_eq : ∀ g : G0g nd, what₂.embLL ((nexp.eLL0 g : ↥LL0) : what₂.LL) = ntypes.e0.coeff g
  nth : NTh R H what₂ LL0 nd ntw nexp
  nbr : ∀ (i : nd.Loc) (w : HeightOneSpectrum (𝓞 H.E)), w ∈ Formalism.BasicNotions.placesOver H.E (nd.l i) →
    Formalism.BasicNotions.LocBridge (nd.l i) H.E nd.Om (ReciprocityTheory.Gal.Dec (F := H.E) (nd.plOm.1 w)) (nd.O i)
  nbr_ind : ∀ (i : nd.Loc) (w : HeightOneSpectrum (𝓞 H.E)) (hw : w ∈ Formalism.BasicNotions.placesOver H.E (nd.l i))
    (x : nd.Om), x ∈ nd.plOm.1 w ↔ ‖(nbr i w hw).j x‖ ≤ 1
  self_good : ∀ (i : nd.Loc) (w : HeightOneSpectrum (𝓞 H.E)) (hw : w ∈ Formalism.BasicNotions.placesOver H.E (nd.l i)),
    Formalism.BasicNotions.Loc.GoodCoef H.condN (nbr i w hw).LL
  ntwbr : ∀ (i : ntw.Tw) (w : HeightOneSpectrum (𝓞 H.E)), w ∈ Formalism.BasicNotions.placesOver H.E (ntw.l i) →
    Formalism.BasicNotions.LocBridge (ntw.l i) H.E nd.Om (ReciprocityTheory.Gal.Dec (F := H.E) (nd.plOm.1 w)) (ntw.O0 i)
  ntwbr_ind : ∀ (i : ntw.Tw) (w : HeightOneSpectrum (𝓞 H.E)) (hw : w ∈ Formalism.BasicNotions.placesOver H.E (ntw.l i))
    (x : nd.Om), x ∈ nd.plOm.1 w ↔ ‖(ntwbr i w hw).j x‖ ≤ 1
  loc_tie : Formalism.MainNotions.N.LocTie nd naut loc nbr
  bc_tie : Formalism.MainNotions.N.BcTie nd naut ntypes
  rbar_tie : Formalism.MainNotions.N.RbarTie nd naut ntypes
  mtpar_tie : Formalism.MainNotions.N.MtParTie nd naut ntypes

section
variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} [NumberField what₂.LL] [StarRing what₂.LL]
    {LL0 : IntermediateField ℚ what₂.LL}

def NLay0.ZOk (L : NLay0 R H what₂ LL0) : Prop :=
  (∀ i x, x ∈ L.nd.Z i ↔ x ∈ Formalism.MainNotions.N.ZN L.nd L.naut i) ∧ ∀ i x, x ∈ L.nd.Zgood i ↔ x ∈ Formalism.MainNotions.N.ZgoodN L.nd L.naut i

def ndZ (N : NData R H what₂) (Z Zg : ∀ i, Finset (N.X i)) : NData R H what₂ := { N with Z := Z, Zgood := Zg }

set_option maxHeartbeats 2000000 in

def NLay0.setZ (L : NLay0 R H what₂ LL0) (Z Zg : ∀ i, Finset (L.nd.X i)) : NLay0 R H what₂ LL0 :=
  { loc := L.loc, locA := L.locA, locT := L.locT, nd := ndZ L.nd Z Zg, ntw := { L.ntw with }, naut := { L.naut with }
    nbc := { L.nbc with }, nexp := { L.nexp with }, ntypes := { L.ntypes with }, nStage_trivialCharacter_compat := L.nStage_trivialCharacter_compat, nStage_trivialCharacter_coeff_eq := L.nStage_trivialCharacter_coeff_eq
    nth := { L.nth with }, nbr := L.nbr, nbr_ind := L.nbr_ind, self_good := L.self_good, ntwbr := L.ntwbr
    ntwbr_ind := L.ntwbr_ind, loc_tie := L.loc_tie, bc_tie := L.bc_tie, rbar_tie := L.rbar_tie, mtpar_tie := L.mtpar_tie }

open Classical in

def NLay0.fixZ (L : NLay0 R H what₂ LL0) : NLay0 R H what₂ LL0 :=
  L.setZ (fun i => Finset.univ.filter fun x => x ∈ Formalism.MainNotions.N.ZN L.nd L.naut i)
    (fun i => Finset.univ.filter fun x => x ∈ Formalism.MainNotions.N.ZgoodN L.nd L.naut i)

set_option maxHeartbeats 2000000 in

def NLay0.reEta (L : NLay0 R H what₂ LL0) (η : ℕ → what₂.places.Pl → ℚ) (hη : ∀ j w, 0 ≤ η j w) :
    @NLay0 R H (rowsEta what₂ η hη) ‹NumberField what₂.LL› ‹StarRing what₂.LL› LL0 :=
  letI : NumberField (rowsEta what₂ η hη).LL := ‹NumberField what₂.LL›
  letI : StarRing (rowsEta what₂ η hη).LL := ‹StarRing what₂.LL›
  { loc := L.loc, locA := L.locA, locT := L.locT, nd := { L.nd with }, ntw := { L.ntw with }, naut := { L.naut with }
    nbc := { L.nbc with }, nexp := { L.nexp with }, ntypes := { L.ntypes with }, nStage_trivialCharacter_compat := L.nStage_trivialCharacter_compat, nStage_trivialCharacter_coeff_eq := L.nStage_trivialCharacter_coeff_eq
    nth := { L.nth with }, nbr := L.nbr, nbr_ind := L.nbr_ind, self_good := L.self_good, ntwbr := L.ntwbr
    ntwbr_ind := L.ntwbr_ind, loc_tie := L.loc_tie, bc_tie := L.bc_tie, rbar_tie := L.rbar_tie, mtpar_tie := L.mtpar_tie }

open Classical in

def NLay0.eta (L : NLay0 R H what₂ LL0) (j : ℕ) (w : what₂.places.Pl) : ℚ :=
  if 1 ≤ j ∧ j ≤ R.m then ∑ i ∈ L.nd.locs j w, L.nd.etaLoc i else what₂.etaJ j w

theorem NLay0.eta_nonneg (L : NLay0 R H what₂ LL0) (j : ℕ) (w : what₂.places.Pl) : 0 ≤ L.eta j w := by
  unfold NLay0.eta
  split_ifs
  · exact Finset.sum_nonneg fun i _ => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  · exact what₂.etaJ_nonneg j w

theorem NLay0.zOk_fixZ (L : NLay0 R H what₂ LL0) : L.fixZ.ZOk := by
  classical
  refine ⟨fun i x => ?_, fun i x => ?_⟩
  · exact ((@Finset.mem_filter _ _ (fun _ => Classical.propDecidable _) _ _).trans (and_iff_right (Finset.mem_univ _)))
  · exact ((@Finset.mem_filter _ _ (fun _ => Classical.propDecidable _) _ _).trans (and_iff_right (Finset.mem_univ _)))

set_option maxHeartbeats 1000000 in
theorem NLay0.ZOk.reEta {L : NLay0 R H what₂ LL0} (h : L.ZOk) (η : ℕ → what₂.places.Pl → ℚ) (hη : ∀ j w, 0 ≤ η j w) :
    @NLay0.ZOk R H (rowsEta what₂ η hη) ‹NumberField what₂.LL› ‹StarRing what₂.LL› LL0 (L.reEta η hη) := h

def NLay0.EtaOk (L : NLay0 R H what₂ LL0) : Prop :=
  ∀ j w, 1 ≤ j → j ≤ R.m → what₂.etaJ j w = ∑ i ∈ L.nd.locs j w, L.nd.etaLoc i

set_option maxHeartbeats 1000000 in
theorem NLay0.etaOk_reEta (L : NLay0 R H what₂ LL0) :
    @NLay0.EtaOk R H (rowsEta what₂ L.eta L.eta_nonneg) ‹NumberField what₂.LL› ‹StarRing what₂.LL› LL0
      (L.reEta L.eta L.eta_nonneg) := fun _ _ h1 h2 => if_pos ⟨h1, h2⟩

end

abbrev Lay0 (D : D7) : Type _ := NLay0 D.R D.host D.what₂ D.LL0

set_option maxHeartbeats 1000000 in

def setRaw (D : D7) (η : ℕ → D.what₂.places.Pl → ℚ) (hη : ∀ j w, 0 ≤ η j w)
    (P : @NLay0 D.R D.host (rowsEta D.what₂ η hη) D.nfLL D.starLL D.LL0)
    (hZ : @NLay0.ZOk D.R D.host (rowsEta D.what₂ η hη) D.nfLL D.starLL D.LL0 P)
    (hE : @NLay0.EtaOk D.R D.host (rowsEta D.what₂ η hη) D.nfLL D.starLL D.LL0 P) : D7 :=
  letI : NumberField (rowsEta D.what₂ η hη).LL := D.nfLL
  letI : StarRing (rowsEta D.what₂ η hη).LL := D.starLL
  { D with
    what₂ := rowsEta D.what₂ η hη
    loc := P.loc, locA := P.locA, locT := P.locT, nd := P.nd, ntw := P.ntw, naut := P.naut, nbc := P.nbc, nexp := P.nexp
    ntypes := P.ntypes, nStage_trivialCharacter_compat := P.nStage_trivialCharacter_compat, nStage_trivialCharacter_coeff_eq := P.nStage_trivialCharacter_coeff_eq, nth := P.nth, nbr := P.nbr, nbr_ind := P.nbr_ind
    self_good := P.self_good, ntwbr := P.ntwbr, ntwbr_ind := P.ntwbr_ind, loc_tie := P.loc_tie, bc_tie := P.bc_tie
    rbar_tie := P.rbar_tie, mtpar_tie := P.mtpar_tie, Z_tie := hZ.1, Zgood_tie := hZ.2, etaJ_tie := hE }

def setN (D : D7) (L : Lay0 D) : D7 :=
  setRaw D L.fixZ.eta L.fixZ.eta_nonneg (L.fixZ.reEta L.fixZ.eta L.fixZ.eta_nonneg) (L.zOk_fixZ.reEta _ _) L.fixZ.etaOk_reEta

def setK (D : D7) (P : Lay0 D) (hZ : P.ZOk) (hE : P.EtaOk) : D7 :=
  { D with
    loc := P.loc, locA := P.locA, locT := P.locT, nd := P.nd, ntw := P.ntw, naut := P.naut, nbc := P.nbc, nexp := P.nexp
    ntypes := P.ntypes, nStage_trivialCharacter_compat := P.nStage_trivialCharacter_compat, nStage_trivialCharacter_coeff_eq := P.nStage_trivialCharacter_coeff_eq, nth := P.nth, nbr := P.nbr, nbr_ind := P.nbr_ind
    self_good := P.self_good, ntwbr := P.ntwbr, ntwbr_ind := P.ntwbr_ind, loc_tie := P.loc_tie, bc_tie := P.bc_tie
    rbar_tie := P.rbar_tie, mtpar_tie := P.mtpar_tie, Z_tie := hZ.1, Zgood_tie := hZ.2, etaJ_tie := hE }

def cfK {D : D7} (P : Lay0 D) (hZ : P.ZOk) (hE : P.EtaOk) (c : CharFrame D) : CharFrame (setK D P hZ hE) :=
  ⟨c.P, c.W, c.mu0, c.eta, c.chiPsi, c.del, c.del', c.isMu0, c.isEta, c.isChi, c.isDel, c.isDel'⟩

def cfTr {D : D7} (L : Lay0 D) (c : CharFrame D) : CharFrame (setN D L) :=
  ⟨c.P, c.W, c.mu0, c.eta, c.chiPsi, c.del, c.del', c.isMu0, c.isEta, c.isChi, c.isDel, c.isDel'⟩

def lay0 (D : D7) : Lay0 D :=
  { loc := D.loc, locA := D.locA, locT := D.locT, nd := D.nd, ntw := D.ntw, naut := D.naut, nbc := D.nbc, nexp := D.nexp
    ntypes := D.ntypes, nStage_trivialCharacter_compat := D.nStage_trivialCharacter_compat, nStage_trivialCharacter_coeff_eq := D.nStage_trivialCharacter_coeff_eq, nth := D.nth, nbr := D.nbr, nbr_ind := D.nbr_ind
    self_good := D.self_good, ntwbr := D.ntwbr, ntwbr_ind := D.ntwbr_ind, loc_tie := D.loc_tie, bc_tie := D.bc_tie
    rbar_tie := D.rbar_tie, mtpar_tie := D.mtpar_tie }

end GlobalTheory.HeightCounting

end
