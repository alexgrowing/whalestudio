import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistDataAgreeAcrossCoefficientsLocalized

noncomputable section

namespace GlobalTheory.HeightCounting.Fin3

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top
  GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 4000000

section Gen

open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.RecTie

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type}
  [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat3 D A3 Ks} {F : Face3 D A3} {X0 : BaseLevelRowSide D}

variable (R) in

def EigVec (i : Fin D.R.m) (k : ℕ) (Q : PlE D.host) (Rr : Finset (GA D (Wc D i))) (c : ↥D.LL0) (v : (R.HW i (sg0 D A3.A)).H) : Prop :=
  hkNorm R i k Q • heckeOn (R.MW i (sg0 D A3.A)) Rr ((R.HW i (sg0 D A3.A)).e v) =
    D.what₂.embLL ((c : ↥D.LL0) : D.what₂.LL) • (R.HW i (sg0 D A3.A)).e v

theorem eigAd_iff_eigVec (Y : R3.Read (A3 := A3) R.toRealDat F.lv2 X0) (Sb : Finset (PlE D.host))
    (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) : EigAd Y Sb eig ↔
    ∀ (i : Fin D.R.m) σ k Q α Rr, HkDat R Sb i k Q α Rr → D.nd.goodRow σ → ∀ y ∈ D.what₂.isot (i.1 + 1) σ,
      EigVec R i k Q Rr (eig (i.1 + 1) σ k Q) (Y.mj.eW i y) := Iff.rfl

theorem EigVec.congr {i : Fin D.R.m} {k : ℕ} {Q : PlE D.host} {Rr : Finset (GA D (Wc D i))} {c : ↥D.LL0}
    {v v' : (R.HW i (sg0 D A3.A)).H} (h : EigVec R i k Q Rr c v) (e : HEq v' v) : EigVec R i k Q Rr c v' := eq_of_heq e ▸ h

end Gen

variable {hL : GlobalTheory.Published.LocalLanglandsGL} {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w}
  {x : St P} (L : LocAll (lay0 (Dof x)))

theorem eig_hkDat_back (l : LC hL x) {i k Q α Rr} (h : HkDat (datL x L).R (sbD L l) i k Q α Rr) :
    HkDat x.m.z.R l.rat.In.Sb ((i)) k ((Q)) ((α)) ((Rr)) :=
  ⟨(by with_unfolding_all exact (h.split :)), (by with_unfolding_all exact (h.offS :)), (by with_unfolding_all exact (h.odd :)), (by with_unfolding_all exact (h.le :)), (by with_unfolding_all exact (h.elt :)), (by with_unfolding_all exact (h.reps :))⟩

theorem eigVec_loc {i k Q Rr c v} (h : EigVec x.m.z.R i k Q Rr c v) :
    EigVec (datL x L).R ((i)) k ((Q)) ((Rr)) ((c)) ((v)) := (h)

theorem eigVec_state (l : LC hL x) (i σ k Q α Rr) (hd : HkDat x.m.z.R l.rat.In.Sb i k Q α Rr) (hσ : (Dof x).nd.goodRow σ) (y)
    (hy : y ∈ (Dof x).what₂.isot (i.1 + 1) σ) : EigVec x.m.z.R i k Q Rr (l.rat.In.eig (i.1 + 1) σ k Q) (x.r.Y.mj.eW i y) :=
  (by with_unfolding_all exact (((eigAd_iff_eigVec _ _ _).1 l.rat.rat.eig i σ k Q α Rr hd hσ y hy) :))

theorem eigAd_loc (l : LC hL x) {p0 : BaseLevelRowSide (w.D (oL x L).Z)} (Y : YT x L p0) (hY : YRel L Y) :
    EigAd Y (sbD L l) (eigD L l) :=
  (eigAd_iff_eigVec _ _ _).2 fun i σ k Q α Rr hd hσ y hy =>
    (by with_unfolding_all exact ((EigVec.congr (v' := ((Y.mj.eW i y))) (eigVec_loc L (eigVec_state l ((i)) ((σ)) k ((Q)) ((α)) ((Rr)) (((eig_hkDat_back L l hd))) ((hσ)) ((y)) ((hy))))
      (((hY.eW i y)))) : _))

end GlobalTheory.HeightCounting.Fin3

end
