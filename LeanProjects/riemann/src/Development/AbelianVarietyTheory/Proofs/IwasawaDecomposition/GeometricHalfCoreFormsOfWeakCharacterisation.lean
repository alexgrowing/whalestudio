import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsBaseEnlargementFixedCoefFieldOfCoeffEnlargemen
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Forms
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GeometricHalfCoreFormsUniformisationIntegral
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EventuallyDefiniteSpacesStandardAndLarge
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PbEqOfPins
import Formalism.LocalToGlobal.IndefiniteReal.LinksW

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj Formalism.IndefR.FWT
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.RealGeo

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.R3.Rw

theorem geometricHalf_coreForms_of_weakCharacterisation (hP : GlobalTheory.Published.CuspRapidDecay) {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T0 : Type}
    {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m} {C : CoreJ D} [Algebra C.Q.c.F D.what₂.LL] (R : RealDat3 D A3 C.Q.c.F)
    (F : Face3 D A3) (hch : R.WeakCharacterisation F) (hEx : R.toRealDat.ExAt) (hn : 8 * D.R.f * D.R.r + 4 ≤ D.R.nV) {ph : Fin D.R.m → ℂ}
    (geo : GeoHalf C R.toRealDat ph) : InGeo geo := by
  have hC : PreChar R.toRealDat :=
    ⟨hch.base.lev, hch.base.grp.red_R, hch.base.grp.red_L, hch.base.grp.record, hch.base.fam, hch.base.models,
      RealDat.chain_of_weak hch.base.chain hEx, RealDat.thP_of_weak hch.base.thP hEx⟩
  have hp : C.pb = R.toRealDat.C.P.pb :=
    GlobalTheory.PinsFixHalf.pb_eq_of_pins C R.toRealDat geo.κ geo.v₀ geo.O hC.lev geo.fw.laws geo.pins
  exact (GlobalTheory.RealGeoIn.inGeo_and_lUnif_and_lIntegral hP _ _ _ _ _ C R.toRealDat _ geo hC hch.base.grp.chiW hp hn).1

theorem stepW_rank_large (p : WP) :
    StepW p fun _ _ _ _ w => ∀ Z : w.Lt, 8 * (w.st Z).toD7.R.f * (w.st Z).toD7.R.r + 4 ≤ (w.st Z).toD7.R.nV :=
  Step.of_evG ((evG_of_ev GlobalTheory.Mem.StdSize.vstd_size_ev).imp fun _ _ _ _ _ H _ _ _ hO _ _ _ w _ Z => (H (w.st Z) hO).2)

set_option maxHeartbeats 1000000 in

theorem inGeo_stepW (hP : GlobalTheory.Published.CuspRapidDecay) (p : WP) :
    StepW p fun _ B' _ _ w' => ∀ (Z' : w'.Lt) (hX' : B'.fields.Ok) (U : Set w'.I.ι) (core' : CoreJ (w'.st Z').toD7)
      (alg' : Algebra core'.Q.c.F (w'.st Z').toD7.what₂.LL), letI := alg'; ∀ (Xg : Finset (Gc B' w'.px → B'.LL)) (tr : TrI B' w'.px)
        (R' : RealDat3 (w'.st Z').toD7 (famR (w'.st Z') w'.I hX' U Xg tr) core'.Q.c.F)
        (cG' : G0 R'.Pg (w'.st Z').toD7.R.r ≃* G0g (w'.st Z').toD7.nd),
        Pins R' (face0 (w'.st Z') w'.I hX' U Xg tr) cG' → R'.toRealDat.ExAt →
        ∀ (ph : Fin (w'.st Z').toD7.R.m → ℂ) (geo : GeoHalf core' R'.toRealDat ph), InGeo geo :=
  (stepW_rank_large p).trans (StepW.of_all fun _ _ _ _ _ _ _ H Z' _ _ _ _ _ _ R' _ hPin hEx _ geo =>
    geometricHalf_coreForms_of_weakCharacterisation hP R' _ hPin.char hEx (H Z') geo)

end GlobalTheory.Mem.R3.Rw

end
