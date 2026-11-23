import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeGeometricAllStatesStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PublishedInputsThirdLayer
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SameGaloisLevelExists
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RootsOfUnityRingLeWittIntegers
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HeckeOpen
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec

set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
namespace GlobalTheory.HeightCounting.HeckeLaw
theorem hecke_geometric_of_multiplicity_lower_bound_alt : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → SerN → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, AllSt fun _ _ _ _ _ P x => ∀ (l : _root_.GlobalTheory.HeightCounting.Up.SecondIntermediateLevel hL x) (i : (Dof x).ntw.Tw) (b : Bool) (j : Fin (Dof x).R.m), GlobalTheory.GeoTie.HeckeGeo l.b.YS x.m.z.geo.fw ((Dof x).nth.iC i) b j := by
  intro hP hS hL
  have ev : ∀ {Q : Ctx → Prop}, Ev Q → StepW Start fun K _ _ _ _ => Q K := fun h =>
    Step.of_evG ((evG_of_ev h).imp fun _ _ _ _ _ H _ _ _ _ _ _ _ _ _ => H)
  refine ((ev GlobalTheory.Mem.HostFrames.hostHyp_frames_ev).and (ev GlobalTheory.Mem.StdSize.vstd_size_ev)).trans
    (StepW.of_all fun K B f T w hO _ H => ?_)
  intro P x l i b j
  obtain ⟨hHo, -⟩ := H.1 (w.st x.o.Z) hO
  obtain ⟨hStd, hSize⟩ := H.2 (w.st x.o.Z) hO
  have hfin : Finite (TupU w.I (usedOf w.I T P.Wt)) := by
    have hs : ({τ | τ = (Formalism.L2.DIV.mu0F (X := B.fields) (tuOf w.I (usedOf w.I T P.Wt))).1 ∨ τ ∈ tuOf w.I (usedOf w.I T P.Wt)} :
        Set _).Finite :=
      (Set.finite_singleton _).union (tuOf w.I (usedOf w.I T P.Wt)).finite_toSet
    exact hs.to_subtype
  let X := GlobalTheory.TwInputs.RealSide.ofPins x.m.z.geo x.m.z.pins x.m.intersectionNumber_baseChange x.m.inGeo hfin hHo hStd hSize
  have hC := X.char
  have hSb : ∀ Q ∈ x.m.z.R.Sb, Q ∈ (Dof x).ntw.S0 i := by
    intro Q hQ
    have hA : x.m.z.R.Sb = x.m.z.R.Pg := x.m.z.pins.char.allPl
    obtain ⟨k, hk⟩ := l.b.ser.ex.good.Pg i j b Q (by rw [l.b.ser.ex.pin.Pg]; exact hA ▸ hQ)
    exact (Dof x).ntw.placesOver_subset_exceptional i k hk
  exact GlobalTheory.GeoTie.CuspLev.heckeGeo_of_levels l.b.YS x.m.z.geo.fw ((Dof x).nth.iC i) b j l.b.ser.ex
    (x.m.z.geo.fw.evaluates_of_lUnif x.m.intersectionNumber_baseChange.prim.unif) hC.lev hC.models.HW x.m.intersectionNumber_baseChange.prim.unif
    (l.rat.In.ks _ (Nat.le_add_left _ _) j.2) (fun hV => GlobalTheory.HeckeSupReal.readsCusp_realSide hP.decay hS.hkRead (Dof x) X j hV)
    (fun Q hQs hQ => GlobalTheory.SplitOffS0.main l.b.ser.ex.good i _ hSb Q hQs hQ) hS.hkTr
    (fun Q hQ => delAt_mem w x.o.Z x.m.z i Q hQ)
end GlobalTheory.HeightCounting.HeckeLaw
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeGeo_at_levelB1_states : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → SerN → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, AllSt fun _ _ _ _ _ P x => ∀ (l : _root_.GlobalTheory.HeightCounting.Up.SecondIntermediateLevel hL x) (i : (Dof x).ntw.Tw) (b : Bool) (j : Fin (Dof x).R.m), GlobalTheory.GeoTie.HeckeGeo l.b.YS x.m.z.geo.fw ((Dof x).nth.iC i) b j := by
  first | exact @_root_.GlobalTheory.HeightCounting.HeckeLaw.hecke_geometric_of_multiplicity_lower_bound_alt | exact _root_.GlobalTheory.HeightCounting.HeckeLaw.hecke_geometric_of_multiplicity_lower_bound_alt | (intros; apply _root_.GlobalTheory.HeightCounting.HeckeLaw.hecke_geometric_of_multiplicity_lower_bound_alt <;> assumption)
end
end
