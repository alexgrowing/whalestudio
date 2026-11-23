import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenLocOfCenReal
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CoreEq
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NoFormsOff
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroWild
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroSupport
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalGlobalAboveL
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PinOfNTrue
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilDeligneLabelsAllPlacesOfFixedAndConjStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsGreenCuspidalLabellingSameGeneratorsStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.JumpsCardOfBuilt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AuxiliaryPlacesSplit
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValuationFixedLattice
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChebSplitNd
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG

namespace GlobalTheory.PinLayer

set_option maxHeartbeats 4000000 in

theorem pinAt_of_side {hL : GlobalTheory.Published.LocalLanglandsGL} {D : D7} {cf : CharFrame D} {nch : NChoice D} {tp : TupTied D cf nch}
    (a : NAt hL D cf nch tp) (hG : GlobalTheory.Published.GreenCuspidal) (hT : TypesTrue D.ntypes cf.P cf.W) (hval : ValLL0 D cf)
    (rep' : D.what₂.FT → NG.FinTyp D.host.E D.R.r) (hrep : HEq a.nt.rep rep')
    (hinj : ∀ σ σ', (rep' σ).Iso (rep' σ') → σ = σ') (hE : Elem D) (hcheb : GlobalTheory.RowTie.ChebSplit D.nd)
    (labc : LabConj a.nt.D a.nt.A.wdT)
    (zeta : ∀ k, a.nt.A.grp.ζ k = @GlobalTheory.GLq.LabelDatum.gen _ ⟨a.nt.D.host.g_prime k⟩ (@GlobalTheory.Mem.TypePl.labDat (a.nt.D.host.g k) ⟨a.nt.D.host.g_prime k⟩)) :
    ∃ P : GlobalTheory.NPin.Pin hL D, PinAt a P := by
  rcases a with ⟨nt, all, chr_eq, host, frameN, chrN, chrGal, Pq', Pq_over, pq, jE_eq, mt_eq, Pq_eq, low', split, ratIn, ratIn_hL, ratIn_eig, ratIn_θ, depth⟩
  obtain ⟨⟨D0, cf0, jE, A, cg, au, rep, row, low, Pq, S, hLm, eig, θ, Bs, M, C0, tp0, ch, mt, big, L, Sp, Au, ss, heq⟩, pack⟩ := nt
  dsimp only at pack heq hrep labc zeta mt_eq ⊢
  subst heq
  cases pack
  cases hrep
  obtain ⟨Hk, hHk⟩ := GlobalTheory.FitHecke.heckeOpen_withLoc D0 cf0 jE A low Pq S hLm eig θ Bs M C0 tp0 ch mt hE.star hE.int hE.split hcheb big L Sp Au
  obtain ⟨ty⟩ := GlobalTheory.HeightCounting.typesOpen_withLoc D0 cf0 jE A low Pq S hLm eig θ Bs M C0 tp0 ch mt hE.star hE.int hE.split hcheb big L Sp Au ss
  obtain ⟨tw⟩ := GlobalTheory.T.side_multiplicity_character D0 cf0 jE A low Pq S hLm eig θ Bs M C0 tp0 ch mt hE.star hE.int hE.split hcheb big L Sp Au
  obtain ⟨Γ, hΓ, -⟩ := GlobalTheory.T.exists_green_cuspidal_labelling_same_generators hG (withLoc L) (cfL L cf0) { A.grp with } hT zeta
  refine ⟨{ cf := cfL L cf0, C := chL L C0, tp := tpL L tp0, chr := tw.chrN, val := hval, Q_eq := ?Q, T := { A.wdT with }, lab := A.lab, cg := { cg with }, M := mtL L M, H := Hk, au := ?au, rep := rep, rep_inj := hinj, row := ?row, locW_eq := fun i i' σ w => (Au.locW i σ w).trans (Au.locW i' σ w).symm, jE := jE, ty := { ty with grp := Γ }, wd := { A.wd with }, wdOf := Au.wdOf }, ⟨rfl, rfl, HEq.rfl, HEq.rfl, eq_of_heq mt_eq, ?lab, hΓ, ?chiT⟩⟩
  case Q =>
    intro i
    have hm : i ∈ L.X.nd.locs (L.X.nd.j i) (L.X.nd.w i) := (L.X.nd.locs_mem _ _ i).2 ⟨rfl, rfl⟩
    exact (Sp.Q_eq _ _ i hm).trans (Sp.Qc_eq _ _)
  case au =>
    intro j h1 h2 π s σ h
    rw [hHk]
    exact au j h1 h2 π s σ h
  case row =>
    intro i
    refine ⟨fun σ s τ h => ?_, fun σ v w hvw Dv hα => ?_⟩
    · exact (congrArg (A.wdT.e s.w) (Au.locW i σ s.w)).trans (row.1 σ s τ h)
    · obtain ⟨α, h1, h2⟩ := row.2 σ v w hvw Dv hα
      exact ⟨α, h1, (Au.satW i σ w).trans h2⟩
  case lab =>
    exact GlobalTheory.T.weilDeligneLabels_all_places_of_fixed_and_conj _ _ A.lab labc
  case chiT =>
    exact A.chiT

set_option maxHeartbeats 4000000 in

theorem pin_atMem : PrN → ∀ hL : GlobalTheory.Published.LocalLanglandsGL,
    AtMem hL fun _ _ _ _ w Z _ _ t nch n c => ∃ P : GlobalTheory.NPin.Pin hL (w.D Z), PinAt c.a P := by
  intro hP hL
  refine GlobalTheory.HeightCounting.JumpsAt.evLgG_of_forall fun K B f T _ w Z Wt p0 t nch n xd c hE _ _ => ?_
  obtain ⟨e⟩ := hE
  have e' : NMore (D := (w.st Z).toD7) c.row t.r.z.geo xd := e
  have hT : TypesTrue (w.D Z).ntypes (TC.cf w.I w.l Z).P (TC.cf w.I w.l Z).W := by
    show TypesTrue _ w.I.C.P w.I.C.W
    rw [w.C_eq]
    exact t.grp
  have hEl : Elem (w.D Z) := by
    refine ⟨fun y => ?_, fun j g => ((w.D Z).hc ((w.D Z).eTau.symm g)).e_int j, fun v hv => ?_⟩
    · exact (IntermediateField.normal_iff_forall_map_le.1 B.coeffGaloisSubfield_isGalois.to_normal
        (starRingEnd (w.D Z).what₂.LL).toRatAlgHom) ⟨_, y.2, rfl⟩
    · have hc : ∀ p ∈ (w.D Z).host.levelPrimes, p.Prime ∧ p % ((w.D Z).host.QS * (w.D Z).host.q * (w.D Z).host.d) = 1 :=
        (w.st Z).B.level_cond
      rcases hv with hv | hv
      · exact GlobalTheory.HeightCounting.Up.isSplitPl_of_mem_levelPrimes _ hc (w.D Z).host.pde_level.1 v hv
      · exact GlobalTheory.HeightCounting.Up.isSplitPl_of_mem_levelPrimes _ hc (w.D Z).host.pde_level.2 v hv
  exact pinAt_of_side c.a hP.greenC hT (GlobalTheory.HeightCounting.Up.valLL0_colW w Z)
    (fun σ => Formalism.IndefR.principalLevelFrame.rowRepR t.r.z.R.θ (t.r.Y.eFT σ)) c.row.rep_eq
    (fun σ σ' h => t.r.Y.eFT.injective (Formalism.IndefR.principalLevelFrame.rowRepR_inj _ _ _ h)) hEl
    (GlobalTheory.ChebSplitDense.chebSplit_nd hP.what₂.cheb _) e'.labc e'.zeta

end GlobalTheory.PinLayer
