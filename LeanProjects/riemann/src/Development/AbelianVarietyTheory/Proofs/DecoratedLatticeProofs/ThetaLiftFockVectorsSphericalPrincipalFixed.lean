import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PrinInf
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TransferOn
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ParamsEx
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdjFormula
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HeckeLPartialContinuationHolds
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainStepFockVectorSphericalOffS
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsFockVacAtOfIsThetaAt
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.OmPureTensorOOfFinite
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeffSpaceLevelFixesFockVectors
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsCartanInvOneOfOnb
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UpperLeftBlockEqOneIffOfMemBlockTri
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.StandardHermitianSpace
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.RealLowestKTypeCoeffSquareIntegrable
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift GlobalTheory.Core.Rk.Exh

noncomputable section

namespace GlobalTheory.ThPFock

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem redFn_of_mem_prin (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) {κ : GA D (Vc D i)}
    (hκ : κ ∈ prin (Vc D i) (R.βV i) (R.Pg ∪ R.Q t)) :
    κ ∈ GfC (Vc D i) ∧ finE (Vc D i) κ ∈ UA D.sp.cm (Vc D i).gram ∧ finE (Vc D i) κ ∈ St (R.βV i) ∧
      ∀ PP ∈ R.Pg ∪ R.Q t, redFn (R.βV i) PP (finE (Vc D i) κ) = 1 := by
  have h := mem_levA.1 hκ
  have hP : (prinDat (Vc D i) (R.Pg ∪ R.Q t)).P.H = ⊥ := by
    rfl
  obtain ⟨h1, h2, h3⟩ := (GlobalTheory.PrincipalLevel.mem_lev_whole _ _ _ rfl rfl hP _).1 h.2
  exact ⟨h.1, h1, h2, h3⟩

theorem is_lift_of_mem_principal_congruence (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) {κ : GA D (Vc D i)}
    (hκ : κ ∈ prin (Vc D i) (R.βV i) (R.Pg ∪ R.Q t)) : IsLevelLift (Vc D i) (R.βV i) (R.datVt i t) 1 κ := by
  obtain ⟨h0, h1, h2, h3⟩ := redFn_of_mem_prin R i t hκ
  refine ⟨h0, mem_parLev.2 ⟨h1, h2, fun PP hPP => ?_, fun PP hPP => ?_⟩, ?_⟩
  · rw [h3 PP (Finset.mem_union_left _ hPP)]
    exact Subgroup.one_mem _
  · rw [h3 PP (Finset.mem_union_right _ hPP)]
    exact Subgroup.one_mem _
  · funext PP
    show upperLeftBlock _ (redFn (R.βV i) PP.1 (finE (Vc D i) κ)) = 1
    rw [h3 PP.1 (Finset.mem_union_left _ PP.2)]
    exact blockDiagonalExtendByOnePrimeField_one _ _

theorem levChi_flag_of_mem_prin (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) {κ : GA D (Vc D i)}
    (hκ : κ ∈ prin (Vc D i) (R.βV i) (R.Pg ∪ R.Q t)) : levChi (Vc D i) (R.βV i) (flagL (R.datVt i t)) κ = 1 := by
  obtain ⟨-, -, -, h3⟩ := redFn_of_mem_prin R i t hκ
  have e : levFn (R.βV i) (flagL (R.datVt i t)) (finE (Vc D i) κ) = levFn (R.βV i) (flagL (R.datVt i t)) 1 := by
    have hr : rTup (R.βV i) (flagL (R.datVt i t)) (finE (Vc D i) κ) = rTup (R.βV i) (flagL (R.datVt i t)) 1 := by
      funext PP
      show upperLeftBlock _ (redFn (R.βV i) PP.1 (finE (Vc D i) κ)) = upperLeftBlock _ (redFn (R.βV i) PP.1 1)
      rw [h3 PP.1 (Finset.mem_union_left _ PP.2), redFn_one]
    unfold levFn
    rw [hr]
    congr 1
    · congr 1
      exact Finset.prod_congr rfl fun PP hPP => Finset.prod_congr rfl fun c _ => by
        rw [h3 PP (Finset.mem_union_left _ hPP), redFn_one]
    · exact Finset.prod_congr rfl fun PP hPP => by
        rw [h3 PP (Finset.mem_union_right _ hPP), redFn_one]
  have h1 := GlobalTheory.RawLift.LevelFix.levChi_flag_one R i t
  unfold levChi at h1 ⊢
  rw [e]
  rw [(finE (Vc D i)).map_one] at h1
  exact h1

theorem is_lift_one_principal_level (R : RealDat D A Ks) (i : Fin D.R.m) : IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) 1 1 :=
  ⟨Subgroup.one_mem _, by rw [map_one]; exact Subgroup.one_mem _, by rw [map_one]; exact rTup_one⟩

end GlobalTheory.ThPFock

open GlobalTheory.ThPFock in

theorem GlobalTheory.ThPFock.fock_sph_prin : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.LiftRows.Given R F → R.FullP → ∀ i t P, (∀ τ, IsCartanInv (gramAt D (Wc D i) τ) (cart (R.MW i (sg0 D A)) τ)) ∧ GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.IsFockVec R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i (sg0 D A))) (R.ptP i t P) ∧ GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.IsSphOff R.ψ (Vc D i) (Wc D i) (GlobalTheory.AdelicU.frameLat (Vc D i)) (GlobalTheory.AdelicU.frameLat (Wc D i)) (under (R.Pg ∪ R.Q t)) (R.ptP i t P) ∧ ∀ κ ∈ prin (Vc D i) (R.βV i) (R.Pg ∪ R.Q t), R.ωP i t (κ, 1) (R.ptP i t P) = R.ptP i t P := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hG _ i t P
  have hC := hG.core
  have hθ : IsInfFam R.θ := hC.models.inf
  have hψ : IsStdChar D R.ψ (-1) := (hC.thP.ωP i t).std
  have cS : ∀ τ, IsCartanInv (gramAt D (Vc D i) τ) 1 := fun τ => GlobalTheory.RawLift.isCartanInv_one_of_onb (hC.models.BV i τ)
  have cT : ∀ τ, IsCartanInv (gramAt D (Wc D i) τ) (cart (R.MW i (sg0 D A)) τ) :=
    fun τ => GlobalTheory.AdTh.VecFock.isCartanInv_cart (R.MW i (sg0 D A)) τ
  have hpt : ∀ φ, IsThetaFunO R.ψ (Vc D i) (Wc D i) (pureTensorO R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1)
      (cart (R.MW i (sg0 D A))) (R.BV i) (onb (R.MW i (sg0 D A))) (R.vP i t) φ) := hC.thP.pt_theta i t
  have hvθ : IsThetaFunO R.ψ (Vc D i) (Wc D i) (R.vP i t) := by
    have := hC.thP.pt_theta i t 1
    unfold RealDat.ptP pureTensorO at this
    rwa [GlobalTheory.AdTh.VecFock.pureTensorL_one] at this
  have hvv : ∀ τ, IsFockVacAt (heisO R.ψ (Vc D i) (Wc D i)) R.θ τ (cplxO 1 (cart (R.MW i (sg0 D A)) τ)) (R.vP i t) :=
    GlobalTheory.DatumFock.isFockVacAt_thPVec _ _ _ _ (fun _ => 1) _ _ _ _ _ _ _ _ _ _ (hC.thP.vP i t) hvθ
  refine ⟨cT, ?_, ?_, ?_⟩
  · exact GlobalTheory.FockSph.isFockVec_pureTensorO hψ hθ cS cT (R.BV i) (onb (R.MW i (sg0 D A))) hvθ hvv P
  · obtain ⟨hvac, e, he, hth⟩ := hC.thP.vP i t
    have hV : (R.ΛV i : Set (Fin (Vc D i).rank → D.host.E)) = (GlobalTheory.AdelicU.frameLat (Vc D i) : Set _) := by
      rw [GlobalTheory.IndefiniteRowSideFullHecke.StandardHermitianSpace.baseLat_eq hC.lev i, GlobalTheory.AdelicU.hermitianSpaceBaseLattice_eq_frameLattice]
    have hW : (R.ΛW i : Set (Fin (Wc D i).rank → D.host.E)) = (GlobalTheory.AdelicU.frameLat (Wc D i) : Set _) := by
      rw [← GlobalTheory.AdelicU.hermitianSpaceBaseLattice_eq_frameLattice]
      obtain ⟨c, -, -, -, h1, h2⟩ := hC.lev.βW i
      ext x
      constructor
      · intro hx
        simpa using h2 x hx
      · intro hx
        simpa using h1 x hx
    have hle : latO (Vc D i) (Wc D i) (GlobalTheory.AdelicU.frameLat (Vc D i) : Set _) (GlobalTheory.AdelicU.frameLat (Wc D i) : Set _)
        (fun v => v ∉ under (R.Pg ∪ R.Q t)) ≤ latO (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i) fun _ => True := by
      rw [hV, hW]
      exact GlobalTheory.PlaceTensor.latO_mono fun _ _ => trivial
    have hz : ∀ u ∈ latO (Vc D i) (Wc D i) (GlobalTheory.AdelicU.frameLat (Vc D i) : Set _) (GlobalTheory.AdelicU.frameLat (Wc D i) : Set _)
        (fun v => v ∉ under (R.Pg ∪ R.Q t)), ∀ a b, cA D (cA D e) * u a b = 0 ∧ cA D e * u a b = 0 := by
      intro u hu a b
      obtain ⟨h1, h2⟩ := GlobalTheory.FockSph.idemSum_mul_of (P := fun v => v ∉ under (R.Pg ∪ R.Q t)) he
        (fun PP hPP hn => hn (Finset.mem_image_of_mem _ hPP)) hu a b
      rw [Formalism.L2.Theta.cA_cA]
      exact ⟨h1, h2⟩
    have hlat := hvac.2.lat
    have fix : ∀ u ∈ latO (Vc D i) (Wc D i) (GlobalTheory.AdelicU.frameLat (Vc D i) : Set _) (GlobalTheory.AdelicU.frameLat (Wc D i) : Set _)
        (fun v => v ∉ under (R.Pg ∪ R.Q t)), heisO R.ψ (Vc D i) (Wc D i) u (R.vacP i) = R.vacP i →
        heisO R.ψ (Vc D i) (Wc D i) u (R.ptP i t P) = R.ptP i t P := fun u hu h0 =>
      GlobalTheory.Hk3.FiniteHeis.heisO_pureTensorO_of_finite R.ψ R.θ (Vc D i) (Wc D i) hθ (fun _ => 1) (cart (R.MW i (sg0 D A)))
        (R.BV i) (onb (R.MW i (sg0 D A))) (R.vP i t) hpt u (GlobalTheory.VacGood.infPart_latO (hle hu))
        (GlobalTheory.Hk3.heisO_fix_thetaAt_off R.ψ (Vc D i) (Wc D i) (cA D e) _ 1 (R.vacP i) _ (R.vP i t) hth u
          (fun a b => ⟨(hz u hu a b).2, (hz u hu a b).1⟩) h0) P
    exact ⟨fun u hu => fix (2 • u) (AddSubgroup.nsmul_mem _ hu 2) (hlat.1 u (hle hu)),
      fun e' he' u hu hh => fix u hu (hlat.2 e' he' u (hle hu) hh)⟩
  · intro κ hκ
    have hl := is_lift_of_mem_principal_congruence R i t hκ
    have hv : R.ωP i t (κ, 1) (R.vP i t) = (1 : ℂ) • R.vP i t := by
      rw [GlobalTheory.T.weilAction_liftPair_stepVector_invLevelChar R hC.lev hC.models.inf hC.thP.ωP hC.thP.vP i t 1 κ 1 hl (is_lift_one_principal_level R i),
        levChi_flag_of_mem_prin R i t hκ, inv_one]
    have := GlobalTheory.FiniteFock.om_pureTensorO_of_finite R.ψ R.θ (Vc D i) (Wc D i) _ _ (R.ωP i t) hθ
      (hC.thP.ωP i t) _ _ _ _ _ hpt κ hl.1 1 (Subgroup.one_mem _) 1 hv P
    exact this.trans (one_smul ℂ _)
