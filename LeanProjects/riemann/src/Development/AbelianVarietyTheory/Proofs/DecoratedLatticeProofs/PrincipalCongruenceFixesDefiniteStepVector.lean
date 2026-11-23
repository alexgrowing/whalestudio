import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PrinInf
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SkewGramHalfModule
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HeckeLPartialContinuationHolds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilDatumFixesVacuumNonSplitPlaceUnramified
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilOperatorLatticeStabiliserFixesVacuumNonsplit
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilLatticeVacuumStabilizerSplittingCharacters
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.OmegaQEmpty
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilRepThetaDatumHalfEqSmulStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SchrodingerIntertwinerSchwartzBruhatIsThetaStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemHomLatticeIffFrameStabilizerActMemStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FrameMatrixMovedHomIntegralReductionsStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LevelPlacesDatumMulRightSourceLevelStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.GlobalFormOfSiegelWeil
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.StepVectorLiftPairFlagLevelRealizedChain

noncomputable section

namespace GlobalTheory.SmallFix

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR GlobalTheory.WeilParts GlobalTheory.VecInv
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem isDetRoot_one (V : HSp D) : IsDetRoot V (1 : GA D V) (1 : (AE D)ˣ) := by
  show ((1 : (AE D)ˣ) : AE D) = _
  rw [map_one, Units.val_one]
  simp

theorem suppPl_one (ε : AF D.host.F) (V : HSp D) : SuppPl ε V (1 : GA D V) := fun i j => by
  rw [GlobalTheory.AdelicLatMove.mt_one, sub_self, Matrix.zero_apply, mul_zero]

theorem suppAt_one (e : AE D) (V : HSp D) : Formalism.L2.Theta.SuppAt e V (1 : GA D V) := fun i j => by
  rw [GlobalTheory.AdelicLatMove.mt_one, sub_self, Matrix.zero_apply, mul_zero]

theorem inert_one {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)}
    {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)} {χS : (AE D)ˣ →* Circle}
    {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} (hW : IsWeilDatumO ψ S T χS 1 om)
    (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT) (hη : ∃ η, IsEtaTilde D η)
    {v : HeightOneSpectrum (𝓞 D.host.F)} {ε : AF D.host.F} (hε : NonSplitAt D v ε) (g : GA D S) (hg : SuppPl ε S g)
    (hst : ∀ u, u ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) ↔
      actO S T g 1 u ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True))
    (f : WO S T → ℂ) (hf : IsThetaFunO ψ S T f)
    (hvac : IsLatVac (heisO ψ S T) (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) f) :
    om (g, 1) f = f := by
  obtain ⟨η, hη⟩ := hη
  have hψ := hW.std
  obtain ⟨θ, hθ⟩ := hψ.2.1
  obtain ⟨om₀, h0, hv, -⟩ := GlobalTheory.T.exists_weilDatum_powers_unramifiedEtaTilde D ψ hψ S T θ hθ ΛS ΛT hS hT η hη
  obtain ⟨om₁, h1, htw⟩ := GlobalTheory.T.exists_weilDatum_twist_heckeCharacters D ψ hψ S T _ _ ((η ^ S.rank)⁻¹ * χS) ((η ^ T.rank)⁻¹ * 1) om₀ h0
    (GlobalTheory.VacInert.hecke_quot hW.hecS h0.hecS) (GlobalTheory.VacInert.hecke_quot hW.hecT h0.hecT)
    (GlobalTheory.VacInert.resEta_quot hW.resS h0.resS) (GlobalTheory.VacInert.resEta_quot hW.resT h0.resT)
  rw [mul_inv_cancel_left, mul_inv_cancel_left] at h1
  obtain ⟨x, hx, xi, -, x1, x2⟩ := GlobalTheory.VacInert.exists_unit_root hε S g hg
  have hlat : ∀ u, u ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun w => w = v) ↔
      actO S T g 1 u ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun w => w = v) := fun u => by
    rw [GlobalTheory.VecInvInert.mem_place_iff hε.1, GlobalTheory.VecInvInert.mem_place_iff hε.1, ← hst, ← GlobalTheory.FinWeilO.actO_smul,
      (GlobalTheory.VecInvInert.act_injective g 1).eq_iff]
  have hfix : ∀ u ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun w => w = v),
      heisO ψ S T u f = f := fun u hu => by
    obtain ⟨a, ha, ha2⟩ := GlobalTheory.FinWeilO.exists_half_of_nonSplit hε
    have e1 : 2 • (a • u) = u := by
      rw [two_nsmul, ← add_smul, ← two_mul, ha2, GlobalTheory.VecInvInert.idem_smul_eq hε.1 hu]
    have e2 := hvac.1 (a • u)
      (GlobalTheory.LatticeStable.smul_mem_latO D S T _ _ _ a ha u (GlobalTheory.PlaceModel.latO_le_top _ hu))
    rwa [e1] at e2
  rw [GlobalTheory.T.weilDatum_unique_on_thetaFunctions D ψ hψ S T χS 1 om om₁ hW h1 _ f hf, htw g 1 x 1 hx (isDetRoot_one T), LinearMap.smul_apply,
    hv v ε hε g 1 hg (suppPl_one ε T) hlat f hf hfix]
  simp [hη.2.1 x xi x1 x2]

theorem local_one {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)}
    {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)} {χS : (AE D)ˣ →* Circle}
    {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} (hW : IsWeilDatumO ψ S T χS 1 om)
    (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT) (hη : ∃ η, IsEtaTilde D η)
    {βS : GL (Fin S.rank) (Lev.EAf D)} {βT : GL (Fin T.rank) (Lev.EAf D)} (frS : IsFrame βS ΛS) (frT : IsFrame βT ΛT)
    {v : HeightOneSpectrum (𝓞 D.host.F)} {ε : AF D.host.F} (hε : IsPlaceIdem D v ε) (g : GA D S) (hg : Stab S βS g)
    (sg : SuppPl ε S g) (f : WO S T → ℂ) (hf : IsThetaFunO ψ S T f)
    (hvac : IsLatVac (heisO ψ S T) (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) f) :
    om (g, 1) f = f := by
  have hlat := mem_latO_iff frS frT (h := (1 : GA D T)) hg.2 (Stab.one T βT).2
  by_cases hsp : ∃ e', IsSplitIdem D e' ∧ e' + cA D e' = algebraMap (AF D.host.F) (AE D) ε
  · obtain ⟨e', he', hb⟩ := hsp
    have := GlobalTheory.T.splitPlace_weilRep_latticeVacuum_character D ψ S T ΛS ΛT χS 1 om hW hS hT e' he' g 1 (fun i j => by rw [hb]; exact sg i j)
      (suppAt_one e' T) hlat _ _ (isDetAt_detAt e' he'.1 S g) (isDetAt_detAt e' he'.1 T 1) f hf hvac
    rw [this, splitFacO, map_one, map_one, MonoidHom.one_apply, inv_one, one_mul, Circle.coe_one, one_smul]
  · exact inert_one hW hS hT hη ⟨hε, hsp⟩ g sg hlat f hf hvac

theorem vac_one {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)}
    {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)} {χS : (AE D)ˣ →* Circle}
    {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} (hW : IsWeilDatumO ψ S T χS 1 om)
    (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT) (hη : ∃ η, IsEtaTilde D η)
    {βS : GL (Fin S.rank) (Lev.EAf D)} {βT : GL (Fin T.rank) (Lev.EAf D)} (frS : IsFrame βS ΛS) (frT : IsFrame βT ΛT)
    (f : WO S T → ℂ) (hf : IsThetaFunO ψ S T f)
    (hvac : IsLatVac (heisO ψ S T) (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) f)
    (g : GA D S) (hg : Stab S βS g) : om (g, 1) f = f := by
  let H : Subgroup (GA D S × GA D T) :=
    { carrier := {p | om (p.1, 1) f = f}
      one_mem' := by
        change om ((1 : GA D S), (1 : GA D T)) f = f
        rw [Prod.mk_one_one, map_one, Module.End.one_apply]
      mul_mem' := fun {p q} hp hq => by
        change om ((p * q).1, (1 : GA D T)) f = f
        have e : ((p * q).1, (1 : GA D T)) = (p.1, (1 : GA D T)) * (q.1, 1) := Prod.ext rfl (mul_one 1).symm
        have hq' : om (q.1, 1) f = f := hq
        have hp' : om (p.1, 1) f = f := hp
        rw [e, map_mul, Module.End.mul_apply, hq', hp']
      inv_mem' := fun {p} hp => by
        change om (p⁻¹.1, (1 : GA D T)) f = f
        have hp' : om (p.1, 1) f = f := hp
        have e : (p⁻¹.1, (1 : GA D T)) = (p.1, (1 : GA D T))⁻¹ := Prod.ext rfl inv_one.symm
        rw [e]
        calc om (p.1, (1 : GA D T))⁻¹ f = om (p.1, (1 : GA D T))⁻¹ (om (p.1, 1) f) := by rw [hp']
          _ = f := by rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] }
  have hcl : IsClosed (H : Set (GA D S × GA D T)) := by
    have : (H : Set (GA D S × GA D T)) = ⋂ w, {p | om (p.1, 1) f w = f w} := by
      ext p
      rw [Set.mem_iInter]
      exact funext_iff
    rw [this]
    exact isClosed_iInter fun w => isClosed_eq
      ((hW.om_cont f hf w).comp (continuous_fst.prodMk continuous_const)) continuous_const
  exact GlobalTheory.T.mem_closedSubgroup_of_localStabilizerPairs D S T βS βT H hcl (fun v ε hε g' h' hg' _ sg' _ =>
    local_one hW hS hT hη frS frT hε g' hg' sg' f hf hvac) g 1 hg (Stab.one T βT)

end GlobalTheory.SmallFix

end

noncomputable section

namespace GlobalTheory.SmallFix

open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec)
open GlobalTheory.Mem.Th (CptF)
open GlobalTheory.Core.Rk.IP
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.Exh GlobalTheory.RegSW

set_option maxHeartbeats 1000000 in
open Classical in

theorem prin_fixes_stepVec : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (A H : HSp D) (χA : (AE D)ˣ →* Circle) (om : WRep A H) (sA : RealMat A) (sH : RealMat H), IsInfFam θ → (∃ η, GlobalTheory.WeilParts.IsEtaTilde D η) → IsWeilDatumO ψ A H χA 1 om → (∀ τ, IsCartanInv (gramAt D A τ) (sA τ)) → (∀ τ, IsCartanInv (gramAt D H τ) (sH τ)) → A.rank ≤ H.rank → ∀ (β : GL (Fin A.rank) (Formalism.IndefR.Lev.EAf D)) (Z : Finset (Formalism.L2.DIV.Pl D.host.E)), Places A β Z → ∀ (βH : GL (Fin H.rank) (Formalism.IndefR.Lev.EAf D)) (f₀ f : WO A H → ℂ), Formalism.L2.DIV.IsFrame βH (frameLat H) → IsStepVecOf ψ θ A H sA sH (frameLat A) (frameLat H) β βH (prinDat A Z) (fun _ => 1) ∅ (fun _ => 1) f₀ f → IsThetaFunO ψ A H f → ∀ κ ∈ prin A β Z, om (κ, 1) f = f := by
  intro D ψ θ A H χA om sA sH hθ hη hW cA' cH hrk β Z hPl βH f₀ f hfrH hv hthf κ hκ
  obtain ⟨hf, e, he, hΘ⟩ := hv
  have dA := frameLat_isSelfDualC A
  have dH := frameLat_isSelfDualC H
  have hlev : Formalism.IndefR.Lev.finE A κ ∈ Formalism.L2.DIV.lev D.sp.cm A.gram β (prinDat A Z) := hκ.2
  have sg : Formalism.IndefR.Lev.finE A κ ∈ Formalism.L2.DIV.St β := Formalism.L2.DIV.parLev_St hlev.1
  have sh : Formalism.IndefR.Lev.finE H 1 ∈ Formalism.L2.DIV.St βH := by rw [map_one]; exact Subgroup.one_mem _
  have h1 : om (κ, 1) f₀ = (1 : ℂ) • f₀ := by
    rw [one_smul]
    exact GlobalTheory.SmallFix.vac_one hW dA dH hη hPl.frame hfrH f₀ hf.2.theta hf.2.lat κ ⟨hκ.1, sg⟩
  have hoG := GlobalTheory.T.levelPlacesDatum_mul_right_source_level D A.rank H.rank (prinDat A Z) (fun _ => 1)
    (fun PP => Formalism.L2.DIV.redFn β PP (Formalism.IndefR.Lev.finE A κ)) (fun PP hP => Formalism.L2.DIV.parLev_g hlev.1 hP) hlev.2
  have h2 := GlobalTheory.T.weilRep_theta_datum_half_eq_smul D ψ A H χA 1 om hW e _ f₀ _ f
    (GlobalTheory.T.schrodingerIntertwiner_schwartzBruhat_isTheta D ψ hW.std A H (frameLat A) (frameLat H) dA dH e (GlobalTheory.PlaceDatum.idemSum_mul_self he)
      (GlobalTheory.PlaceDatum.infPart_idemSum he) f₀ hf.2.theta) hΘ κ 1
    (GlobalTheory.T.mem_homLattice_iff_frameStabilizer_act_mem D A H (frameLat A) (frameLat H) β βH dA dH hPl.frame hfrH κ 1 sg sh) 1 1 one_ne_zero h1 (fun x => by
      obtain ⟨i1, i2⟩ := GlobalTheory.T.frameMatrix_movedHom_integral_reductions D A H β βH κ 1 sg sh x
      have i0 : Formalism.IndefR.Datum.IsHalf e (actO A H κ⁻¹ 1⁻¹ x) ↔ Formalism.IndefR.Datum.IsHalf e x :=
        ⟨fun H' => GlobalTheory.AdelicLatMove.actO_actO_inv A H κ 1 x ▸ GlobalTheory.SplitHecke.isHalf_actO κ 1 H',
          fun H' => GlobalTheory.SplitHecke.isHalf_actO _ _ H'⟩
      by_cases hx : Formalism.IndefR.Datum.IsHalf e x ∧ Formalism.IndefR.Datum.IsIntM (frMapO A H β βH x)
      · beta_reduce
        rw [if_pos hx, if_pos ⟨i0.2 hx.1, i1.2 hx.2⟩, funext (i2 hx.2), GlobalTheory.ChainOnto.StepLevLaw.omegaQ_empty,
          GlobalTheory.ChainOnto.StepLevLaw.omegaQ_empty, mul_one, mul_one]
        simp only [map_one, Formalism.L2.DIV.redFn_one, inv_one, Units.val_one, Matrix.one_mul]
        rw [hoG]
        congr 1
        rw [show (prinDat A Z).s = 0 from rfl, Finset.range_zero]
        simp only [Finset.prod_empty, Finset.prod_const_one, MonoidHom.one_apply, inv_one, mul_one]
        exact (congrArg Units.val (show (prinDat A Z).P.chi _ = 1 from rfl)).trans Units.val_one
      · beta_reduce
        rw [if_neg hx, if_neg fun H' => hx ⟨i0.1 H'.1, i1.1 H'.2⟩, mul_zero])
  rw [h2, mul_one, one_smul]

end GlobalTheory.SmallFix

end
