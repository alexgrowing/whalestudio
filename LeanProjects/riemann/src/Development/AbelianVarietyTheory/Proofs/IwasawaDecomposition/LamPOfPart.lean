import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.GreenCuspidalIff
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonzeroPlacesOverPrimesLifts
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsIsBIffCoreB
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinRepApply
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.IsPrincipalMapOfAlgHom
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.PublishedTheorems.WeberRayClassFields.WeberRayFieldSt
import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StrictHenselianAcyclic
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PositionMv
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.IsLinked
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.AllRows
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.APerTw
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.EventuallyAllScaleContextsAndOfBoth
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NotGeoClFalse
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.UpLReStage
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHostDatumOfPlaceDataStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HostPlacesRayFieldStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StandardLatticesDiagonalStatement
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DivisionPairOfAdelicFormsFaceColumnsData
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TwArgs
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LambdaPrimeEqLambdaThree
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeThetaLiftTwistedModelIffUntwisted
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GeometricParameterOfReciprocity
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StdPsiOfStdFrame
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSphericalEigensystemFirstLiftBaseLevel
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEqOfMemISup
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteTypesViaFullHeckeAlgebraEigensystemsStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.HeightCounting.Up GlobalTheory.Mem.SRe GlobalTheory.Mem.R3.Rw

open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.Lev
open GlobalTheory.Mem.R3

noncomputable section
namespace GlobalTheory.Mem.R3.ScalarComponentUnique

open Formalism.IndefR.RecTie GlobalTheory.LamPrimeTransport
open scoped InnerProductSpace

set_option maxHeartbeats 4000000 in

theorem eigenvalue_of_part : GlobalTheory.Published.CuspRapidDecay → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type}
    {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
    (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D)
    (Y : Read (A3 := A3) R.toRealDat F.lv2 X0), Pins R F cG → Holds R F → ∀ (i : Fin D.R.m) π (c : A3.fam3.base3.Ix),
    D.what₂.isot ((i : ℕ) + 1) π ≠ ⊥ → D.what₂.isot ((i : ℕ) + 1) π ≤ (R.Wp3 i c).comap (Y.mj.eW i) →
    D.what₂.lamP D.what₂.mu0 ((i : ℕ) + 1) π = R.lam3 i A3.A.μ0 c A3.A.v0 := by
  intro hCRD D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y hP hH i π p hne hle
  have hC := hP.char
  have hEx := hH.aux.ex
  have hA := hH.prim.thmA
  have hGE := hH.prim.gEquiv
  have hE : R.toRealDat.IsThP := RealDat.thP_of_weak hC.base.thP hEx
  have hM : R.toRealDat.IsModels := hC.base.models
  have hμ : Used0 D D.what₂.mu0 := Or.inl rfl
  have hT := Y.tied.lift
  have htup : Y.tupT D.what₂.mu0 = A3.A.μ0 := by rw [← Y.tup0, Y.tupT_tup]
  have hread := thetaP_read R.toRealDat F.lv2 Y.tupT Y.hm Y.hTop Y.hinj hC.base.lev hC.base.grp hM hE Y.IL hT D.what₂.mu0 hμ i
  rw [← htup]
  refine hT.lamP D.what₂.mu0 hμ i π _ hne fun y hy' => ?_
  have hw0p : Y.mj.eW i y ∈ R.Wp3 i p := hle hy'
  have hw0e : PiTensorProduct.lift ((R.HW i (sg0 D A3.A)).e (Y.mj.eW i y)) = (Y.IL.jMj i y).1 := (Y.mjRead i y).symm
  have hw0W : PiTensorProduct.lift ((R.HW i (sg0 D A3.A)).e (Y.mj.eW i y)) ∈
      (toLiftReal R.toRealDat F.lv2 Y.tupT Y.hm Y.hTop Y.hinj).Wc i := by
    rw [hw0e]; exact (Y.IL.jMj i y).2
  have haS := GlobalTheory.LamPrimeTransport.adjoint_mem_base_level R F hCRD hC hEx hGE Y.tupT Y.hm Y.hTop Y.hinj i (Y.mj.eW i y) hw0W
  obtain ⟨a, ha⟩ : ∃ a, LinearMap.adjoint (R.thG i (Y.tupT D.what₂.mu0)) (Y.mj.eW i y) = a := ⟨_, rfl⟩
  rw [ha] at haS
  obtain ⟨x', hx'⟩ : ∃ x', Y.IL.jMt D.what₂.mu0 hμ i x' = ⟨R.toRealDat.extV i (Y.tupT D.what₂.mu0) a, haS⟩ :=
    ⟨_, LinearEquiv.apply_symm_apply _ _⟩
  have hprex : pre R.toRealDat F.lv2 Y.tupT Y.hm Y.hTop Y.hinj D.what₂.mu0 i (Y.IL.jMt D.what₂.mu0 hμ i x') = a := by
    apply Y.hinj i (Y.tupT D.what₂.mu0)
    rw [ext_pre, hx']
  have hTx : D.what₂.thetaT D.what₂.mu0 ((i : ℕ) + 1) y = x' := by
    refine ext_inner_left ℂ fun u => ?_
    have e1 : ⟪u, D.what₂.thetaT D.what₂.mu0 ((i : ℕ) + 1) y⟫_ℂ = ⟪D.what₂.thetaP D.what₂.mu0 ((i : ℕ) + 1) u, y⟫_ℂ :=
      LinearMap.adjoint_inner_right _ _ _
    rw [e1, hT.mj i, hT.mt D.what₂.mu0 hμ i, hread u, ← hw0e]
    erw [ipWc_lift R.toRealDat hM.HW F.lv2 Y.tupT Y.hm Y.hTop Y.hinj i]
    rw [← ext_pre R.toRealDat F.lv2 Y.tupT Y.hm Y.hTop Y.hinj D.what₂.mu0 i (Y.IL.jMt D.what₂.mu0 hμ i u),
      ← ext_pre R.toRealDat F.lv2 Y.tupT Y.hm Y.hTop Y.hinj D.what₂.mu0 i (Y.IL.jMt D.what₂.mu0 hμ i x'),
      ipA_ext, hprex, ← ha, LinearMap.adjoint_inner_right]
  rw [hTx]
  apply (Y.IL.jMj i).injective
  apply Subtype.ext
  rw [hread x', hprex, ← ha, hA i (Y.tupT D.what₂.mu0) p (Y.mj.eW i y) hw0p, LinearEquiv.map_smul, Submodule.coe_smul, ← hw0e]
  rw [map_smul]
  exact map_smul _ _ _

end GlobalTheory.Mem.R3.ScalarComponentUnique
end

noncomputable section
namespace GlobalTheory.Mem.R3.ScalarComponentUnique

open Formalism.L2.Col GlobalTheory.HeckeLifts₂

set_option maxHeartbeats 4000000 in

theorem part_unique : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type}
    {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
    (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D)
    (Y : Read (A3 := A3) R.toRealDat F.lv2 X0), Pins R F cG → Holds R F → ∀ (i : Fin D.R.m) π (c p : A3.fam3.base3.Ix),
    D.what₂.isot ((i : ℕ) + 1) π ≠ ⊥ → D.what₂.isot ((i : ℕ) + 1) π ≤ (R.Wp3 i c).comap (Y.mj.eW i) →
    D.what₂.isot ((i : ℕ) + 1) π ≤ (R.Wp3 i p).comap (Y.mj.eW i) → c = p := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y hP hH i π c p hne hc hp
  by_contra hcp
  obtain ⟨hW, hHk⟩ := hH.prim.hecke.2
  have hu := untw_of_hH hP.char hHk
  have hd0 := disjoint_eigSum (hu.comm i) (C := SysC A3 i c) (C' := SysC A3 i p) fun y h h' =>
    h.elim fun x hx => h'.elim fun x' hx' => by
      have e : x = x' := funext fun k => D.what₂.embLL.injective ((congrFun hx.2 k).symm.trans (congrFun hx'.2 k))
      subst e
      exact (A3.liftI i A3.A.fam.μ0).excl3 (hH.sep c.1 c.2 p.1 p.2 (fun h => hcp (Subtype.ext h)) i) x hx.1 hx'.1
  have hd : Disjoint (R.Wp3 i c) (R.Wp3 i p) := hd0.mono (hu.parts i c).le (hu.parts i p).le
  have hinj : ∀ x, Y.mj.eW i x = 0 → x = 0 := fun x hx => by
    have h1 := Y.mj.eW_norm i x
    rw [hx, norm_zero] at h1
    have hn := RealDat.nP_pos (F := F.lv2) false
    have h2 : ‖x‖ ^ 2 = 0 := by
      rcases mul_eq_zero.1 (show RealDat.nP F.lv2 false * ‖x‖ ^ 2 = 0 by rw [← h1]; ring) with h | h
      · exact absurd h hn.ne'
      · exact h
    exact norm_eq_zero.1 (pow_eq_zero_iff (n := 2) (by norm_num) |>.1 h2)
  apply hne
  refine eq_bot_iff.2 fun x hx => ?_
  have h1 : Y.mj.eW i x ∈ R.Wp3 i c := hc hx
  have h2 : Y.mj.eW i x ∈ R.Wp3 i p := hp hx
  exact (Submodule.mem_bot ℂ).2 (hinj x ((Submodule.disjoint_def.1 hd) _ h1 h2))

end GlobalTheory.Mem.R3.ScalarComponentUnique
end
