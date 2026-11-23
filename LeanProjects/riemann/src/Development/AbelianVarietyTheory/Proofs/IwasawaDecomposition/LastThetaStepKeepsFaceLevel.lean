import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GoodProjectorSmallestSpaceForms
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GoodProjectorLevelMultiplicitySpaceMemGoodRows
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HcFiniteAndSchurMult
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

noncomputable section

namespace GlobalTheory.Mem.R3.DTheta

section TopLevProof

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem liftsExist_top (R : RealDat D A Ks) (hl : R.toLevCh.Is A.μ0) (t : T) (g0 : G0 R.Pg D.R.r) :
    ∃ κ, IsLevelLift D.sp.X' R.βX (R.datXt t) g0 κ := by
  obtain ⟨c, hc⟩ := hl.βX
  exact GlobalTheory.T.parahoricLevel_liftsExist D.sp.X' R.βX (R.datXt t) _ _ hc (GlobalTheory.ChainEquiv.places_sep R.toLevCh _ hl t).1
    (GlobalTheory.ChainEquiv.places_sep R.toLevCh _ hl t).2 g0

set_option maxHeartbeats 2000000 in

theorem topLev_of_clauses (R : RealDat D A Ks) (F : Face D A) (hl : R.toLevCh.Is A.μ0) (hM : R.IsModels) (hc : R.IsChain)
    (hS : ∀ t j, j < D.R.m → SchurMult R.θ (R.MY j) (levS _ (R.βY j) (R.datYt t j R.triv))
      (levChi _ (R.βY j) (R.datYt t j R.triv)) (R.νY t j) (R.fdY t j)) : TopLev R F := by
  intro b t y hy
  have hm : D.R.m - 1 < D.R.m := by have := D.R.two_le_m; omega
  have hrel : ∀ p : (R.levR F b).H, GlobalTheory.ChainEquiv.Rel R t p (D.R.m - 1) (R.ioX t y)
      ((((R.levR F b).chi p : ℂˣ) : ℂ) • R.ioX t y) := by
    intro p
    have hL := liftsExist_top R hl t (p : G0 R.Pg D.R.r)
    refine hL.elim fun κ' hκ' => ?_
    intro κ hκ v g
    have hF : ∀ w h, (((((R.levR F b).chi p : ℂˣ) : ℂ) • y : LinearMap.range (R.cX.toMap R.prX ∘ₗ (R.HX t).e)) :
        SmT R.MX →ₗ[ℂ] (GA D D.sp.X' → ℂ)) w h =
        (levChi _ R.βX (flagL (R.datXt t)) κ')⁻¹ * (y : SmT R.MX →ₗ[ℂ] (GA D D.sp.X' → ℂ)) w (h * κ') := by
      intro w h
      have hT : HasType D.sp.X' R.βX (withP (R.datXt t) (R.levR F b)) ((y : SmT R.MX →ₗ[ℂ] (GA D D.sp.X' → ℂ)) w) :=
        (GlobalTheory.ChainEquiv.multT_value _ _ _ _ _ hy w).2
      rw [← GlobalTheory.KeepLevel.eigen_of_hasType hT p hκ' h]
      rfl
    have key := GlobalTheory.ChainEquiv.step R.ψ R.θ hM.inf _ _ (R.ωX t) (hc.ωX t) _ _ _ _ (R.vX t) (hc.ptX t) (R.MY (D.R.m - 1))
      (R.βY (D.R.m - 1)) (R.datYt t (D.R.m - 1) R.triv) rfl _ (GlobalTheory.ChainEquiv.meas_chain hM.νY hM.νY' t _ hm).1 _
      (GlobalTheory.ChainEquiv.meas_chain hM.νY hM.νY' t _ hm).2
      (hS t _ hm) R.ItX (hc.ItX t).ne _ (GlobalTheory.ChainEquiv.range_left R.cX R.prX (R.HX t) _ _ (hM.HX t).2.1) R.βX (R.datXt t) _
      (hM.νX t).1.1 _ (hM.νX t).2 (R.ioX t) (hc.ioX t) (p : G0 R.Pg D.R.r) κ hκ (p : G0 R.Pg D.R.r) κ' hκ' _
      (GlobalTheory.T.lastVector_lift_pair_flagLevel_characters R hl hM.inf hc.ωX hc.vX t (p : G0 R.Pg D.R.r) κ κ' hκ hκ') y _ hF v g
    have e := (R.ioX t).map_smul (((R.levR F b).chi p : ℂˣ) : ℂ) y
    exact (congrArg (fun U : R.CC t (D.R.m - 1) => (U : SmT (R.MY (D.R.m - 1)) →ₗ[ℂ] (GA D (Yc D (D.R.m - 1)) → ℂ)) v g)
      e).symm.trans key
  have hU := (GlobalTheory.KeepLevel.mem_lvlPart_iff (R := R) (R.levR F b) t (D.R.m - 1) (R.ioX t y)).2 hrel
  exact (mem_multT R.θ (R.MY (D.R.m - 1)) _ _ _).2 hU

end TopLevProof

set_option maxHeartbeats 2000000 in

theorem topLev_holds : (GlobalTheory.Published.DiscreteSeriesCover ∧ GlobalTheory.Published.HarishChandraModules ∧ GlobalTheory.Published.CasselmanWallach ∧ GlobalTheory.Published.HarishChandraFinite ∧ GlobalTheory.Published.CuspRapidDecay) → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd), Pins R F cG → Holds R F → GlobalTheory.Mem.R3.DTheta.TopLev R.toRealDat F.lv2 := by
  intro hC D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG hP hH
  exact topLev_of_clauses R.toRealDat F.lv2 hP.char.base.lev hP.char.base.models
    (RealDat.chain_of_weak hP.char.base.chain hH.aux.ex)
    (fun _ _ _ => GlobalTheory.MultFinite.schurMult hC.2.2.2.2 _ _)

end GlobalTheory.Mem.R3.DTheta
