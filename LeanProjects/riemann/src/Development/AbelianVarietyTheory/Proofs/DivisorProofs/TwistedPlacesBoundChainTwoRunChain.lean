import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsDeltaDelAtOwnAt
import Formalism.LocalToGlobal.Divisibility.NumbersLemmas
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.DepthCond
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TraceLatticeLeThetaLatticeAtPlace
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GoodLiftOnto
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTieCoordBase

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Module
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.DivisionValues Formalism.EigenvalueLevelCeiling Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links
open Formalism.IndefR.Cx Formalism.IndefR.FWT Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.FormTies GlobalTheory.BigOn
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.OnAtPlacesBase

section Free

variable {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : DefBase K} {Df : DefSide Bs} {S : IndefData Df} {P : Type}
  [Group P] [Finite P] {c : OnConst}

theorem on_of_has_atPlaces (N : IndefNum Bs) (O : OnObj S P c) (CE : ℝ) (hRk : RankRows S)
    (hMk : LeafMackey O) (hSup : LeafSup O) (hProj : LeafProj O) (hC : TieCoord O)
    (hSp : LeafSpan O) (hS : LeafLemmaS O) (hT0 : HasIndexBound O) (hD : LeafData O) (hJ : GlobalTheory.TraceClassRank.RankAtPlaces O)
    (hI : LeafIdentity O) (h2 : LeafTW2 O) (h1 : HasTwistBound O)
    (hSh : LeafShareI O) (hIU : LeafIndexU O) (hBS : LeafBadShare O) (hUn : LeafUnip O)
    (hG : LeafDepthGood N O) (hR : LeafDepthRam N O) (h2p : LeafDepth2 N O) (hL : LeafDepthLevel N O)
    (hPg : LeafPage O) (hSz : LeafSizes O) (hX : LeafX O) (hBad : LeafBad O)
    (hE : HasExpBound N O) (hCE : c.CE ≤ CE) (tE1 : ErrorConstantMatchesDefinition N O CE) : ∃ err, ONwith S N err := by
  obtain ⟨Th1, a, r1, r2, de2, hT0⟩ := hT0
  obtain ⟨ε, h1⟩ := h1
  obtain ⟨-, Jp, hJS, hJE⟩ := hE
  exact ⟨_, GlobalTheory.TraceClassRank.on_core_atPlaces N
    ({ O with Th1 := Th1, a := a, r1 := r1, r2 := r2, de2 := de2, ε0 := ε, Jp := Jp } : OnObj S P c) CE hRk
    hMk hSup hProj hC hSp hS hT0 hD hJ hI h2 h1 hSh hIU hBS hUn hG hR h2p hL hPg hSz hX hBad hJS hJE hCE tE1⟩

end Free

theorem on_base_atPlaces : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (J : CoreJ D) [Algebra J.Q.c.F D.what₂.LL] (R : RealDat D A J.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (fw : FWTie J R κ v₀) (L : SizeData₂ D) (Pm : ParameterChoice' D L) (Tp : ParamsT D L Pm) (hK : DV.KapDef D) (EX : ErrX D) (r : TwoRuns J G) (c : OnConst) (O : OnObj ((R.toCx F).data F.cr false) (Mir R) c), IsRec Tp hK EX F fw r O → ∀ (s : ℕ) (N : IndefNum A.fam.base) (C : ℝ), A.fam.Ok s → R.grp_levels F → R.grp_chiW → R.IsModels → R.tup_mu_conj → R.thP_thG → R.LUnif → BaseLinks R F → TwistedRational R F (fun _ => 1) → RankRows ((R.toCx F).data F.cr false) → LeafLevelSq O (Res R) D.R.f → LeafYBound O → LeafSup O → LeafSpan O → LeafLemmaS O → HasIndexBound O → LeafData O → GlobalTheory.TraceClassRank.RankAtPlaces O → LeafIdentity O → LeafTW2 O → HasTwistBound O → LeafShareI O → LeafBadShare O → LeafDepthGood N O → LeafDepthRam N O → LeafDepth2 N O → LeafDepthLevel N O → LeafPage O → LeafSizes O → LeafX O → LeafBad O → HasExpBound N O → c.CE ≤ C → ErrorConstantMatchesDefinition N O C → ∃ err, ONwith ((R.toCx F).data F.cr false) N err := by
  intro D G _ _ Pl0 T0 A J _ R F κ v₀ fw L Pm Tp hK EX r c O hO s N C hOk h1 h2 hM hμ hth hU hB hrat hRk hSq hY hSup hSp hS hT0
    hD hJ hI hT2 hT1 hSh hBS hDG hDR hD2 hDL hPg hSz hX hBad hE hCE tE1
  classical
  obtain ⟨hc, hinj, ht⟩ := hO.tied
  obtain ⟨st, hd⟩ := hO.depth
  have hN : TieLevelNum O (rankPred D.R) D.R.f := by
    letI := st
    letI := hostAlg D
    refine ⟨hd.f_eq, ?_⟩
    rw [hO.rr_eq, OntoChain.rank_eq]
    push_cast
    rfl
  obtain ⟨w, hw⟩ := GlobalTheory.BigOnBase.exists_tieCoord_base ht (fun g hg => by
    obtain ⟨u, -, e⟩ := (mem_base_iff h1 g).1 hg
    exact ⟨u, e⟩) hOk h1 h2 hM.HV hM.jV hM.HW hμ (phasedLift_one hth) hU hB hrat hI hT2
  obtain ⟨tU, hMk, hP⟩ := level_of_tied ht hOk.irr h1
  exact on_of_has_atPlaces N (withCoord O w) C hRk hMk hSup hP hw hSp hS hT0 hD hJ hI hT2 hT1 hSh
    (leafIndexU_of O D.R.f (mirab_levelGroups _ _) hSq hY tU hN) hBS (leafUnip_of O D.R.f (mirab_levelGroups _ _) hSq tU hN)
    hDG hDR hD2 hDL hPg hSz hX hBad hE hCE tE1

end GlobalTheory.OnAtPlacesBase

end
