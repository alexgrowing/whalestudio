import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.JointCmpEmbeddingY
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ModelsOK
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ValidForConstructedPointClassesEventuallyWorking
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IteratedFDerivConstSmulOfNe
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PendTThFLtOfKapLawLt
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.XiExThetaGeneral
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelEntryPeriodNeZeroAndLatticeLaws
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SiteSystemRanksEqDatumRanks
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteDatumLevelPosBadPrimesNoConjugatePair
import Formalism.LocalToGlobal.PairingIndexBounds.HalvesRecursion.Outright
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.KerInert GlobalTheory.TwV

namespace GlobalTheory.TwV

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 2000000 in

theorem site_law_xiIn : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S =>
    S.Pair → S.Pos → S.Move → S.Away → S.Law ∧
    Lt.LawInLt (sysS H X std) S.hfin S.E S.hLT (hT.gat_pos u w hg) (J.fd std) t.B t.χ S.lam (GlobalTheory.TwU.ssRec t u μ) (t.rd u μ).lev
      (J.xi0 std S.Xi) S.muT ∧
    AdmLoc.XiIn (sysS H X std) S.E S.hfin S.hst S.hLT (hT.gat_pos u w hg) (J.fd std) t.B t.χ S.lam (GlobalTheory.TwU.ssRec t u μ) (t.rd u μ).lev
      (J.xi0 std S.Xi) S.muT) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S hPair hPos hMove hAway
  obtain ⟨hδ, hLat, hVec, hEq⟩ := GlobalTheory.TieBase.base_data t
  obtain ⟨hcl, hSS⟩ := GlobalTheory.BadPrimes.lev_pos_and_noConj J.A J.dtU J.a J.pins J.tie
  have hmm : (sysS H X std).mm = D.R.m := (DelB.sysS_ranks S).1
  have hLaw : S.Law :=
    GlobalTheory.TwU.LawAll.kapLawLt_frecG D t.cc t.δ t.B t.χ t.cc_ok t.δ_ok hδ t.χ_ok hLat hVec hEq (GlobalTheory.TwU.ssRec t u μ) (t.rd u μ).lev hcl hSS
      (D.what₂.places.resChar w) (sysS H X std) S.E.toCEmb (hT.gat_pos u w hg) (J.fd std) S.lam (J.xi0 std S.Xi) S.muT (J.rho std)
      (Formalism.L2.PairingIndexBounds.F.ltC S.g S.hLT) hPair hPos hMove
  refine ⟨hLaw, ?_, ?_⟩
  · intro j hj c L0 La' ε hrep hL' hε
    letI := wittFractionAlgebraCp (D.what₂.places.resChar w)
    letI := algKfC S.E.toCEmb
    exact GlobalTheory.TwU.KapLawLt.stab (h := hLaw) (hj := hj) c L0 La' ε (repOf_lat _ S.hfin j (c, L0) hrep) hL' hε
  · intro v j hj
    have hRB := GlobalTheory.TwU.pendT_ThF_lt_of_kapLawLt (D.what₂.places.resChar w) (sysS H X std) S.E S.hfin S.hst S.g S.hLT D.what₂.Tau
      (hT.gat_pos u w hg)
      (Formalism.L2.PairingIndexBounds.F.FrecG S.E.toCEmb (hT.gat_pos u w hg) (J.fd std) t.B t.χ S.lam (GlobalTheory.TwU.ssRec t u μ) (t.rd u μ).lev (J.xi0 std S.Xi) S.muT
        (Formalism.L2.PairingIndexBounds.F.ltC S.g S.hLT)) hLaw
    exact hRB.2 v j hj
      (GlobalTheory.XiGen.xiEx_theta_general D t.cc t.δ t.B t.χ t.cc_ok t.δ_ok hδ t.χ_ok hLat hVec hEq
        (Formalism.L2.PairingIndexBounds.Rec.model_at_split_places_holds D) (Formalism.L2.PairingIndexBounds.Rec.split_place_moves_compose D) (GlobalTheory.TwU.ssRec t u μ) (t.rd u μ).lev hcl hSS
        (D.what₂.places.resChar w) (sysS H X std) S.E.toCEmb (hT.gat_pos u w hg) (J.fd std) S.lam (J.xi0 std S.Xi) S.muT (J.rho std)
        (Formalism.L2.PairingIndexBounds.F.ltC S.g S.hLT) hPair v j hj (hAway v j (hmm ▸ hj)))

end GlobalTheory.TwV
