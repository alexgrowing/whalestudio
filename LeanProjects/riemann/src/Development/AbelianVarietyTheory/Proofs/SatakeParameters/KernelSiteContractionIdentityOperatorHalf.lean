import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Reframe
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ContractionIdentityFramesWithOperatorScalarStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SiteFramesAndChangedFramesInvertibleStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SiteSystemRanksEqDatumRanksStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SeriesCoefficientsAtKernelSiteOfClassSeriesStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaSeriesSiteEqChangedFrameClassSeriesStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelScalarOfSourceTargetPartsProductStatement
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwV.DelB TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV.DelB

theorem delPolAt_site : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => J.Dict std → S.Pair → S.Pos → S.Law → ∀ (d : Dec J std), ∀ ι : ℂ →+* ℂ_[D.what₂.places.resChar w], (∀ z : TaylorLogMetric.Qbar, ι z = S.lam z) → letI := wittFractionAlgebraCp (D.what₂.places.resChar w); letI := algKfC S.E.toCEmb; ∀ (Φ₀ : ∀ j, MvPolynomial (GL3Theta.FrV D (D.R.N (j + 1))) ℂ →ₛₗ[ι] XspC ((sysS H X std).Pj (j + 1)) ℂ_[D.what₂.places.resChar w]) (τ : ∀ j, (sysS H X std).Lv.comp (j + 1) → ((sysS H X std).Pj (j + 1)).Tup → XspC ((sysS H X std).Pj (j + 1)) ℂ_[D.what₂.places.resChar w] →ₗ[ℂ_[D.what₂.places.resChar w]] XspC ((sysS H X std).Pj (j + 1)) ℂ_[D.what₂.places.resChar w]) (sc : ∀ j, (sysS H X std).Lv.comp (j + 1) → ((sysS H X std).Pj (j + 1)).Tup → ℂ_[D.what₂.places.resChar w]) (sO : ∀ j, (sysS H X std).Lt j → ℂ_[D.what₂.places.resChar w]) (Gm : ∀ j, (sysS H X std).Lt j → ((ex.tw.fm u μ).lat j).V → ((sysS H X std).Pj j).Xsp), ∀ j < D.R.m, ∀ (cK : ℂ_[D.what₂.places.resChar w]) (hN : RankTie (sysS H X std) D j), MoveH S.Y u μ (kaAt X H hT).cmp (fun j La => glInv (sysS H X std) j (BOf d.fd2 j La)) Gm j → TieOpS (Y := S.Y) t u μ (clsAt X H) Gm sO j (eIdx (sysS H X std) D (hT.gat_pos u w hg) j hN) (ι := ι) (Φ₀ j) → KernelEntryDegreeCondition (Y := S.Y) t u μ (clsAt X H) j (eIdx (sysS H X std) D (hT.gat_pos u w hg) j hN) → DelYEqH S.Y (fun j La' => VOf ℂ_[D.what₂.places.resChar w] d.fd2 (ltC S.g S.hLT) j La') τ j → (∀ (La : (sysS H X std).Lt j) (La' : (sysS H X std).Lt (j + 1)), ((sysS H X std).Pj j).IsLatTup La.2 → ((sysS H X std).Pj (j + 1)).IsLatTup La'.2 → cK * (Formalism.L2.G.Pend.cA (sysS H X std) ℂ_[D.what₂.places.resChar w] j (BOf d.fd2 j La) * sO j La) * ι (d.uS S j La) * ι (d.uT S j La') = sc j La'.1 La'.2) → DelPolAt (Y := S.Y) t u μ (clsAt X H) (kaAt X H hT).cmp (fun j => clsAt X H (j + 1)) (phiH D Φ₀ τ sc) (srOf S.Y) j cK) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S hDict hPair hPos hLaw d ι hι
  intro Φ₀ τ sc sO Gm j hj cK hN hMove hOp hDeg hDel hSc
  letI := wittFractionAlgebraCp (D.what₂.places.resChar w)
  letI := algKfC S.E.toCEmb
  have hR := GlobalTheory.T.siteSystem_ranks_eq_datum_ranks S
  have hFr := (GlobalTheory.T.siteFrames_and_changedFrames_invertible S).2 d
  have hSer := GlobalTheory.T.thetaSeries_site_eq_changedFrame_classSeries S hDict hPair hPos d ι hι j hj
  have hSerH := GlobalTheory.T.seriesCoefficients_at_kernelSite_of_classSeries S d ι j hN
  have hChi := GlobalTheory.T.kernelScalar_of_sourceTarget_parts_product S hDict d ι j hj (fun j La => Formalism.L2.G.Pend.cA (sysS H X std) ℂ_[D.what₂.places.resChar w] j (BOf d.fd2 j La) * sO j La) sc cK hSc
  exact GlobalTheory.T.contraction_identity_frames_with_operator_scalar t u μ _ (sysS H X std) S.E S.hfin S.hst S.g S.hLT (hT.gat_pos u w hg) d.fd2 (ltC S.g S.hLT)
    (fun j La La' => FrecG S.E.toCEmb (hT.gat_pos u w hg) (J.fd std) t.B t.χ S.lam (ssRec t u μ) (t.rd u μ).lev (J.xi0 std S.Xi) S.muT (ltC S.g S.hLT) j La La')
    (d.gS S ι) hFr hLaw _ (clsAt X H) (kaAt X H hT).cmp (fun j => clsAt X H (j + 1)) ι Φ₀ τ sc (d.sH S ι) sO Gm j (hR.1 ▸ hj) cK hN
    hSer hMove hOp hDeg hSerH hChi hDel

end GlobalTheory.TwV.DelB
