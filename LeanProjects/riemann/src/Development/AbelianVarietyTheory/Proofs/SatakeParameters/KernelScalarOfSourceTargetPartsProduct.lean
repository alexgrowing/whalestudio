import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Reframe
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FrameFactorsCancelPPowerOfPairSeriesStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LatticeTuplePairScalarEqCharacterProductStatement
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwV.DelB TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV.DelB

theorem tieChiH_of_parts : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => J.Dict std → ∀ (d : Dec J std) (ι : ℂ →+* ℂ_[D.what₂.places.resChar w]), ∀ j < D.R.m, ∀ (cB : ∀ j, (sysS H X std).Lt j → ℂ_[D.what₂.places.resChar w]) (sc : ∀ j, (sysS H X std).Lv.comp (j + 1) → ((sysS H X std).Pj (j + 1)).Tup → ℂ_[D.what₂.places.resChar w]) (cK : ℂ_[D.what₂.places.resChar w]), (∀ (La : (sysS H X std).Lt j) (La' : (sysS H X std).Lt (j + 1)), ((sysS H X std).Pj j).IsLatTup La.2 → ((sysS H X std).Pj (j + 1)).IsLatTup La'.2 → cK * cB j La * ι (d.uS S j La) * ι (d.uT S j La') = sc j La'.1 La'.2) → TieChiH S.Y t u μ (clsAt X H) (fun j => clsAt X H (j + 1)) ι sc (d.sH S ι) cB j cK) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S hD d ι j hj cB sc cK hsc La hLa c' L' hL'
  have hLat := S.Y.Rep_lat j La hLa
  have hsC := GlobalTheory.T.latticeTuplePairScalar_eq_characterProduct S hD d j hj La (c', L') hLat hL'
  have he := GlobalTheory.T.frameFactors_cancel_p_power_of_pair_series _ (sysS H X std) S.E S.hfin S.hst S.g S.hLT D.what₂.Tau (hT.gat_pos u w hg)
    (FrecG S.E.toCEmb (hT.gat_pos u w hg) (J.fd std) t.B t.χ S.lam (ssRec t u μ) (t.rd u μ).lev (J.xi0 std S.Xi) S.muT (ltC S.g S.hLT)) j La (c', L')
  have h2 := hsc La (c', L') hLat hL'
  show cK * S.E.iK (S.Y.eS j La * (S.Y.eT j (c', L'))⁻¹) * cB j La * (pPow (sysS H X std) j La (c', L') * ι (d.sC S j La (c', L'))) = _
  rw [hsC]
  have hι : ∀ x y : ℂ, ι (x * y) = ι x * ι y := map_mul ι
  simp only [hι]
  linear_combination (cK * cB j La * ι (d.uS S j La) * ι (d.uT S j (c', L')) *
      ι ((GL3Theta.rhoOf D (t.O u μ).mt j ((t.O u μ).dt j (clsAt X H j La.1 La.2)) : ℂˣ) : ℂ) *
      ι ((GL3Theta.rhoOf' D (t.O u μ).mt j ((t.O u μ).dt (j + 1) (clsAt X H (j + 1) c' L')) : ℂˣ) : ℂ)) * he +
    ι ((GL3Theta.rhoOf D (t.O u μ).mt j ((t.O u μ).dt j (clsAt X H j La.1 La.2)) : ℂˣ) : ℂ) *
      ι ((GL3Theta.rhoOf' D (t.O u μ).mt j ((t.O u μ).dt (j + 1) (clsAt X H (j + 1) c' L')) : ℂˣ) : ℂ) * h2

end GlobalTheory.TwV.DelB
