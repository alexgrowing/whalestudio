import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeVolSlopeOfTendsto

open NumberField IsDedekindDomain Filter Topology
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovHt.Link GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo GlobalTheory.ProjVar GlobalTheory.Cartier GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.CovHt.Link

variable {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A} {s : FinalTheorems S κ}

def apxGap (Φ : s.Flag) (L : CmList A) (x : ToroidalCompactificationData s) (P : Mean4O.PolOf x Φ) (B : ℝ) (u : AllWt.Weight S.Dw) (r : ℚ)
    (k : s.Comp) (σ : D.what₂.LL →+* ℂ) (y : Pts (Φ.C k).Y σ) : ℝ :=
  lnN (GlobalTheory.ShFam.DeKeyTrue.hodgeLw x Φ k σ u) (genAt ((Φ.C k).Lw u) (under y)) y -
    lnN ((mbarOf P B (wtR L u) r k).m σ) (genAt ((Φ.C k).Lw u) (under y) ^ ((mbarOf P B (wtR L u) r k).n : ℕ)) y /
      (((mbarOf P B (wtR L u) r k).n : ℕ) : ℝ)

end GlobalTheory.CovHt.Link
