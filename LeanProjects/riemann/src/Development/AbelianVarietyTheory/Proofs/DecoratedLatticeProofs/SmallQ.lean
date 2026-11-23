import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CombAtSingleZero
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing MeasureTheory

noncomputable section

namespace GlobalTheory.FinPl.VLast

variable {D : D7} {u : D.what₂.Word}

def kerL (d : Dat D u) (j : ℕ) (h : j + 2 * 0 + 2 = D.R.m)
    (P₁ : Formalism.IndefR.Links.PolF D (d.st (j + 1)).V.rank (d.st j).V.rank)
    (P₂ : Formalism.IndefR.Links.PolF D d.top.st.V.rank (d.st (j + 1)).V.rank) (φ : GA D (D.sp.X j) → ℂ)
    (h' : GA D D.sp.X') : ℂ :=
  ∫ g in (d.st (j + 1)).fd, (d.pT j h).ω (g, h') ((d.pT j h).pt P₂) 0 *
    (∫ h₀ in (d.x j).vol.𝓕, φ h₀ * (d.p j).ω (embA (d.bes j 0 h).d (d.bes j 0 h).o h₀, g)
      ((d.p j).ω (d.t j, 1) ((d.p j).pt P₁)) 0 ∂(d.x j).vol.μ) ∂(d.st (j + 1)).ν

def smallQ (d : Dat D u) (j : ℕ) (h : j + 2 * 0 + 2 = D.R.m) (om0 : Om (d.bes j 0 h).V₀ (D.sp.X (j + 1)))
    (omT : Om (D.sp.X (j + 1)) D.sp.X') (φ : GA D (D.sp.X j) → ℂ) (Ξ : WO (d.bes j 0 h).V₀ (D.sp.X (j + 1)) → ℂ)
    (Φ : WO (D.sp.X (j + 1)) D.sp.X' → ℂ) (F : GA D D.sp.X' → ℂ) : ℂ :=
  ∫ h' in d.top.fd, F h' * (∫ g in (d.x (j + 1)).vol.𝓕, omT (g, h') Φ 0 *
    (∫ h₀ in (d.x j).vol.𝓕, φ h₀ * om0 ((d.bes j 0 h).o.emb (h₀, 1), g) Ξ 0 ∂(d.x j).vol.μ) ∂(d.x (j + 1)).vol.μ) ∂d.top.ν

end GlobalTheory.FinPl.VLast

end
