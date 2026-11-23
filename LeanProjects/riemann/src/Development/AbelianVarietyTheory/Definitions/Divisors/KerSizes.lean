import Mathlib
import Formalism.LocalToGlobal.KernelLattices.FirstKernelLawReading
import Formalism.LocalToGlobal.Divisibility.NumbersLemmas
import Development.AbelianVarietyTheory.Definitions.Divisors.FactorBounds
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ColHeightSharpWith

noncomputable section

namespace GlobalTheory.ColRows

open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {K : G.Consts} {Y : DivX D} {cX : ExtraC}
  {ex : Extra D L hT Gi Gl K Y cX}

structure KerTies (t : KerEntTied ex) (W : Wts t.X t.Pr.Word D.R) (Del h0 : ℕ) : Prop where
  host : HostTie (ofRecord D L Del h0) t.seam t.Pr
  wts : ∃ pl : RPl D.R ≃ t.X.Tau, ∀ u, WeightTie (ofRecord D L Del h0) W pl (t.word u) (letterOf D L Del h0 u)
  chr : CharTie (ofRecord D L Del h0) t.seam W t.Ch t.glob t.sel
  an : AnalyticTie D t.δ t.χ t.cD
  mu0 : t.tup D.what₂.mu0 = 1
  sharp : (t.cst D.what₂.mu0).sharp = true
  m2 : t.m2 = D.R.m - 2
  fld : ∀ u, FieldOfDefinition W t.sel (t.tup D.what₂.mu0) (t.cst D.what₂.mu0) (t.word u) t.amb

structure KerSizes (t : KerEntTied ex) (W : Wts t.X t.Pr.Word D.R) (Del h0 : ℕ) (CY CT : ℝ) : Prop where
  sizes : Sizes t.Pr W L.sc.a
  what₂ : ∀ u, GlobalTheory.Core.Ht2.SizeRowsS CY (ofRecord D L Del h0) (letterOf D L Del h0 u)
  logT : ∀ u, Real.log (((D.mem u).A.T : ℕ) : ℝ) ≤ CT * D.R.m * L.sc.L

theorem KerSizes.mono {t : KerEntTied ex} {W : Wts t.X t.Pr.Word D.R} {Del h0 : ℕ} {CY CT CT' : ℝ} (h : KerSizes t W Del h0 CY CT)
    (hC : CT ≤ CT') (hL : 0 ≤ L.sc.L) : KerSizes t W Del h0 CY CT' :=
  ⟨h.sizes, h.what₂, fun u => (h.logT u).trans (by
    have : (0 : ℝ) ≤ D.R.m := Nat.cast_nonneg _
    gcongr)⟩

end GlobalTheory.ColRows

end
