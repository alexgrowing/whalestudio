import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GrothendieckDeformation
import Development.AbelianVarietyTheory.Definitions.Divisors.CovolXOfCovol
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
import Development.AbelianVarietyTheory.Definitions.Divisors.WellChosen
import Development.AbelianVarietyTheory.Definitions.Divisors.MeanLogLeOfBounds
import Development.AbelianVarietyTheory.Definitions.Divisors.WedgeNrmLeOfWedgeNormLe
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomWeightHomWeight
import Development.AbelianVarietyTheory.Definitions.Divisors.MemLevEigenIffTransl
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LogMeanShares.LogMeanStatements.HSClaim
import Development.AbelianVarietyTheory.Definitions.Divisors.GenRatios
import Development.AbelianVarietyTheory.Definitions.Divisors.BadElt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoversOfLifts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HostBoundHolds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightBoundHolds
import Development.AbelianVarietyTheory.Definitions.Divisors.QuoIff

open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.CovTop.FlatSz

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ}

theorem lrd_bounds {PP A M : ℝ} (hH : HostNum D L PP A M) :
    0 ≤ GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects.lrd D.host.E ∧ GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects.lrd D.host.E ≤ 2 * L.sc.L := by
  have hne : (discr D.host.E : ℝ) ≠ 0 := by exact_mod_cast NumberField.discr_ne_zero D.host.E
  have h1 : (1 : ℝ) ≤ |(discr D.host.E : ℝ)| := by
    rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs (NumberField.discr_ne_zero D.host.E)
  have hlog0 : 0 ≤ Real.log |(discr D.host.E : ℝ)| := Real.log_nonneg h1
  have hf : (0 : ℝ) < D.R.f := by have := hH.f8; positivity
  have heq : GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects.lrd D.host.E = Real.log |(discr D.host.E : ℝ)| / (2 * D.R.f) := by
    rw [GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects.lrd, NumberField.rootDiscr_def, Int.cast_abs, Real.log_rpow (abs_pos.2 hne), hH.deg]
    push_cast
    ring
  rw [heq]
  refine ⟨by positivity, ?_⟩
  rw [div_le_iff₀ (by positivity)]
  nlinarith [hH.disc]

theorem abs_flatDegVal_le (p : PtAt ex Csz) (i : Fin D.R.m) {PP A M : ℝ} (hH : HostNum D L PP A M) (hW : WtNum p i PP) :
    |GlobalTheory.FlatLine.flatDegVal (dat p i) (Formalism.L2.DIV.ofRecord D L p.Del p.h0).logOm| ≤ 9 * D.R.r * L.sc.L := by
  have hd : p.T.Q.H.d = D.host.d := p.fw.laws.pins.1.1
  have hpq : ((dat p i).p : ℝ) + (dat p i).q = D.R.r := by exact_mod_cast hW.sig.2.2
  have hom := hW.om
  have hL : 10 ≤ L.sc.L := hH.big.2.1
  have hld : Real.log (p.T.Q.H.d : ℝ) ≤ L.sc.L := by rw [hd]; exact hH.logd
  have hld0 : 0 ≤ Real.log (p.T.Q.H.d : ℝ) := Real.log_natCast_nonneg _
  obtain ⟨hr0, hr1⟩ := lrd_bounds hH
  unfold GlobalTheory.FlatLine.flatDegVal
  set a := (Formalism.L2.DIV.ofRecord D L p.Del p.h0).logOm
  set P : ℝ := ((dat p i).p : ℝ)
  set Q : ℝ := ((dat p i).q : ℝ)
  set u := Real.log (p.T.Q.H.d : ℝ)
  set v := GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects.lrd D.host.E
  have hP : 0 ≤ P := Nat.cast_nonneg _
  have hQ : 0 ≤ Q := Nat.cast_nonneg _
  have h1 : |(P - Q) / 2 * a| ≤ (P + Q) / 2 * (3 * L.sc.L) := by
    rw [abs_mul, abs_div, abs_two]
    refine mul_le_mul ?_ hom (abs_nonneg _) (by positivity)
    gcongr
    exact abs_le.2 ⟨by linarith, by linarith⟩
  have h2 : |Q * (u - v)| ≤ Q * (2 * L.sc.L) := by
    rw [abs_mul, abs_of_nonneg hQ]
    exact mul_le_mul_of_nonneg_left (abs_le.2 ⟨by linarith, by linarith⟩) hQ
  have h3 := abs_add_le ((P - Q) / 2 * a) (Q * (u - v))
  rw [hpq] at h1
  have hQr : Q ≤ D.R.r := by rw [← hpq]; linarith
  have hr : (0 : ℝ) ≤ D.R.r := Nat.cast_nonneg _
  nlinarith [mul_le_mul_of_nonneg_right hQr (by linarith : (0 : ℝ) ≤ 2 * L.sc.L), mul_nonneg hr (by linarith : (0 : ℝ) ≤ L.sc.L)]

end GlobalTheory.CovTop.FlatSz

namespace GlobalTheory.CovTop.FlatSz

theorem flatDegVal_covers : Size → Covers fun Fm x _ ι p i Y PP _ =>
    |GlobalTheory.FlatLine.flatDegVal (dat p i) (Formalism.L2.DIV.ofRecord (Fm.D x ι) (Fm.L x ι) p.Del p.h0).logOm| ≤
      9 * (Fm.D x ι).R.r * (Fm.L x ι).sc.L := by
  intro _
  have h1 := GlobalTheory.CovTop.CovSz.covers_of_lifts
    (Q := fun Fm x _ ι _ _ _ PP => ∃ A, HostNum (Fm.D x ι) (Fm.L x ι) PP A 0) (Sizes.hostN 0)
    (fun _ _ _ _ _ _ C _ h _ _ _ => ⟨C, h⟩)
  have h2 := GlobalTheory.CovTop.CovSz.covers_of_lifts
    (Q := fun _ _ _ _ p i _ PP => WtNum p i PP) GlobalTheory.CovTop.WtShape.wtN
    (fun _ _ _ _ _ _ _ _ h _ _ _ => h)
  exact GlobalTheory.CovTop.CovSz.covers_imp (GlobalTheory.CovTop.CovSz.covers_and h1 h2)
    (fun _ _ _ _ p i _ _ h => abs_flatDegVal_le p i h.1.choose_spec h.2)

end GlobalTheory.CovTop.FlatSz

end
