import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LineSCShortExact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernPartOverProperClosedEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.L2DbarChartMeasureTransfer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankTwoFlagRationalSections
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxForm GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.Cartier GlobalTheory.CovTest GlobalTheory.CovTest.SwapLine GlobalTheory.LineForm
open scoped Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LineNull

open GlobalTheory.CurveDens

theorem isCosSq_unique {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ} {V L L' : X.Modules} {r : ℕ}
    (h : Met p σ V r) {l : L ⟶ V} {l' : L' ⟶ V} (hL : IsVB L 1) (hL' : IsVB L' 1) (hl : IsSubbundle l)
    (hl' : IsSubbundle l') {v v' : CxPts p σ → ℝ} (hv : IsCosSq h l l' v) (hv' : IsCosSq h l l' v') : v = v' := by
  funext y
  obtain ⟨U, t, t', ht, ht', hU⟩ := AdjFlag.exists_frames hL hL' y
  have a := AdjFlag.form_frame_pos (h.restrict hl hL) ht hU
  have b := AdjFlag.form_frame_pos (h.restrict hl' hL') ht' hU
  rw [h.form_restrict hl hL t t hU] at a
  rw [h.form_restrict hl' hL' t' t' hU] at b
  have e := (hv U t t' y hU).symm.trans (hv' U t t' y hU)
  exact mul_right_cancel₀ a.ne' (mul_right_cancel₀ b.ne' e)

theorem part_cosSq_one : ∀ (k : Type) [CommRing k] (B Y : Scheme.{0}) [IsIntegral B] [IsIntegral Y] (q : B ⟶ Sp k) (p : Y ⟶ Sp k) (d : ℕ)
    (hB : IsRegVar q d) (hY : IsRegVar p (d + 1)) (π : Y ⟶ B) (w : π ≫ q = p) (E : B.Modules) (h : VMetric q E 2) (H : h.IsCInf)
    (flB : Vert.Flag E 2) (fl : Vert.Flag ((Scheme.Modules.pullback π).obj E) 2),
    IsFlagBundle π (fun _ : Unit => E) (fun _ => 2) (fun _ => fl) → ∀ (A : HermLB q) (σ : k →+* ℂ),
    ∀ v : CxPts p σ → ℝ, GlobalTheory.CurveDens.IsCosSq ((h.pull π w).met σ) (fl.ι 1) ((Scheme.Modules.pullback π).map (flB.ι 1)) v →
    ∀ α : (hY.atlas σ).Fld, (hY.atlas σ).IsForm α → ∀ ε : ℤˣ, (hY.atlas σ).part α ε {y | v y = 1} = 0 := by
  intro k _ B Y _ _ q p d hB hY π w E h H flB fl hfl A σ v hv α _ ε
  obtain ⟨r, hr, -, h₂⟩ := exists_ratSec_fam5 k B Y q p d hB.toIsArithVar hY.toIsArithVar hB.regular π w E h H flB fl hfl A
  obtain ⟨v', hv', hlt⟩ := h₂ σ
  obtain rfl : v = v' := isCosSq_unique _ (fl.isVB 1) ((flB.pull π).isVB 1) (fl.isSubbundle 1)
    ((flB.pull π).isSubbundle 1) hv hv'
  generalize ((fam5 π w H flB fl A 0).dual.tens (fam5 π w H flB fl A 4)).div hr = D at hlt
  have hset : {y : CxPts p σ | y.1 (IsLocalRing.closedPoint ℂ) ∈ (D.supp : Set Y)} = (offSupp p σ D)ᶜ := by
    ext y
    rw [Set.mem_compl_iff, offSupp, mem_ptsIn]
    exact not_not.symm
  have hA : MeasurableSet {y : CxPts p σ | y.1 (IsLocalRing.closedPoint ℂ) ∈ (D.supp : Set Y)} := by
    rw [hset]
    exact (isOpen_ptsIn _).measurableSet.compl
  refine measure_mono_null (t := {y : CxPts p σ | y.1 (IsLocalRing.closedPoint ℂ) ∈ (D.supp : Set Y)})
    (fun y hy => ?_) ?_
  · rw [hset]
    exact fun hm => (hlt y hm).1.ne hy
  · exact GlueCoverNull.glueMeas_null _ _ hA fun c =>
      ChernNull.chart_null hY.toIsArithVar D.supp.isClosed (CartierDiv.genericPoint_notMem_supp D) σ c

end GlobalTheory.LineNull
