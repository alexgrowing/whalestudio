import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.ChernOn
import Development.AbelianVarietyTheory.Definitions.Divisors.NefFibOfIsNef
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackSmoothFunctionCInfAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticDegreeMixedLinearRoot
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open scoped ENNReal Classical
open MvPolynomial GlobalTheory.ArInt
open CategoryTheory AlgebraicGeometry GlobalTheory GlobalTheory.Mean4O GlobalTheory.HermLB

open GlobalTheory.Points ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi

noncomputable section

open GlobalTheory.CxPts
open scoped ContDiff Topology

namespace GlobalTheory.HermLB

variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k}

theorem genWt_chart_eq (L : HermLB p) (t : LB.Gen L.B) (ht : t.IsGen) (σ : k →+* ℂ) {i j : L.B.ι}
    {y : CxPts p σ} (hi : y ∈ ptsIn p σ (L.B.U i)) (hj : y ∈ ptsIn p σ (L.B.U j)) :
    (L.φ σ).φ i y - logSq y _ (t.s i) = (L.φ σ).φ j y - logSq y _ (t.s j) := by
  have hy : y ∈ ptsIn p σ (L.B.U i ⊓ L.B.U j) := mem_ptsIn_inf.2 ⟨hi, hj⟩
  have e := congrArg (logSq y _) (ht i j)
  rw [logSq_res _ hy, logSq_mul hy, logSq_res _ hy] at e
  have e2 := (L.φ σ).trans i j y hi hj
  change _ = _ - logSq y _ (L.B.g i j) at e2
  linarith

def genWt (L : HermLB p) (t : LB.Gen L.B) (σ : k →+* ℂ) (y : CxPts p σ) : ℝ :=
  (L.φ σ).φ (pick L.isLB y) y - logSq y _ (t.s (pick L.isLB y))

theorem genWt_eq (L : HermLB p) (t : LB.Gen L.B) (ht : t.IsGen) (σ : k →+* ℂ) {j : L.B.ι}
    {y : CxPts p σ} (hj : y ∈ ptsIn p σ (L.B.U j)) :
    genWt L t σ y = (L.φ σ).φ j y - logSq y _ (t.s j) :=
  genWt_chart_eq L t ht σ (mem_pick L.isLB y) hj

theorem cInfAt_logSq {σ : k →+* ℂ} {U : X.Opens} (u : Γ(X, U)ˣ) {y : CxPts p σ}
    (hy : y ∈ ptsIn p σ U) : CInfAt (fun z => logSq z U u) y := by
  have hs : ContDiff ℝ ∞ fun v : Unit → ℂ => ‖v ()‖ ^ 2 := (contDiff_apply ℝ ℂ ()).norm_sq ℂ
  refine ⟨U, Unit, inferInstance, fun _ => u.val, fun v => Real.log (‖v ()‖ ^ 2),
    {v | ‖v ()‖ ^ 2 ≠ 0}, hy, isOpen_ne_fun hs.continuous continuous_const, ?_,
    hs.contDiffOn.log fun _ h => h, Filter.Eventually.of_forall fun _ => rfl⟩
  exact pow_ne_zero _ (norm_ne_zero_iff.2 (ev_ne_zero hy u.isUnit))

theorem cInfAt_genWt (L : HermLB p) (t : LB.Gen L.B) (ht : t.IsGen) (σ : k →+* ℂ) (y : CxPts p σ) :
    CInfAt (genWt L t σ) y := by
  have hj := mem_pick L.isLB y
  refine ((L.cInf σ _ y hj).add (cInfAt_logSq (t.s (pick L.isLB y)) hj).neg).congr ?_
  filter_upwards [(isOpen_ptsIn (p := p) (σ := σ) _).mem_nhds hj] with z hz
  rw [genWt_eq L t ht σ hz, sub_eq_add_neg]

theorem isConj_genWt (L : HermLB p) (t : LB.Gen L.B) (ht : t.IsGen) (σ σ' : k →+* ℂ) :
    (Weight.ofFun (genWt L t σ)).IsConj (Weight.ofFun (genWt L t σ')) := by
  intro i y y' h _
  change genWt L t σ' y' = genWt L t σ y
  have hj := mem_pick L.isLB y
  have hj' : y' ∈ ptsIn p σ' (L.B.U (pick L.isLB y)) := by
    change ⊤ ≤ y'.1 ⁻¹ᵁ _
    rw [h]
    exact fun x _ => hj (Set.mem_univ _)
  rw [genWt_eq L t ht σ' hj', genWt_eq L t ht σ hj, L.conj σ σ' _ y y' h hj]
  congr 1
  simp only [logSq, CxPts.ev_conj h hj, RCLike.norm_conj]

theorem isometric_fnB_of_gen : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (L : HermLB p)
    (t : LB.Gen L.B), t.IsGen → ∃ (c : ∀ σ : k →+* ℂ, CxPts p σ → ℝ) (hc : ∀ σ y, CxPts.CInfAt (c σ) y)
      (hcc : ∀ σ σ', (Weight.ofFun (c σ)).IsConj (Weight.ofFun (c σ'))), (fnB c hc hcc).Isometric L := by
  intro k _ X p L t ht
  refine ⟨genWt L t, fun σ y => cInfAt_genWt L t ht σ y, fun σ σ' => isConj_genWt L t ht σ σ', ?_⟩
  refine isometric_of_local L.B.U (exists_chart L.isLB) id (fun _ => PUnit.unit) (fun _ => le_rfl)
    (fun _ => le_top) t.s (fun x j j' hj hj' => ?_) (fun σ j y hy => ?_)
  · have e := congrArg (gm (𝟙 X) x _) (ht j j')
    have hx : (𝟙 X : X ⟶ X) x ∈ L.B.U j ⊓ L.B.U j' := ⟨hj, hj'⟩
    rw [map_mul, gm_res _ x _ hx, gm_res _ x _ hx] at e
    rw [e]
    change _ = _ * (gm (𝟙 X) x _ (1 : Γ(X, ⊤ ⊓ ⊤)ˣ))⁻¹ * _
    rw [map_one, inv_one, mul_one]
    rfl
  · change _ = genWt L t σ y + _
    rw [genWt_eq L t ht σ hy]
    change (L.φ σ).φ j y = _ - _ + _
    ring

end GlobalTheory.HermLB

end
