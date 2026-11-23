import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsTateZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticFunctionalQuadraticRelations
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GradedMetricPullbackIsometric
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetMetricShortExactIsometric
open CategoryTheory AlgebraicGeometry Set Matrix ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.ArInt GlobalTheory.TorsionForm GlobalTheory.ThetaRR
open GlobalTheory.LB (toMod)
open GlobalTheory.LieVB (omega)
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe (Fl Pt stdLat symMat tauU siegel symPart ChernIsFlat IsMetric InducesPolarisation cov)
open ReciprocityTheory.L2DbarEstimates (V)
open Filter Topology
open scoped ContDiff
open GlobalTheory.HermFrame GlobalTheory.VB
open scoped ComplexOrder

namespace GlobalTheory.BcScale

theorem extTrace_exp_smul {m l : Type} [Fintype m] [Fintype l] [DecidableEq m] [DecidableEq l]
    {D : ℕ} {K : V D → Matrix (m ⊕ l) (m ⊕ l) ℂ} {z : V D} (h : MContDiffAt 1 K z)
    (hp : ∀ᶠ x in 𝓝 z, (K x).PosDef) (s : ℝ) :
    extTrace (fun x => (Real.exp s : ℂ) • K x) z = extTrace K z := by
  have e (M : Matrix (m ⊕ l) (m ⊕ l) ℂ) :
      chg (((Real.exp (s / 2) : ℝ) : ℂ) • (1 : Matrix (m ⊕ l) (m ⊕ l) ℂ)) M = (Real.exp s : ℂ) • M := by
    rw [chg, conjTranspose_smul, transpose_smul, transpose_smul, conjTranspose_one, transpose_one,
      Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.smul_mul, Matrix.mul_one, smul_smul,
      Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul, ← Real.exp_add, add_halves]
  simp only [← e]
  refine extTrace_chg (A := fun _ => ((Real.exp (s / 2) : ℝ) : ℂ) • 1) h hp
    (fun _ _ => contDiffAt_const) ?_ (fun η => mdbar_const _ _ _) (.of_forall fun _ => ?_)
  · rw [det_smul, det_one, mul_one]
    exact (pow_ne_zero _ (by exact_mod_cast (Real.exp_pos _).ne')).isUnit
  · ext i j
    simp [toBlocks₂₁]

variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ}

theorem restrict_expMul {E F : X.Modules} {r s : ℕ} (h : Met p σ E r) {i : F ⟶ E}
    (hi : IsSubbundle i) (hF : IsVB F s) (u : CxPts p σ → ℝ) :
    (h.expMul u).restrict hi hF = (h.restrict hi hF).expMul u :=
  Met.ext_form fun U t t' y hy => by
    rw [Met.form_restrict _ _ _ _ _ hy, Met.form_expMul, Met.form_expMul,
      Met.form_restrict _ _ _ _ _ hy]

theorem bcMeas_expMul {S : ShortComplex X.Modules} {r s : ℕ} {h : Met p σ S.X₂ (r + s)}
    (hS : S.ShortExact) (h₁ : IsVB S.X₁ r) (h₃ : IsVB S.X₃ s) (H : h.IsCInf) (t : ℝ) :
    (h.expMul fun _ => t).bcMeas hS h₁ h₃ = h.bcMeas hS h₁ h₃ := by
  have hd (c : AlgChart p σ 1) (y) (hy : y ∈ c.e.source) :
      (h.expMul fun _ => t).bcDens hS h₁ h₃ c y = h.bcDens hS h₁ h₃ c y := by
    have ha := (Met.exists_adapted hS h₁ h₃ y).choose_spec
    have hp := h.eventually_posDef hS _ c hy ha
    rw [Met.bcDens, Met.bcDens, Met.bcForm, Met.bcForm, ← extTrace_exp_smul
      (((H.gram (Met.exists_adapted hS h₁ h₃ y).choose.frame ha).mContDiffAt c hy).of_le
        (by norm_cast)) hp t]
    congr 3
    funext v
    ext a b
    exact Met.form_expMul _ _ _ _ _
  refine iSup_congr fun c => MeasureTheory.Measure.ext fun T hT => ?_
  have hm := c.e.open_source.measurableSet.inter hT
  rw [ChartGlue.chartMeas_apply _ _ hT, ChartGlue.chartMeas_apply _ _ hT]
  refine MeasureTheory.setLIntegral_congr_fun
    (ChartGlue.measurableSet_image _ hm inter_subset_left) ?_
  rintro _ ⟨y, hy, rfl⟩
  simp only [c.e.left_inv hy.1, hd c y hy.1]

theorem flagBc_scale {E : X.Modules} {r : ℕ} {h : VMetric p E r} (H : h.IsCInf)
    (fl : Vert.Flag E r) (s : ℝ) :
    ((h.scale s).FlagBcFinite fl ↔ h.FlagBcFinite fl) ∧ (h.scale s).flagBc fl = h.flagBc fl := by
  have e (i : Fin r) (σ : k →+* ℂ) : (((h.scale s).stepMet fl i).met σ).bcMeas
      (VMetric.stepSeq_shortExact fl i) (fl.isVB i.castSucc) (fl.isVB_gr i) =
      ((h.stepMet fl i).met σ).bcMeas
      (VMetric.stepSeq_shortExact fl i) (fl.isVB i.castSucc) (fl.isVB_gr i) := by
    have e₁ : ((h.scale s).stepMet fl i).met σ = ((h.stepMet fl i).met σ).expMul fun _ => s :=
      restrict_expMul (h.met σ) (fl.isSubbundle i.succ) (fl.isVB i.succ) _
    rw [e₁]
    exact bcMeas_expMul _ _ _ ((H σ).restrict (fl.isSubbundle i.succ) (fl.isVB i.succ)) s
  exact ⟨forall_congr' fun i => forall_congr' fun σ => (congrArg (· univ ≠ ⊤) (e i σ)).to_iff,
    Finset.sum_congr rfl fun i _ => finsum_congr fun σ =>
      congrArg (fun μ : MeasureTheory.Measure _ => (μ univ).toReal) (e i σ)⟩

end GlobalTheory.BcScale
