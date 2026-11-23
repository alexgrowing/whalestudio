import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DualGramInterpGram
open AlgebraicGeometry CategoryTheory Matrix ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.CxPts GlobalTheory.GradedNorm
open scoped ComplexOrder

set_option autoImplicit false

open scoped ContDiff

namespace GlobalTheory

theorem smoothOn_log_grSq : ∀ {k : Type} [CommRing k] {Y : Scheme.{0}} {p : Y ⟶ Sp k} {σ : k →+* ℂ} {D m : ℕ} (R : AnRead p σ D) (S : Set (CxPts p σ)) (M : CxPts p σ → Matrix (Fin m) (Fin m) ℂ), (∀ a b, R.SmoothOn S (fun y => (M y a b).re) ∧ R.SmoothOn S (fun y => (M y a b).im)) → (∀ y ∈ S, (M y).PosDef) → ∀ i : Fin m, R.SmoothOn S (fun y => Real.log (grSq (M y) i)) := by
  intro k _ Y p σ D m R S M hM hP i j
  have hE : ∀ a b, ContDiffOn ℝ ∞ (fun v => M ((R.chart j).e.symm v) a b)
      ((R.chart j).e.target ∩ (R.chart j).e.symm ⁻¹' S) := fun a b => by
    have h1 := Complex.ofRealCLM.contDiff.comp_contDiffOn ((hM a b).1 j)
    have h2 := Complex.ofRealCLM.contDiff.comp_contDiffOn ((hM a b).2 j)
    refine (h1.add (h2.mul (contDiffOn_const (c := Complex.I)))).congr fun v _ => ?_
    simp [Function.comp_def, Complex.re_add_im]
  have hL : ∀ K : Fin (m + 1), ContDiffOn ℝ ∞ (fun v => ReciprocityTheory.ChartRestriction.G.FD.lminor (M ((R.chart j).e.symm v)) K)
      ((R.chart j).e.target ∩ (R.chart j).e.symm ⁻¹' S) := fun K => by
    simp only [ReciprocityTheory.ChartRestriction.G.FD.lminor, Matrix.det_apply, Units.smul_def, zsmul_eq_mul]
    exact ContDiffOn.sum fun π _ => contDiffOn_const.mul (contDiffOn_prod fun c _ => hE _ _)
  have hq := (hL i.succ).mul ((hL i.castSucc).inv fun v (hv : v ∈ (R.chart j).e.target ∩ (R.chart j).e.symm ⁻¹' S) =>
    (GlobalTheory.GradedNorm.lminor_pos (hP _ hv.2) _).ne')
  have hr := Complex.reCLM.contDiff.comp_contDiffOn hq
  exact (hr.log fun v hv => (grSq_pos (hP _ hv.2) i).ne').congr fun v _ => by simp [grSq, div_eq_mul_inv]

end GlobalTheory
