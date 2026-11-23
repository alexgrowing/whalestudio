import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ToroidalCompactificationData
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SmoothPullbackToFrameDomainStatement

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory GlobalTheory.CxPts GlobalTheory.Toroidal GlobalTheory.LieMet GlobalTheory.ShFam
open Formalism.DegreeFormula Formalism.MJ GlobalTheory.HodgeDomain GlobalTheory.TrueCx
open scoped ComplexOrder ContDiff

namespace GlobalTheory.ShFam

theorem smoothOn_nrm_toCpt : ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (s : FinalTheorems S κ) (L : CmList A)
    (k : s.Comp) (x : ToroidalCompactificationData s) (i : Fin x.m),
    HodgeDomain.SmoothOn fun z : Pt D.what₂.Tau j (N - j) => (x.nrm κ.σ₀ i (s.toCpt L k z) : ℂ) := by
  intro D A N j S κ s L k x i
  have hoff : ∀ z : Pt D.what₂.Tau j (N - j), ¬ LiesIn (s.toCpt L k z) (x.cpt i) := fun z h =>
    s.not_liesIn_toCpt L k z ((x.liesIn_genBd_iff _).2 ⟨i, h⟩)
  obtain ⟨-, h2, -⟩ := GlobalTheory.T.smooth_pullback_to_frame_domain D A N j S κ s L k {y | ¬ LiesIn y (x.cpt i)}
    (fun y => Real.log (x.nrm κ.σ₀ i y ^ 2)) (isOpen_not_liesIn _) (x.nrm_div κ.σ₀ i).smoothOn_log
  have e : {v ∈ DomFlat D.what₂.Tau j (N - j) | s.toCpt L k (unflat v) ∈ {y | ¬ LiesIn y (x.cpt i)}} =
      DomFlat D.what₂.Tau j (N - j) :=
    Set.sep_eq_self_iff_mem_true.2 fun v _ => hoff (unflat v)
  rw [e] at h2
  have h3 : ContDiffOn ℝ ∞ (fun v => Real.exp (Real.log (x.nrm κ.σ₀ i (s.toCpt L k (unflat v)) ^ 2) / 2))
      (DomFlat D.what₂.Tau j (N - j)) := (h2.div_const 2).exp
  refine (Complex.ofRealCLM.contDiff.comp_contDiffOn h3).congr fun v _ => ?_
  have hp := x.nrm_pos (s.not_liesIn_toCpt L k (unflat v)) i
  simp only [Function.comp_apply, Complex.ofRealCLM_apply]
  rw [Real.log_pow, Nat.cast_ofNat, mul_div_cancel_left₀ _ (two_ne_zero), Real.exp_log hp]

end GlobalTheory.ShFam
