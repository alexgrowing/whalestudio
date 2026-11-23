import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyLink
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightsSumToVolumeProportional
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomogeneousMemSpanLinearRoots
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.LocM GlobalTheory.GenDeg

noncomputable section

namespace GlobalTheory.CompChern

open MvPolynomial

theorem interPoly_homog (hP : GlobalTheory.CovTop.Hypotheses2) {D : D7} (O : GlobalTheory.Mean4O.Setup D) (c : O.s.Comp)
    (Q : MvPolynomial (DV.Rt D.what₂.Tau O.N) ℝ) (hQ : Q.IsHomogeneous (Formalism.DegreeFormula.dimFl D.what₂.Tau O.N)) :
    letI := Classical.decEq D.what₂.Tau
    (O.var c).interPoly (fun x : DV.Rt D.what₂.Tau O.N => GlobalTheory.ShFam.Pad.divOf (O.Φ.C c) (O.ex x)) Q =
      (O.s.cx O.L O.B O.fl).volC c * Formalism.L2.Geo.degFlL D.what₂.Tau O.N Q := by
  classical
  have hM : GlobalTheory.Published.MumfordProportionality := (GlobalTheory.T.stronger_published_hypotheses_imply hP).p16
  have he : (O.var c).dim = Formalism.DegreeFormula.dimFl D.what₂.Tau O.N := O.dim_eq c
  set Λ₁ := (O.var c).interPoly (fun x : DV.Rt D.what₂.Tau O.N => GlobalTheory.ShFam.Pad.divOf (O.Φ.C c) (O.ex x)) with hΛ₁
  set Λ₂ := (O.s.cx O.L O.B O.fl).volC c • Formalism.L2.Geo.degFlL D.what₂.Tau O.N with hΛ₂
  have key := GlobalTheory.T.polynomial_power_eq_of_integral_points (Formalism.DegreeFormula.dimFl D.what₂.Tau O.N) Λ₁ Λ₂
    (fun a => by
      have := GlobalTheory.CompPropObj.interPoly_int hM O c fun τ i => -a (τ, i)
      simp only [neg_neg, he] at this
      refine this.trans ?_
      have hl : Formalism.DegreeFormula.linRoot (fun τ i => ((-a (τ, i) : ℤ) : ℝ)) = ∑ x, C ((a x : ℤ) : ℝ) * X x := by
        simp [Formalism.DegreeFormula.linRoot, Finset.sum_neg_distrib]
      show _ * Formalism.DegreeFormula.degFl _ _ (Formalism.DegreeFormula.linRoot _ ^ Formalism.DegreeFormula.dimFl _ _) = _ * (Formalism.L2.Geo.degFlL D.what₂.Tau O.N _)
      rw [hl]
      erw [Formalism.L2.Geo.degFlL_apply])
  have hpol : GlobalTheory.PowLinSpan.polOf (Λ₁ - Λ₂) (Formalism.DegreeFormula.dimFl D.what₂.Tau O.N) = 0 := by
    refine MvPolynomial.funext fun u => ?_
    rw [GlobalTheory.PowLinSpan.eval_polOf, map_zero, LinearMap.sub_apply, key u, sub_self]
  have h0 := GlobalTheory.PowLinSpan.homog_kill (Λ₁ - Λ₂) _ hpol Q hQ
  rw [LinearMap.sub_apply, sub_eq_zero] at h0
  rw [h0, hΛ₂, LinearMap.smul_apply, smul_eq_mul]

theorem chern_eq_sum : GlobalTheory.CovTop.Hypotheses2 → ∀ (D : D7) (O : GlobalTheory.Mean4O.Setup D) (Q : MvPolynomial (DV.Rt D.what₂.Tau O.N) ℝ),
    Q.IsHomogeneous (Formalism.DegreeFormula.dimFl D.what₂.Tau O.N) → ∑ c : O.s.Comp, (O.var c).interPoly
      (fun x : DV.Rt D.what₂.Tau O.N => GlobalTheory.ShFam.Pad.divOf (O.Φ.C c) (O.ex x)) Q = O.Y.chern Q := by
  intro hP D O Q hQ
  classical
  rw [Finset.sum_congr rfl fun c _ => interPoly_homog hP O c Q hQ, ← Finset.sum_mul]
  show _ = O.Y.vol * Formalism.L2.Geo.degFlL D.what₂.Tau O.N Q
  rfl

end GlobalTheory.CompChern
