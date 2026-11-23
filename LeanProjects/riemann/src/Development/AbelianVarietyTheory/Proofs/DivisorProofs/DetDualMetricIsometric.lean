import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
import Development.AbelianVarietyTheory.Definitions.Divisors.FirstChernIntegralEqDegree

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Points GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.ChartGlue GlobalTheory.CechPic
open scoped ComplexOrder

namespace GlobalTheory

namespace VMetric

theorem log_det_dualGram {n : Type} [Fintype n] [DecidableEq n] {G : Matrix n n ℂ}
    (hG : G.PosDef) : Real.log (dualGram G).det.re = -Real.log G.det.re := by
  have e : G.det = (G.det.re : ℂ) :=
    Complex.ext rfl (by rw [Complex.ofReal_im]; exact (Complex.pos_iff.1 hG.det_pos).2.symm)
  rw [dualGram, Matrix.det_transpose, Matrix.det_nonsing_inv, Ring.inverse_eq_inv', e,
    ← Complex.ofReal_inv, Complex.ofReal_re, Complex.ofReal_re, Real.log_inv]

theorem isometric_det_dual (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (E : X.Modules)
    (r : ℕ) (h : VMetric p E r) (H : h.IsCInf) : (det H.dual).Isometric (det H).dual := by
  refine HermLB.Isometric.symm (HermLB.isometric_of_chart (L := (det H).dual) (M := det H.dual)
    (fun c : Chart E r => c.dual) (fun _ => le_rfl) (fun x c c' _ _ => ?_) fun σ c y hy => ?_)
  · exact congrArg (gm (𝟙 X) x _) (IsFrame.detUnit_dual c.isFrame c'.isFrame _ _).symm
  · change -Real.log ((h.met σ).dual.G c.dual y).det.re = -(-Real.log ((h.met σ).G c y).det.re)
    rw [(h.met σ).dual_G c hy, log_det_dualGram ((h.met σ).posDef c y hy)]

end VMetric

end GlobalTheory
