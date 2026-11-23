import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.JInjRdOf
import Formalism.LocalToGlobal.ProjectiveLattices.AllTest
import Formalism.LocalToGlobal.ProjectiveLattices.CuspFDOf

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ}

theorem rdIndep_of_wt (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (σ : c.F →+* ℂ)
    (hW : EvalWD (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z)) (hAT : AllTest Xo c)
    (hU : IsUnf (U σ)) (hA : BCEx Xo c σ) (hF : WtField Xo c) : RdIndep Xo c U σ := by
  intro a k _ n b hb hli
  have hT : ∀ kk x, FromTest (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) ((U σ).un kk x) := by
    intro kk x
    letI : IsReduced (CAt σ) := inferInstanceAs (IsReduced ℂ)
    exact hAT (CAt σ) ((U σ).un kk x)
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have hrel : ∀ kk (x : ((U σ).X kk).dom), ∑ i, g i * toC (evR Xo c (b i) ((U σ).un kk x)) = 0 := by
    intro kk x
    have h := congrFun (congrFun hg kk) x.1
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h
    rw [← h]
    exact Finset.sum_congr rfl fun i _ => by rw [← rdU_apply_dom (U σ) _ kk x]
  have hall := rel_of_frames (U σ) hU.2.2.1 hT hF b hb g hrel
  let _ : Algebra c.F ℂ := σ.toAlgebra
  have hc := indep_of_complex (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) hW
    (fun p φ y => hA p y φ) b (fun i => (hb i).1) hli g (fun z hz => hall z hz)
  intro i
  exact congrFun hc i

end ReciprocityTheory.ChartRestriction.G.PullbackSections
