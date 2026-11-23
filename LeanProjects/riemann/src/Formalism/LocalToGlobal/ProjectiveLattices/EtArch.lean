import Formalism.LocalToGlobal.ProjectiveLattices.Adm3OfExtension
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.TorusAt

noncomputable section

namespace Formalism.L2.Pj

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {T : Top D} (h : LawsP T)

def EtArch (th tableLineDegreeTwo : ℝ) : ∀ j i, (recB h.toLawsCore).Cusp j (wEt D j i) → Prop :=
  fun j i η => ∀ σ, GoodEmb T.Q.c σ → ∀ (k : (T.U j σ).Comp)
    (x : ReciprocityTheory.ChartRestriction.G.FD.Frame ((T.U j σ).X k).Ψ D.R.r), x ∈ ((T.U j σ).X k).dom →
      lieFac (T.Q.Dw j) (xiR D) (wtA (wEt D j i)) *
          ((T.U j σ).X k).pnorm (laU (T.U j σ) (wtA (wEt D j i)) (wEt D j i).n k)
            (rdU (T.U j σ) η.1 k) x ≤
        Real.exp (-(i : ℝ) * (ReciprocityTheory.ChartRestriction.G.I2.phiFD ((T.U j σ).X k) th x - tableLineDegreeTwo))

end Formalism.L2.Pj
