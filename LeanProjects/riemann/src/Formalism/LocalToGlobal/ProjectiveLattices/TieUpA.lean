import Formalism.LocalToGlobal.ProjectiveLattices.CurveComp
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.PublishedIntClosHolds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.SpanSteps

noncomputable section

namespace Formalism.L2.Pj

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps ReciprocityTheory.ChartRestriction.G.Geo.Tor
  ReciprocityTheory.ChartRestriction.G.FD TensorProduct

variable {D : D7} {T : Top D} (h : LawsP T) (j : ℕ) (hj : InR D j)

def rdR {u : WeightFamilies.Wt D j} (F : (recB h.toLawsCore).Cusp j u) :=
  rdU (T.U j T.σ₀) F.1

def TieReadSt : Prop :=
  (∀ (u : WeightFamilies.Wt D j) (F : (recB h.toLawsCore).Cusp j u) (k : (T.U j T.σ₀).Comp),
    rdR h j F k ∈ ((T.U j T.σ₀).X k).SS (laU (T.U j T.σ₀) (wtA u) u.n k)) ∧
  ∀ u : WeightFamilies.Wt D j, ReciprocityTheory.ChartRestriction.G.PullbackSections.JInjRd T j (wtA u) u.n

abbrev KT (T : Top D) (j N : ℕ) : Type := FractionRing (MvPolynomial (Idx D j N) T.Q.c.F)

def IsIoExt {N : ℕ} (io : KT T j N →+* ℂ) : Prop :=
  ∀ a : T.Q.c.F, io (algebraMap T.Q.c.F (KT T j N) a) = T.σ₀ a

def rdSec {ka wL wF : WeightFamilies.Wt D j} (G : GlobalFamilyData (recPlus h j hj) ka wL wF) (io : KT T j G.N →+* ℂ)
    (i : Fin (WeightFamilies.dimY D j + 1)) :=
  ∑ k', io (algebraMap (MvPolynomial (Idx D j G.N) T.Q.c.F) (KT T j G.N) (MvPolynomial.X (i, k'))) •
    rdR h j (G.w k')

def TieMaxCuspSt (CR Tt c : ℝ) (ka : WeightFamilies.Wt D j) : Prop :=
  ∀ F : (recB h.toLawsCore).Cusp j ka,
    F ∈ WeightFamilies.MggK (recB h.toLawsCore) CR Tt c j ka ↔
      ∀ k, rdR h j F k ∈ ((T.U j T.σ₀).X k).SSgt (laU (T.U j T.σ₀) (wtA ka) ka.n k) (WeightFamilies.c1 D CR Tt c j)

end Formalism.L2.Pj
