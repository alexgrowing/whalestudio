import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ConjScalarThm

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ConjScalar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

def ConjScalarAt (R : RealDat D A Ks) : Prop :=
  ∀ gramR c0R c0L, Bridge.FamTie R.B R.pl (R.Sb : Set (Pl D.host.E)) R.Q (labLL D) (fun τ => Bridge.lamRdef (Ptw D) τ)
      (fun i τ => Bridge.lamLdef (Vc D i).rank ((i : ℕ) + 1) τ) gramR c0R c0L →
    ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature.OverK σ →
    ∀ μ' η' c c₁ H j th, GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature.IsConjDatum R i σ (c0L i) μ' η' c c₁ H j th →
    ∀ ev : Pl D.host.E → List ℤ → ℂ, ∃ l : ℝ, ∀ u : H.H, th u ∈ GlobalTheory.LiftLower.partH R i σ ev →
      th (LinearMap.adjoint th (th u)) = (l : ℂ) • th u

theorem conjScalarAt_of (h : ConjScalarThm) (R : RealDat D A Ks) (F : Face D A) (hC : R.Char F) (hψ : IsStdChar D R.ψ (-1))
    (hX : ∀ χ ∈ A.X, IsAbsIrrChar χ) : ConjScalarAt R :=
  h D G Pl0 T0 A Ks R F hC hψ hX

end GlobalTheory.ConjScalar

end
