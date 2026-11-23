import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MovedFiniteDatumFourierExpansionChainless
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PureTensorOSmul
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.EmbeddingsDifferOnInteger
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OneMapTypingsEquiv

noncomputable section

open NumberField

namespace GlobalTheory.OneMapRefObj

open Formalism Formalism.IndefR Formalism.IndefR.FWT Formalism.IndefR.Links Formalism.L2.Pj Formalism.L2.DIV Formalism.BasicNotions

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem tieIn_of_fwTie {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
    {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F} {κ : ∀ i : Fin D.R.m, Formalism.MainNotions.WeightFamilies.Wt D ((i : ℕ) + 1)}
    {v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec} (t : FWTie T R κ v₀) : TieIn T R κ v₀ :=
  ⟨t.laws, t.alg_eq, t.kap, t.hv₀, t.chiR, t.x0⟩

end GlobalTheory.OneMapRefObj
