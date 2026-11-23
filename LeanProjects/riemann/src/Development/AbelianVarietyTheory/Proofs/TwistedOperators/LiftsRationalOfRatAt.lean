import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.GoodLiftPhase
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CommutingRationalGroups
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.RayFieldTheta
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EOpEqAsAlgebraHom
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LevelGroupActionEqZeroOfNoLift

noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open Formalism.IndefR.Arith

namespace GlobalTheory.LiftRat

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Abstract

variable {K : Type} [Field K] {G : Type} [Group G] [Fintype G]

end Abstract

section Forms

variable {LL Ks : Type} [Field LL] [NumberField LL] [Field Ks] [NumberField Ks] [Algebra Ks LL]
  {WL : Type} [AddCommGroup WL] [Module LL WL] [Module Ks WL]
  {W : (LL →+* ℂ) → Type} [∀ σ, NormedAddCommGroup (W σ)] [∀ σ, InnerProductSpace ℂ (W σ)]
  {G : Type} [Group G] [Fintype G] (A : FormsL LL Ks WL W G)

end Forms

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

section Package

variable {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A)

theorem j_eq_sum (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (y : Fin (R.nW i) → D.what₂.LL) :
    (R.FW i).j σ y = ∑ k, σ (y k) • (R.FW i).j σ (Pi.basisFun D.what₂.LL (Fin (R.nW i)) k) := by
  conv_lhs => rw [← (Pi.basisFun D.what₂.LL (Fin (R.nW i))).sum_repr y]
  rw [map_sum]
  exact Finset.sum_congr rfl fun k _ => by rw [map_smulₛₗ, Pi.basisFun_repr]

theorem span_basis (hU : R.LUnif) (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) :
    Submodule.span ℂ (Set.range fun k => (R.FW i).j σ (Pi.basisFun D.what₂.LL (Fin (R.nW i)) k)) = ⊤ := by
  refine top_le_iff.1 ((hU i σ).2.1.ge.trans (Submodule.span_le.2 ?_))
  rintro _ ⟨y, rfl⟩
  rw [j_eq_sum]
  exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)

end Package

variable (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A)
  (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1))
  (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec)
  (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)) (ph : Fin D.R.m → ℂ)

end GlobalTheory.LiftRat

end
