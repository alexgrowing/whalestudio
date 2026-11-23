import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SeriesUnitOfReadInjScaleRootConjRootCoordRange
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeffPolynomialEqZeroOfVanishingOnGLFamily
import Formalism.LocalToGlobal.Columns.CoefColLemmas

set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie
open GlobalTheory.BigOn GlobalTheory.BigOn.Exp Formalism.L2.Theta GlobalTheory.ExportSeries
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CoeffNonvanish

open MvPolynomial

theorem exists_coefFn_ne_zero : ∀ {D : D7} {n : ℕ} (lam : D.what₂.Tau → DomWeight n),
    ∃ (F : VV D.what₂.LL lam) (x : GLR D n), coefFn D.what₂.embLL lam (F : Pol D.what₂.LL D.what₂.Tau n) x ≠ 0 := by
  intro D n lam
  refine ⟨⟨Formalism.L2.Col.extVV D.what₂.LL lam, Formalism.L2.Col.extVV_mem D.what₂.LL lam⟩, ?_⟩
  by_contra h
  push_neg at h
  have hmap : MvPolynomial.map D.what₂.embLL (Formalism.L2.Col.extVV D.what₂.LL lam) = 0 := by
    apply GlobalTheory.ExportSeries.eq_zero_of_coefFn_id_eq_zero D n lam
    intro x
    have hx := h x
    simp only [coefFn] at hx ⊢
    rw [eval₂Hom_map_hom] at *
    simpa using hx
  exact Formalism.L2.Col.extVV_ne_zero D.what₂.LL lam
    ((map_eq_zero_iff _ (MvPolynomial.map_injective _ D.what₂.embLL.injective)).mp hmap)

end GlobalTheory.CoeffNonvanish
