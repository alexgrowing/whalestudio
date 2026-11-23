import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.TwistSeries
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.RationalRayLevels
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoverFormRationalDescentToBaseStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedDescentIntegralFormsOnePlaceStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GlueIntegralDecompositionsOverRationalPrimeStatement

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.DescIntRoad

open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum
  Formalism.IndefR.FWT Formalism.L2.Pj GlobalTheory.CoverRead

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem descIntAt_of_laws : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), LawsJ T → R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsFam → R.IsModels → R.IsThP → TieIn T R κ v₀ → ∀ (i : Fin D.R.m), VStd D i → ∀ hV : T.V ((i : ℕ) + 1) T.σ₀ = Wc D i, GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.FramePin T R i T.σ₀ hV → GlobalTheory.IndefiniteRowSideFullHecke.TwistSeries.DescIntAt T i (κ i) := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ hL hμ hG hF hM hP hT i hS hV hFP l hl C hC hpin S hO hU φ hφ hk
  obtain ⟨m, x, ψ, hψ, e⟩ := GlobalTheory.T.coverForm_rational_descent_to_base D G Pl0 T0 A T R F κ v₀ hL hμ hG hF hM hP hT i hS hV hFP l hl C hC hpin φ
    (C.intForms_subset _ _ S hφ) hk
  refine GlobalTheory.T.glue_integral_decompositions_over_rationalPrime D G Pl0 T0 A T R F κ v₀ hL hμ hG hF hM hP hT i hS hV hFP l hl C hC hpin S hO hU φ hφ hk m x ψ hψ e
    fun la hla => ?_
  have hsub : C.intForms (wtA (κ i)) (κ i).n S ⊆ C.intForms (wtA (κ i)) (κ i).n {la} :=
    Set.image_mono fun _ hf => ⟨hf.1, fun la' h => hf.2 la' (by rw [Set.mem_singleton_iff.1 h]; exact hla)⟩
  exact GlobalTheory.T.unramified_descent_integral_forms_one_place D G Pl0 T0 A T R F κ v₀ hL hμ hG hF hM hP hT i hS hV hFP l hl C hC hpin la (hO la hla)
    (fun la' h => hU la' (by rw [Set.mem_singleton_iff.1 h]; exact hla)) φ (hsub hφ) hk m x ψ hψ e

end GlobalTheory.DescIntRoad
